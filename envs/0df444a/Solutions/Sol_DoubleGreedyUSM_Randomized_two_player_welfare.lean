-- Prove2me | solution 1 for DoubleGreedyUSM.Randomized.two_player_welfare
-- status  : ACCEPTED   (prove)
-- author  : @techtao
-- created : 2026-10-05T03:54:41.660987+00:00
-- url     : https://prove2.me/submissions/889c3967-b382-402f-ab61-795515244aa4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_DoubleGreedyUSM_Randomized_Algorithm2

set_option autoImplicit false

/- Complete local proof against public Prove2Me definitions.
Server verification has not been obtained. Source: Buchbinder et al.,
FOCS 2012, Algorithm 2 and Theorems I.2/I.4.
All supporting lemmas are proved in this file; no open theorem is imported. -/


/-!
Supporting scalar algebra for Buchbinder--Feldman--Naor--Schwartz,
Algorithm 2 and Lemma III.1.  The scalar lemmas below are combined with set and adaptive
probability-law arguments later in this submission file.
-/

namespace DoubleGreedyScalar

noncomputable def addProb (a b : ℝ) : ℝ :=
  let ap := max a 0
  let bp := max b 0
  if ap + bp = 0 then 1 else ap / (ap + bp)

/-- The paper's comparison-set loss has this bound after applying
submodularity.  If the processed element is in the comparison set, the add
branch changes nothing and the remove-branch loss is at most `a`; otherwise
the remove branch changes nothing and the add-branch loss is at most `b`. -/
def comparisonLossCap (inOpt : Bool) (a b p : ℝ) : ℝ :=
  if inOpt then (1 - p) * a else p * b

lemma positive_case (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hab : 0 < a + b) :
    a * b / (a + b) ≤
      (a / (a + b) * a + b / (a + b) * b) / 2 := by
  have hnum : a * b ≤ (a * a + b * b) / 2 := by
    nlinarith [sq_nonneg (a - b)]
  have hdiv : a * b / (a + b) ≤
      ((a * a + b * b) / 2) / (a + b) := by
    apply (div_le_div_iff₀ hab hab).2
    exact mul_le_mul_of_nonneg_right hnum (le_of_lt hab)
  have heq : ((a * a + b * b) / 2) / (a + b) =
      (a / (a + b) * a + b / (a + b) * b) / 2 := by
    field_simp [ne_of_gt hab]
  rw [heq] at hdiv
  exact hdiv

lemma probability_nonneg (a b : ℝ) : 0 ≤ addProb a b := by
  dsimp [addProb]
  have ha : 0 ≤ max a 0 := le_max_right a 0
  have hb : 0 ≤ max b 0 := le_max_right b 0
  split_ifs with h
  · norm_num
  · exact div_nonneg ha (add_nonneg ha hb)

lemma probability_le_one (a b : ℝ) : addProb a b ≤ 1 := by
  dsimp [addProb]
  have ha : 0 ≤ max a 0 := le_max_right a 0
  have hb : 0 ≤ max b 0 := le_max_right b 0
  split_ifs with h
  · norm_num
  · have hs : 0 < max a 0 + max b 0 := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    apply (div_le_iff₀ hs).2
    linarith

lemma clipped_step (a b : ℝ) (hsum : 0 ≤ a + b) (inOpt : Bool) :
    comparisonLossCap inOpt a b (addProb a b) ≤
      (addProb a b * a + (1 - addProb a b) * b) / 2 := by
  by_cases ha : 0 ≤ a
  · by_cases hb : b ≤ 0
    · have hp : addProb a b = 1 := by
        unfold addProb
        rw [max_eq_left ha, max_eq_right hb]
        by_cases haz : a = 0
        · simp [haz]
        · simp [haz]
      rw [hp]
      cases inOpt <;> simp [comparisonLossCap] <;> nlinarith
    · have hb0 : 0 ≤ b := le_of_lt (lt_of_not_ge hb)
      have hab : 0 < a + b := by linarith
      have hp : addProb a b = a / (a + b) := by
        unfold addProb
        rw [max_eq_left ha, max_eq_left hb0]
        simp [ne_of_gt hab]
      have hq : 1 - addProb a b = b / (a + b) := by
        rw [hp]
        field_simp [ne_of_gt hab]
        ring
      have hcap : comparisonLossCap inOpt a b (addProb a b) =
          a * b / (a + b) := by
        cases inOpt
        · simp [comparisonLossCap, hp]
          ring
        · simp [comparisonLossCap, hq]
          ring
      rw [hcap, hq, hp]
      exact positive_case a b ha hb0 hab
  · have ha0 : a < 0 := lt_of_not_ge ha
    have hb : 0 < b := by linarith
    have hp : addProb a b = 0 := by
      unfold addProb
      rw [max_eq_right (le_of_lt ha0), max_eq_left (le_of_lt hb)]
      simp [ne_of_gt hb]
    rw [hp]
    cases inOpt <;> simp [comparisonLossCap] <;> nlinarith

/-- A set-level proof may supply the two branchwise loss bounds directly.
The conditional one-step estimate then follows without knowing which
branch changes the comparison set. -/
lemma expected_loss_le (a b addLoss removeLoss : ℝ)
    (hsum : 0 ≤ a + b)
    (hadd : addLoss ≤ b) (hremove : removeLoss = 0) :
    let p := addProb a b
    p * addLoss + (1 - p) * removeLoss ≤
      (p * a + (1 - p) * b) / 2 := by
  dsimp
  rw [hremove, mul_zero, add_zero]
  have hp := probability_nonneg a b
  have hle := clipped_step a b hsum false
  dsimp [comparisonLossCap] at hle
  exact le_trans (mul_le_mul_of_nonneg_left hadd hp) hle

lemma expected_loss_le_inOpt (a b addLoss removeLoss : ℝ)
    (hsum : 0 ≤ a + b)
    (hadd : addLoss = 0) (hremove : removeLoss ≤ a) :
    let p := addProb a b
    p * addLoss + (1 - p) * removeLoss ≤
      (p * a + (1 - p) * b) / 2 := by
  dsimp
  rw [hadd, mul_zero, zero_add]
  have hq : 0 ≤ 1 - addProb a b := by
    linarith [probability_le_one a b]
  have hle := clipped_step a b hsum true
  dsimp [comparisonLossCap] at hle
  exact le_trans (mul_le_mul_of_nonneg_left hremove hq) hle

end DoubleGreedyScalar


/- Standalone supporting lemmas for Buchbinder et al., FOCS 2012,
Lemma II.1 and the set part of Lemma III.1.
The local predicate is definitionally equal to the imported platform predicate;
the final wrappers below use the original platform definitions. -/
namespace Prove2MePreparation

def Submodular {α : Type*} [DecidableEq α] (f : Finset α → ℝ) : Prop :=
  ∀ A B, f (A ∪ B) + f (A ∩ B) ≤ f A + f B

theorem nested_marginal_sum_nonneg {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : Submodular f)
    (X Y : Finset α) (u : α) (hXY : X ⊆ Y) (huY : u ∈ Y) (huX : u ∉ X) :
    0 ≤ (f (insert u X) - f X) + (f (Y.erase u) - f Y) := by
  have hunion : insert u X ∪ Y.erase u = Y := by
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ((rfl | hx) | ⟨_, hx⟩)
      · exact huY
      · exact hXY hx
      · exact hx
    · intro hx
      by_cases hxu : x = u
      · exact Or.inl (Or.inl hxu)
      · exact Or.inr ⟨hxu, hx⟩
  have hinter : insert u X ∩ Y.erase u = X := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨h | hx, hne, _⟩
      · exact False.elim (hne h)
      · exact hx
    · intro hx
      refine ⟨Or.inr hx, ?_, hXY hx⟩
      intro hxu
      subst x
      exact huX hx
  have h := hf (insert u X) (Y.erase u)
  rw [hunion, hinter] at h
  linarith

theorem comparison_losses_when_mem {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : Submodular f)
    (X O : Finset α) (u : α) (hXO : X ⊆ O) (huO : u ∈ O) (huX : u ∉ X) :
    (f O - f (insert u O) = 0) ∧
      (f O - f (O.erase u) ≤ f (insert u X) - f X) := by
  constructor
  · simp [Finset.insert_eq_of_mem huO]
  · have h := nested_marginal_sum_nonneg f hf X O u hXO huO huX
    linarith

theorem comparison_losses_when_not_mem {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : Submodular f)
    (O Y : Finset α) (u : α) (hOY : O ⊆ Y) (huY : u ∈ Y) (huO : u ∉ O) :
    (f O - f (O.erase u) = 0) ∧
      (f O - f (insert u O) ≤ f (Y.erase u) - f Y) := by
  constructor
  · simp [Finset.erase_eq_of_notMem huO]
  · have h := nested_marginal_sum_nonneg f hf O Y u hOY huY huO
    linarith

end Prove2MePreparation

namespace Prove2MePreparation

/-- The complete conditional one-step inequality, with branch losses
derived from submodularity rather than supplied as assumptions.
`O` is the current comparison set, with X ⊆ O ⊆ Y. -/
theorem one_step_expected_loss {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : Submodular f)
    (X O Y : Finset α) (u : α)
    (hXO : X ⊆ O) (hOY : O ⊆ Y) (huY : u ∈ Y) (huX : u ∉ X) :
    let a := f (insert u X) - f X
    let b := f (Y.erase u) - f Y
    let p := DoubleGreedyScalar.addProb a b
    p * (f O - f (insert u O)) + (1 - p) * (f O - f (O.erase u)) ≤
      (p * a + (1 - p) * b) / 2 := by
  dsimp only
  have hsum := nested_marginal_sum_nonneg f hf X Y u (hXO.trans hOY) huY huX
  by_cases huO : u ∈ O
  · have hloss := comparison_losses_when_mem f hf X O u hXO huO huX
    exact DoubleGreedyScalar.expected_loss_le_inOpt _ _ _ _ hsum hloss.1 hloss.2
  · have hloss := comparison_losses_when_not_mem f hf O Y u hOY huY huO
    exact DoubleGreedyScalar.expected_loss_le _ _ _ _ hsum hloss.2 hloss.1

end Prove2MePreparation



/-! A standalone recursive expectation for Algorithm 2 of Buchbinder et al.
The recursion follows the actual current sets, so its probability is adaptive. -/

namespace DoubleGreedyRun

noncomputable def expected {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) : List α → Finset α → Finset α → ℝ
  | [], X, _ => f X
  | u :: rest, X, Y =>
      let a := f (insert u X) - f X
      let b := f (Y.erase u) - f Y
      let p := DoubleGreedyScalar.addProb a b
      p * expected f rest (insert u X) Y +
        (1 - p) * expected f rest X (Y.erase u)

@[simp] theorem expected_nil {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (X Y : Finset α) : expected f [] X Y = f X := rfl

theorem remaining_after_add {α : Type*} [DecidableEq α]
    (X Y : Finset α) (u : α) :
    Y \ insert u X = (Y \ X).erase u := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
  tauto

theorem remaining_after_remove {α : Type*} [DecidableEq α]
    (X Y : Finset α) (u : α) :
    Y.erase u \ X = (Y \ X).erase u := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  tauto

theorem endpoint_of_no_remaining {α : Type*} [DecidableEq α]
    (X O Y : Finset α) (hXO : X ⊆ O) (hOY : O ⊆ Y)
    (hempty : Y \ X = ∅) : X = O ∧ O = Y := by
  have hYX : Y ⊆ X := by
    intro x hx
    by_contra hnot
    have : x ∈ Y \ X := Finset.mem_sdiff.mpr ⟨hx, hnot⟩
    simp [hempty] at this
  have hXY : X ⊆ Y := hXO.trans hOY
  have hXYeq : X = Y := Finset.Subset.antisymm hXY hYX
  constructor
  · exact Finset.Subset.antisymm hXO (hXYeq ▸ hOY)
  · exact Finset.Subset.antisymm hOY (hXYeq ▸ hXO)

/-- A pathwise comparison set can start anywhere between the current lower
and upper sets. This stronger invariant closes under both branches of the
adaptive recursion. -/
theorem recursive_bound {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : Prove2MePreparation.Submodular f) :
    ∀ (l : List α) (X O Y : Finset α),
      l.Nodup → l.toFinset = Y \ X → X ⊆ O → O ⊆ Y →
      2 * f O + f X + f Y ≤ 4 * expected f l X Y := by
  intro l
  induction l with
  | nil =>
      intro X O Y _ hremaining hXO hOY
      have hempty : Y \ X = ∅ := by simpa using hremaining.symm
      obtain ⟨hX, hO⟩ := endpoint_of_no_remaining X O Y hXO hOY hempty
      subst O
      subst Y
      simp [expected]
      nlinarith
  | cons u rest ih =>
      intro X O Y hnodup hremaining hXO hOY
      have hu : u ∈ Y \ X := by
        rw [← hremaining]
        simp
      have huY : u ∈ Y := (Finset.mem_sdiff.mp hu).1
      have huX : u ∉ X := (Finset.mem_sdiff.mp hu).2
      have ⟨hunotList, hnodupTail⟩ := List.nodup_cons.mp hnodup
      have htail : rest.toFinset = (Y \ X).erase u := by
        rw [← hremaining]
        ext x
        simp only [Finset.mem_erase, List.mem_toFinset, List.mem_cons]
        constructor
        · intro hx
          exact ⟨by intro heq; subst x; exact hunotList hx, Or.inr hx⟩
        · rintro ⟨_, (heq | hx)⟩
          · exact False.elim (‹x ≠ u› heq)
          · exact hx
      have hadd_rem : rest.toFinset = Y \ insert u X := by
        rw [remaining_after_add]
        exact htail
      have hremove_rem : rest.toFinset = Y.erase u \ X := by
        rw [remaining_after_remove]
        exact htail
      have hadd_XO : insert u X ⊆ insert u O := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hXO hx)
      have hadd_OY : insert u O ⊆ Y := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact huY
        · exact hOY hx
      have hremove_XO : X ⊆ O.erase u := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨by intro heq; subst x; exact huX hx, hXO hx⟩
      have hremove_OY : O.erase u ⊆ Y.erase u := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
          hOY (Finset.mem_erase.mp hx).2⟩
      have hadd := ih (insert u X) (insert u O) Y hnodupTail
        hadd_rem hadd_XO hadd_OY
      have hremove := ih X (O.erase u) (Y.erase u) hnodupTail
        hremove_rem hremove_XO hremove_OY
      let a := f (insert u X) - f X
      let b := f (Y.erase u) - f Y
      let p := DoubleGreedyScalar.addProb a b
      have hp : 0 ≤ p := DoubleGreedyScalar.probability_nonneg a b
      have hq : 0 ≤ 1 - p := by
        have := DoubleGreedyScalar.probability_le_one a b
        linarith
      have hstep :
          p * (f O - f (insert u O)) +
            (1 - p) * (f O - f (O.erase u)) ≤
            (p * a + (1 - p) * b) / 2 := by
        exact Prove2MePreparation.one_step_expected_loss f hf X O Y u
          hXO hOY huY huX
      have hwa := mul_le_mul_of_nonneg_left hadd hp
      have hwr := mul_le_mul_of_nonneg_left hremove hq
      change 2 * f O + f X + f Y ≤
        4 * (p * expected f rest (insert u X) Y +
          (1 - p) * expected f rest X (Y.erase u))
      dsimp only [a, b] at hstep
      nlinarith

theorem half_approximation {α : Type*} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (hf : Prove2MePreparation.Submodular f)
    (hf0 : ∀ S : Finset α, 0 ≤ f S)
    (O : Finset α) (l : List α) (hnodup : l.Nodup)
    (hcover : l.toFinset = Finset.univ) :
    f O ≤ 2 * expected f l ∅ Finset.univ := by
  have hremaining : l.toFinset = Finset.univ \ (∅ : Finset α) := by
    simpa using hcover
  have h := recursive_bound f hf l ∅ O Finset.univ hnodup hremaining
    (Finset.empty_subset _) (Finset.subset_univ _)
  have h0 := hf0 (∅ : Finset α)
  have hU := hf0 (Finset.univ : Finset α)
  linarith

end DoubleGreedyRun



/-! Relates the recursive expected value proof to Prove2Me's exact finite
mass-function encoding of randomized double greedy. -/

namespace DoubleGreedyPlatformBridge

open DoubleGreedyUSM.Randomized

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Integrating a single transition against any real-valued observable
recovers the weighted values at the two successor states. -/
theorem expect_advance (f : Finset X → ℝ)
    (μ : (Finset X × Finset X) → ℝ) (u : X)
    (g : Finset X × Finset X → ℝ) :
    expect (advance f μ u) g =
      ∑ s : Finset X × Finset X,
        μ s * (addProb f s u * g (insert u s.1, s.2) +
          (1 - addProb f s u) * g (s.1, s.2.erase u)) := by
  classical
  simp only [expect, advance, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext s
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp [nextMass, add_mul, Finset.sum_add_distrib]

/-- The platform fold of the adaptive state law has exactly the recursive
expected output from the standalone induction. -/
theorem expect_foldl (f : Finset X → ℝ)
    (l : List X) (μ : (Finset X × Finset X) → ℝ) :
    expect (l.foldl (advance f) μ) (fun s => f s.1) =
      ∑ s : Finset X × Finset X, μ s *
        DoubleGreedyRun.expected f l s.1 s.2 := by
  induction l generalizing μ with
  | nil => simp [expect, DoubleGreedyRun.expected]
  | cons u rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      change expect (advance f μ u)
        (fun s => DoubleGreedyRun.expected f rest s.1 s.2) = _
      rw [expect_advance]
      simp only [DoubleGreedyRun.expected]
      congr 1

/-- The exact platform initial mass is concentrated on `(∅, univ)`. -/
theorem expect_state_eq_recursive (f : Finset X → ℝ) (l : List X) :
    expect (state f l l.length) (fun s => f s.1) =
      DoubleGreedyRun.expected f l ∅ Finset.univ := by
  classical
  simp only [state, List.take_length]
  rw [expect_foldl]
  simp

/-- The platform's exact Algorithm 2 theorem, using the published definitions
of submodularity, optimum, state mass, and expectation. -/
theorem randomized_usm_half
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hf0 : ∀ S : Finset X, 0 ≤ f S)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x : X, x ∈ l) :
    NonmonotoneSubmod.Shared.OPT f ≤
      2 * expect (state f l l.length) (fun s => f s.1) := by
  have hcover : l.toFinset = Finset.univ := by
    ext x
    simp [hcov x]
  have hsub : Prove2MePreparation.Submodular f := hf
  have hopt : NonmonotoneSubmod.Shared.OPT f ≤
      2 * DoubleGreedyRun.expected f l ∅ Finset.univ := by
    unfold NonmonotoneSubmod.Shared.OPT
    apply Finset.sup'_le
    intro O hO
    exact DoubleGreedyRun.half_approximation f hsub hf0 O l hl hcover
  rw [expect_state_eq_recursive]
  exact hopt

end DoubleGreedyPlatformBridge



/-! Supporting reduction for the two-player submodular welfare objective.
This uses the locally proved adaptive double-greedy recursion. -/

namespace WelfareProof

variable {X : Type} [Fintype X] [DecidableEq X]

def objective (f₁ f₂ : Finset X → ℝ) (S : Finset X) : ℝ :=
  f₁ S + f₂ Sᶜ

theorem objective_submodular
    (f₁ f₂ : Finset X → ℝ)
    (hsub₁ : NonmonotoneSubmod.Shared.Submodular f₁)
    (hsub₂ : NonmonotoneSubmod.Shared.Submodular f₂) :
    Prove2MePreparation.Submodular (objective f₁ f₂) := by
  intro S T
  have hU : (S ∪ T)ᶜ = Sᶜ ∩ Tᶜ := by
    ext x
    simp
  have hI : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ := by
    ext x
    simp
  have h₁ := hsub₁ S T
  have h₂ := hsub₂ Sᶜ Tᶜ
  change f₂ (Sᶜ ∪ Tᶜ) + f₂ (Sᶜ ∩ Tᶜ) ≤ f₂ Sᶜ + f₂ Tᶜ at h₂
  dsimp [objective]
  rw [hU, hI]
  linarith

theorem objective_endpoint_bound
    (f₁ f₂ : Finset X → ℝ)
    (hmono₁ : ∀ A B : Finset X, A ⊆ B → f₁ A ≤ f₁ B)
    (hmono₂ : ∀ A B : Finset X, A ⊆ B → f₂ A ≤ f₂ B)
    (hnorm₁ : f₁ ∅ = 0) (hnorm₂ : f₂ ∅ = 0)
    (O : Finset X) :
    objective f₁ f₂ O ≤
      objective f₁ f₂ ∅ + objective f₁ f₂ Finset.univ := by
  have h₁ := hmono₁ O Finset.univ (Finset.subset_univ O)
  have h₂ := hmono₂ Oᶜ Finset.univ (Finset.subset_univ Oᶜ)
  simp only [objective, Finset.compl_empty, Finset.compl_univ, hnorm₁, hnorm₂,
    zero_add, add_zero]
  linarith

theorem three_quarters_comparison
    (f₁ f₂ : Finset X → ℝ)
    (hsub₁ : NonmonotoneSubmod.Shared.Submodular f₁)
    (hsub₂ : NonmonotoneSubmod.Shared.Submodular f₂)
    (hmono₁ : ∀ A B : Finset X, A ⊆ B → f₁ A ≤ f₁ B)
    (hmono₂ : ∀ A B : Finset X, A ⊆ B → f₂ A ≤ f₂ B)
    (hnorm₁ : f₁ ∅ = 0) (hnorm₂ : f₂ ∅ = 0)
    (O : Finset X) (l : List X) (hl : l.Nodup)
    (hcov : l.toFinset = Finset.univ) :
    3 * objective f₁ f₂ O ≤
      4 * DoubleGreedyRun.expected (objective f₁ f₂) l ∅ Finset.univ := by
  have hsub := objective_submodular f₁ f₂ hsub₁ hsub₂
  have hremaining : l.toFinset = Finset.univ \ (∅ : Finset X) := by
    simpa using hcov
  have hrun := DoubleGreedyRun.recursive_bound (objective f₁ f₂) hsub
    l ∅ O Finset.univ hl hremaining (Finset.empty_subset _)
    (Finset.subset_univ _)
  have hend := objective_endpoint_bound f₁ f₂ hmono₁ hmono₂ hnorm₁ hnorm₂ O
  linarith

theorem three_quarters_sup
    (f₁ f₂ : Finset X → ℝ)
    (hsub₁ : NonmonotoneSubmod.Shared.Submodular f₁)
    (hsub₂ : NonmonotoneSubmod.Shared.Submodular f₂)
    (hmono₁ : ∀ A B : Finset X, A ⊆ B → f₁ A ≤ f₁ B)
    (hmono₂ : ∀ A B : Finset X, A ⊆ B → f₂ A ≤ f₂ B)
    (hnorm₁ : f₁ ∅ = 0) (hnorm₂ : f₂ ∅ = 0)
    (l : List X) (hl : l.Nodup)
    (hcov : l.toFinset = Finset.univ) :
    3 * (Finset.univ.sup' Finset.univ_nonempty (objective f₁ f₂)) ≤
      4 * DoubleGreedyRun.expected (objective f₁ f₂) l ∅ Finset.univ := by
  let E := DoubleGreedyRun.expected (objective f₁ f₂) l ∅ Finset.univ
  have hsup : Finset.univ.sup' Finset.univ_nonempty (objective f₁ f₂) ≤
      (4 * E) / 3 := by
    apply Finset.sup'_le
    intro O _
    have h := three_quarters_comparison f₁ f₂ hsub₁ hsub₂
      hmono₁ hmono₂ hnorm₁ hnorm₂ O l hl hcov
    linarith
  dsimp [E] at hsup ⊢
  linarith

end WelfareProof

open DoubleGreedyUSM.Randomized

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f₁ f₂ : Finset X → ℝ)
    (hsub₁ : NonmonotoneSubmod.Shared.Submodular f₁)
    (hsub₂ : NonmonotoneSubmod.Shared.Submodular f₂)
    (hmono₁ : ∀ A B : Finset X, A ⊆ B → f₁ A ≤ f₁ B)
    (hmono₂ : ∀ A B : Finset X, A ⊆ B → f₂ A ≤ f₂ B)
    (hnonneg₁ : ∀ S : Finset X, 0 ≤ f₁ S)
    (hnonneg₂ : ∀ S : Finset X, 0 ≤ f₂ S)
    (hnorm₁ : f₁ ∅ = 0) (hnorm₂ : f₂ ∅ = 0)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x : X, x ∈ l) :
    let g : Finset X → ℝ := fun S => f₁ S + f₂ Sᶜ
    3 * NonmonotoneSubmod.Shared.OPT g ≤
      4 * expect (state g l l.length) (fun s => g s.1) := by
  let g : Finset X → ℝ := fun S => f₁ S + f₂ Sᶜ
  change 3 * NonmonotoneSubmod.Shared.OPT g ≤
      4 * expect (state g l l.length) (fun s => g s.1)
  rw [DoubleGreedyPlatformBridge.expect_state_eq_recursive]
  have hcover : l.toFinset = Finset.univ := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact hcov x
  have hopt : NonmonotoneSubmod.Shared.OPT g ≤
      (4 * DoubleGreedyRun.expected g l ∅ Finset.univ) / 3 := by
    unfold NonmonotoneSubmod.Shared.OPT
    apply Finset.sup'_le
    intro O _
    have h := WelfareProof.three_quarters_comparison f₁ f₂ hsub₁ hsub₂
      hmono₁ hmono₂ hnorm₁ hnorm₂ O l hl hcover
    change 3 * g O ≤ 4 * DoubleGreedyRun.expected g l ∅ Finset.univ at h
    linarith
  linarith

#print axioms solution
