-- Prove2me | solution 1 for CoverModular.proposition_2_greedy_type_approximation
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T11:24:29.075199+00:00
-- url     : https://prove2.me/submissions/b1c84afb-9a5e-44b6-9626-311050d84a75

import Definitions.Def_CoverModular_FDPInstance_IsAlgorithm1Run
import Theorems.Thm_CoverModular_approximation_factor_ge
import Definitions.Def_CoverModular_IsOptimal
import Definitions.Def_CoverModular_IsDualFeasible
import Definitions.Def_CoverModular_alphaBar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_CoverModular_dual_objective_eq_two_f
import Definitions.Def_CoverModular_FDPInstance_Standing
import Definitions.Def_CoverModular_FDPInstance_F
import Definitions.Def_CoverModular_FDPInstance_Emax
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum


set_option autoImplicit false

open scoped BigOperators

namespace CoverModular.S09Dual

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Remove fixed proportions from one row and column, then insert mass at
their crossing. The crossing loses both proportions. -/
noncomputable def perturb (x : I → J → ℝ) (i : I) (j : J) (a b ε : ℝ) : I → J → ℝ :=
  fun k l => x k l - (if k = i then a * x k l else 0)
    - (if l = j then b * x k l else 0) + if k = i ∧ l = j then ε else 0

theorem perturb_feasible (c : I → ℝ) (d : J → ℝ) (S : Finset (I × J))
    (x : I → J → ℝ) (hx : (network c d S).Feasible x)
    (i : I) (j : J) (hij : (i, j) ∈ S) (a b ε : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) (hε : 0 ≤ ε)
    (hac : a * c i = ε) (hbd : b * d j = ε) :
    (network c d S).Feasible (perturb x i j a b ε) := by
  have ha1 : 0 ≤ 1 - a := by linarith
  have hb1 : 0 ≤ 1 - b := by linarith
  have hab1 : 0 ≤ 1 - a - b := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k l
    have hx0 := hx.1 k l
    by_cases hk : k = i <;> by_cases hl : l = j <;>
      (try simp only [hk, hl] at hx0) <;>
      simp only [perturb, hk, hl, and_self, and_false, false_and, if_true, if_false] <;>
      nlinarith [mul_nonneg ha1 hx0, mul_nonneg hb1 hx0, mul_nonneg hab1 hx0]
  · intro k l hnot
    have hz := hx.2.1 k l hnot
    have hne : ¬ (k = i ∧ l = j) := by
      rintro ⟨rfl, rfl⟩
      exact hnot hij
    simp [perturb, hz, hne]
  · intro k
    by_cases hk : k = i
    · subst k
      have hpoint : ∀ l, perturb x i j a b ε i l ≤
          (1 - a) * x i l + if l = j then ε else 0 := by
        intro l
        have hbx := mul_nonneg hb (hx.1 i l)
        by_cases hl : l = j <;> (try simp only [hl] at hbx) <;> simp [perturb, hl] <;> nlinarith
      calc
        ∑ l, perturb x i j a b ε i l
            ≤ (1 - a) * (∑ l, x i l) + ε := by
              simpa [Finset.sum_add_distrib, ← Finset.mul_sum] using
                Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hpoint l)
        _ ≤ (1 - a) * c i + ε :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2.2.1 i) ha1) le_rfl
        _ = c i := by linarith
    · apply le_trans (Finset.sum_le_sum (fun l _ => ?_)) (hx.2.2.1 k)
      have hbx := mul_nonneg hb (hx.1 k l)
      by_cases hl : l = j <;> (try simp only [hl] at hbx) <;> simp [perturb, hk, hl] <;> linarith
  · intro l
    by_cases hl : l = j
    · subst l
      have hpoint : ∀ k, perturb x i j a b ε k j ≤
          (1 - b) * x k j + if k = i then ε else 0 := by
        intro k
        have hax := mul_nonneg ha (hx.1 k j)
        by_cases hk : k = i <;> (try simp only [hk] at hax) <;> simp [perturb, hk] <;> nlinarith
      calc
        ∑ k, perturb x i j a b ε k j
            ≤ (1 - b) * (∑ k, x k j) + ε := by
              simpa [Finset.sum_add_distrib, ← Finset.mul_sum] using
                Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpoint k)
        _ ≤ (1 - b) * d j + ε :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2.2.2 j) hb1) le_rfl
        _ = d j := by linarith
    · apply le_trans (Finset.sum_le_sum (fun k _ => ?_)) (hx.2.2.2 l)
      have hax := mul_nonneg ha (hx.1 k l)
      by_cases hk : k = i <;> (try simp only [hk] at hax) <;> simp [perturb, hk, hl] <;> linarith

theorem profit_perturb (p x : I → J → ℝ) (i : I) (j : J) (a b ε : ℝ) :
    profit p (perturb x i j a b ε) = profit p x
      - a * (∑ l, p i l * x i l) - b * (∑ k, p k j * x k j) + ε * p i j := by
  have hpoint : ∀ k l, p k l * perturb x i j a b ε k l =
      p k l * x k l - (if k = i then a * (p k l * x k l) else 0)
      - (if l = j then b * (p k l * x k l) else 0)
      + if k = i ∧ l = j then ε * p k l else 0 := by
    intro k l
    by_cases hk : k = i <;> by_cases hl : l = j <;> simp [perturb, hk, hl] <;> ring
  simp only [profit, hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_irrel, Finset.sum_ite_eq', ← Finset.mul_sum, ite_and]

end CoverModular.S09Dual

namespace CoverModular

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The proposed dual prices satisfy every arc constraint: otherwise the
explicit row-and-column perturbation would improve an optimal flow. -/
theorem s09_dual_feasible_alphaBar_betaBar (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) (hp : ∀ i j, 0 ≤ p i j)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, p i j ≤ P)
    (S : Finset (I × J)) (x : I → J → ℝ) (hx : IsOptimal c d p S x) :
    IsDualFeasible p S (alphaBar c p P x) (betaBar d p P x) := by
  have hα : ∀ i, 0 ≤ alphaBar c p P x i := by
    intro i
    unfold alphaBar
    split_ifs with hi
    · exact div_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hp i j) (hx.1.1 i j))) hi.le
    · exact hP0
  have hβ : ∀ j, 0 ≤ betaBar d p P x j := by
    intro j
    unfold betaBar
    split_ifs with hj
    · exact div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i j) (hx.1.1 i j))) hj.le
    · exact hP0
  refine ⟨?_, hα, hβ⟩
  intro i j hij
  by_cases hci : 0 < c i
  · by_cases hdj : 0 < d j
    · let ε := min (c i) (d j) / 2
      have hε : 0 < ε := div_pos (lt_min hci hdj) (by norm_num)
      have hac0 : 0 ≤ ε / c i := div_nonneg hε.le hci.le
      have hbd0 : 0 ≤ ε / d j := div_nonneg hε.le hdj.le
      have hac1 : ε / c i ≤ 1 / 2 := by
        apply (div_le_iff₀ hci).2
        dsimp [ε]
        linarith [min_le_left (c i) (d j)]
      have hbd1 : ε / d j ≤ 1 / 2 := by
        apply (div_le_iff₀ hdj).2
        dsimp [ε]
        linarith [min_le_right (c i) (d j)]
      have hac : (ε / c i) * c i = ε := by field_simp
      have hbd : (ε / d j) * d j = ε := by field_simp
      have hfeas := S09Dual.perturb_feasible c d S x hx.1 i j hij
        (ε / c i) (ε / d j) ε hac0 hbd0 (by linarith) hε.le hac hbd
      have hopt := hx.2 _ hfeas
      rw [S09Dual.profit_perturb] at hopt
      have e1 : (ε / c i) * (∑ l, p i l * x i l) =
          ε * ((∑ l, p i l * x i l) / c i) := by ring
      have e2 : (ε / d j) * (∑ k, p k j * x k j) =
          ε * ((∑ k, p k j * x k j) / d j) := by ring
      rw [e1, e2] at hopt
      simp only [alphaBar, betaBar, if_pos hci, if_pos hdj]
      nlinarith
    · rw [betaBar, if_neg hdj]
      exact (hP i j).trans (le_add_of_nonneg_left (hα i))
  · rw [alphaBar, if_neg hci]
    exact (hP i j).trans (le_add_of_nonneg_right (hβ j))


end CoverModular


set_option autoImplicit false

open scoped BigOperators

namespace CoverModular.S09Dual

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]
  [DecidableEq I] [DecidableEq J]

/-- Weak duality on an arbitrary structure, with a correction only for arcs
outside the structure on which the supplied prices are feasible. -/
theorem lpValue_upper (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j)
    (S B : Finset (I × J)) (α : I → ℝ) (β : J → ℝ)
    (hdual : IsDualFeasible p S α β) :
    lpValue c d p B ≤ (∑ i, c i * α i) + (∑ j, d j * β j)
      + ∑ a ∈ B \ S, min (c a.1) (d a.2) * max (p a.1 a.2 - α a.1 - β a.2) 0 := by
  have hzero : (network c d B).Feasible (fun _ _ => 0) := by
    refine ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, ?_, ?_⟩
    · intro i; simpa [network] using hc i
    · intro j; simpa [network] using hd j
  unfold lpValue
  refine csSup_le ⟨_, ⟨(fun _ _ => 0), hzero, rfl⟩⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  let q : I → J → ℝ := fun i j => min (c i) (d j) * max (p i j - α i - β j) 0
  have hpoint : ∀ i j, p i j * y i j ≤ α i * y i j + β j * y i j
      + if (i, j) ∈ B \ S then q i j else 0 := by
    intro i j
    have hy0 := hy.1 i j
    by_cases he : (i, j) ∈ B \ S
    · simp only [if_pos he]
      have hyc : y i j ≤ c i :=
        (Finset.single_le_sum (fun k _ => hy.1 i k) (Finset.mem_univ j)).trans (hy.2.2.1 i)
      have hyd : y i j ≤ d j :=
        (Finset.single_le_sum (fun k _ => hy.1 k j) (Finset.mem_univ i)).trans (hy.2.2.2 j)
      have hym : y i j ≤ min (c i) (d j) := le_min hyc hyd
      have h1 := mul_le_mul_of_nonneg_right (le_max_left (p i j - α i - β j) 0) hy0
      have h2 := mul_le_mul_of_nonneg_left hym (le_max_right (p i j - α i - β j) 0)
      dsimp [q]
      nlinarith
    · simp only [if_neg he, add_zero]
      by_cases hb : (i, j) ∈ B
      · have hs : (i, j) ∈ S := by
          by_contra hs
          exact he (Finset.mem_sdiff.mpr ⟨hb, hs⟩)
        have h := mul_le_mul_of_nonneg_right (hdual.1 i j hs) hy0
        nlinarith
      · have hz := hy.2.1 i j hb
        simp [hz]
  have hrow : (∑ i, ∑ j, α i * y i j) ≤ ∑ i, c i * α i := by
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.mul_sum]
    simpa [network, mul_comm] using mul_le_mul_of_nonneg_left (hy.2.2.1 i) (hdual.2.1 i)
  have hcol : (∑ i, ∑ j, β j * y i j) ≤ ∑ j, d j * β j := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j _
    rw [← Finset.mul_sum]
    simpa [network, mul_comm] using mul_le_mul_of_nonneg_left (hy.2.2.2 j) (hdual.2.2 j)
  have heq : (∑ i, ∑ j, if (i, j) ∈ B \ S then q i j else 0) =
      ∑ a ∈ B \ S, q a.1 a.2 := by
    rw [← Fintype.sum_prod_type']
    exact Finset.sum_ite_mem_eq (B \ S) (fun a => q a.1 a.2)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hpoint i j))
  simp only [Finset.sum_add_distrib] at hsum
  rw [heq] at hsum
  unfold profit
  exact hsum.trans (add_le_add (add_le_add hrow hcol) le_rfl)

theorem E_nonneg (inst : FDPInstance I J Ω) (hinst : inst.Standing)
    (P : ℝ) (x : Ω → I → J → ℝ) (i : I) (j : J) :
    0 ≤ inst.E P x i j := by
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hinst.1 ω)
    (mul_nonneg (le_min (hinst.2.1 i ω) (hinst.2.2.1 j ω)) (le_max_right _ _))

theorem Emax_nonneg (inst : FDPInstance I J Ω) (hinst : inst.Standing)
    (P : ℝ) (x : Ω → I → J → ℝ) (S : Finset (I × J)) :
    0 ≤ inst.Emax P x S := by
  unfold FDPInstance.Emax
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    exact (E_nonneg inst hinst P x a.1 a.2).trans (Finset.le_sup' (fun a : I × J => inst.E P x a.1 a.2) ha)
  · exact le_rfl

theorem E_le_Emax (inst : FDPInstance I J Ω) (P : ℝ)
    (x : Ω → I → J → ℝ) (S : Finset (I × J)) (a : I × J) (ha : a ∉ S) :
    inst.E P x a.1 a.2 ≤ inst.Emax P x S := by
  have hm : a ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
  have hn : (Finset.univ \ S).Nonempty := ⟨a, hm⟩
  rw [FDPInstance.Emax, dif_pos hn]
  exact Finset.le_sup' (fun a : I × J => inst.E P x a.1 a.2) hm

theorem correction_sum_le (inst : FDPInstance I J Ω) (hinst : inst.Standing)
    (P : ℝ) (x : Ω → I → J → ℝ) (S B : Finset (I × J)) :
    (∑ a ∈ B \ S, inst.E P x a.1 a.2) ≤ (B.card : ℝ) * inst.Emax P x S := by
  calc
    (∑ a ∈ B \ S, inst.E P x a.1 a.2)
        ≤ ∑ _a ∈ B \ S, inst.Emax P x S := by
          apply Finset.sum_le_sum
          intro a ha
          exact E_le_Emax inst P x S a (Finset.mem_sdiff.mp ha).2
    _ = ((B \ S).card : ℝ) * inst.Emax P x S := by simp
    _ ≤ (B.card : ℝ) * inst.Emax P x S := by
      apply mul_le_mul_of_nonneg_right _ (Emax_nonneg inst hinst P x S)
      exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : B \ S ⊆ B))

theorem structural_comparison (inst : FDPInstance I J Ω) (hinst : inst.Standing)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, inst.p i j ≤ P)
    (S B : Finset (I × J)) (x : Ω → I → J → ℝ)
    (hx : ∀ ω, IsOptimal (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p S (x ω)) :
    inst.F B ≤ 2 * inst.F S + (B.card : ℝ) * inst.Emax P x S := by
  have hscenario : ∀ ω,
      lpValue (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p B ≤
        2 * lpValue (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p S +
        ∑ a ∈ B \ S, min (inst.c a.1 ω) (inst.d a.2 ω) *
          max (inst.p a.1 a.2
            - alphaBar (fun i => inst.c i ω) inst.p P (x ω) a.1
            - betaBar (fun j => inst.d j ω) inst.p P (x ω) a.2) 0 := by
    intro ω
    have hd := s09_dual_feasible_alphaBar_betaBar
      (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p
      (fun i => hinst.2.1 i ω) (fun j => hinst.2.2.1 j ω) hinst.2.2.2 P hP0 hP S (x ω) (hx ω)
    have hu := lpValue_upper (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p
      (fun i => hinst.2.1 i ω) (fun j => hinst.2.2.1 j ω) S B _ _ hd
    rw [dual_objective_eq_two_f
      (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p
      (fun i => hinst.2.1 i ω) (fun j => hinst.2.2.1 j ω) hinst.2.2.2 P hP0 hP S (x ω) (hx ω)] at hu
    exact hu
  have hweighted := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hscenario ω) (hinst.1 ω))
  have heq : (∑ ω, inst.μ ω *
      (2 * lpValue (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p S +
        ∑ a ∈ B \ S, min (inst.c a.1 ω) (inst.d a.2 ω) *
          max (inst.p a.1 a.2
            - alphaBar (fun i => inst.c i ω) inst.p P (x ω) a.1
            - betaBar (fun j => inst.d j ω) inst.p P (x ω) a.2) 0)) =
        2 * inst.F S + ∑ a ∈ B \ S, inst.E P x a.1 a.2 := by
    unfold FDPInstance.F FDPInstance.E
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    · simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
  have hsum : inst.F B ≤ 2 * inst.F S + ∑ a ∈ B \ S, inst.E P x a.1 a.2 := by
    exact hweighted.trans_eq heq
  exact hsum.trans (add_le_add le_rfl (correction_sum_le inst hinst P x S B))


end CoverModular.S09Dual


namespace CoverModular.S09Recurrence

/-- The exact greedy recurrence, including the one-step boundary case. -/
theorem recurrence_bound (K : ℕ) (hK : 1 ≤ K) (v : ℕ → ℝ) (B : ℝ)
    (hzero : v 0 = 0)
    (hstep : ∀ t < K, B ≤ 2 * v t + (K : ℝ) * (v (t + 1) - v t)) :
    (1 - (1 - 2 / (K : ℝ)) ^ K) / 2 * B ≤ v K := by
  by_cases hone : K = 1
  · subst K
    have hs := hstep 0 (by decide)
    norm_num [hzero] at hs ⊢
    exact hs
  have htwo : 2 ≤ K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hK)
  let q : ℝ := 1 - 2 / (K : ℝ)
  have hq : 0 ≤ q := by
    dsimp [q]
    have hk2 : (2 : ℝ) ≤ K := by exact_mod_cast htwo
    have hd : (2 : ℝ) / K ≤ 1 := (div_le_one hKr).2 hk2
    linarith
  have hrec (t : ℕ) (ht : t < K) : q * v t + B / K ≤ v (t + 1) := by
    apply (mul_le_mul_iff_right₀ hKr).mp
    have hid : (K : ℝ) * (q * v t + B / K) = ((K : ℝ) - 2) * v t + B := by
      dsimp [q]
      field_simp
      <;> ring
    rw [hid]
    nlinarith [hstep t ht]
  have hall : ∀ t, t ≤ K → (1 - q ^ t) / 2 * B ≤ v t := by
    intro t
    induction t with
    | zero =>
      intro _
      simp [hzero]
    | succ t ih =>
      intro ht
      have hprev := ih (Nat.le_trans (Nat.le_succ t) ht)
      have hs := hrec t (Nat.lt_of_succ_le ht)
      have hm := mul_le_mul_of_nonneg_left hprev hq
      have hid : (1 - q ^ (t + 1)) / 2 * B = q * ((1 - q ^ t) / 2 * B) + B / K := by
        rw [pow_succ]
        dsimp [q]
        field_simp
        <;> ring
      rw [hid]
      linarith
  exact hall K le_rfl


end CoverModular.S09Recurrence


namespace CoverModular.S09Recurrence

open scoped BigOperators

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]

theorem lp_empty (c : I → ℝ) (d : J → ℝ) (p : I → J → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ j, 0 ≤ d j) :
    lpValue c d p ∅ = 0 := by
  have hset : profit p '' {x | (network c d ∅).Feasible x} = {0} := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : x = fun _ _ => 0 := by
        funext i j
        exact hx.2.1 i j (by simp [network])
      simp [hx0, profit]
    · intro hr
      have hr0 : r = 0 := hr
      subst r
      refine ⟨fun _ _ => 0, ?_, by simp [profit]⟩
      refine ⟨fun _ _ => le_rfl, fun _ _ _ => rfl, ?_, ?_⟩
      · intro i
        simpa [network] using hc i
      · intro j
        simpa [network] using hd j
  rw [lpValue, hset, csSup_singleton]

theorem F_empty (inst : FDPInstance I J Ω) (hinst : inst.Standing) :
    inst.F ∅ = 0 := by
  unfold FDPInstance.F
  have hval (ω : Ω) :
      lpValue (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p ∅ = 0 :=
    lp_empty _ _ _ (fun i => hinst.2.1 i ω) (fun j => hinst.2.2.1 j ω)
  simp only [hval, mul_zero, Finset.sum_const_zero]

end CoverModular.S09Recurrence

open CoverModular

namespace CoverModular.S09Recurrence

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]
  [DecidableEq I] [DecidableEq J]

theorem run_card (inst : FDPInstance I J Ω) (P : ℝ) (K : ℕ)
    (A : ℕ → Finset (I × J)) (hA : inst.IsAlgorithm1Run P K A) :
    (A K).card ≤ K := by
  have hall : ∀ t, t ≤ K → (A t).card ≤ t := by
    intro t
    induction t with
    | zero =>
      intro _
      simp [hA.1]
    | succ t ih =>
      intro ht
      obtain ⟨x, hx, a, hins, hgain⟩ := hA.2 t (Nat.lt_of_succ_le ht)
      have hp := ih (Nat.le_trans (Nat.le_succ t) ht)
      rw [hins]
      exact (Finset.card_insert_le a (A t)).trans (Nat.add_le_add_right hp 1)
  exact hall K le_rfl

end CoverModular.S09Recurrence

theorem solution {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]
    [DecidableEq I] [DecidableEq J]
    (inst : FDPInstance I J Ω) (hinst : inst.Standing) (K : ℕ) (hK : 1 ≤ K)
    (P : ℝ) (hP0 : 0 ≤ P) (hP : ∀ i j, inst.p i j ≤ P)
    (A : ℕ → Finset (I × J)) (hA : inst.IsAlgorithm1Run P K A) :
    (A K).card ≤ K ∧
      (∀ B : Finset (I × J), B.card ≤ K →
        (1 - (1 - 2 / (K : ℝ)) ^ K) / 2 * inst.F B ≤ inst.F (A K)) ∧
      (1 - Real.exp (-2)) / 2 ≤ (1 - (1 - 2 / (K : ℝ)) ^ K) / 2 := by
  refine ⟨CoverModular.S09Recurrence.run_card inst P K A hA, ?_,
    CoverModular.approximation_factor_ge K hK⟩
  intro B hB
  apply CoverModular.S09Recurrence.recurrence_bound K hK (fun t => inst.F (A t)) (inst.F B)
  · rw [hA.1, CoverModular.S09Recurrence.F_empty inst hinst]
  · intro t ht
    obtain ⟨x, hx, a, hins, hgain⟩ := hA.2 t ht
    have hc := CoverModular.S09Dual.structural_comparison inst hinst P hP0 hP (A t) B x hx
    have he := CoverModular.S09Dual.Emax_nonneg inst hinst P x (A t)
    have hb : (B.card : ℝ) ≤ K := by exact_mod_cast hB
    have hmul := mul_le_mul_of_nonneg_right hb he
    have hg : inst.Emax P x (A t) ≤ inst.F (A (t + 1)) - inst.F (A t) := by
      linarith
    have hmul2 := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    exact hc.trans (add_le_add le_rfl (hmul.trans hmul2))


#print axioms solution
