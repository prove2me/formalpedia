-- Prove2me | solution 1 for FullForesight.Randomized.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:00:34.720338+00:00
-- url     : https://prove2.me/submissions/cddc55c5-b7a6-415a-a6c0-d09d23e24b31

import Mathlib
import Definitions.Def_FullForesight_Randomized_Model
import Definitions.Def_FullForesight_Randomized_AdditionRobust
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_additionRobustReduction

/-!
# Bridge: Lemma 1 of the mission from Lemma 1 of the source development

The source development proves `ConsistentSubmodular.additionRobustReduction`. This file
derives the mission's statement `FullForesight.Randomized.lemma_1` from it.

* The conclusion is converted by `of_randomizedGuarantee` (the two models of clairvoyant
  consistent algorithms agree).
* The hypothesis is converted by `admits_of_platform`: a window instance with single arrivals
  of the source development is an addition-robust instance of the mission, so the mission's
  hypothesis yields the source development's `AdmitsAdditionRobust`.
-/

namespace FullForesight.Randomized.Bridge

open ConsistentSubmodular

/-! ## The conclusion: the two models of clairvoyant consistent algorithms -/

/-- Diminishing returns implies the lattice form of submodularity. -/
theorem lattice_of_dr {α : Type*} [DecidableEq α] (f : Finset α → ℝ)
    (h : SubsamplingSM.Offline.IsSubmodular f) (A B : Finset α) :
    f (A ∪ B) + f (A ∩ B) ≤ f A + f B := by
  have key : ∀ (D S T : Finset α), S ⊆ T → Disjoint D T →
      f (T ∪ D) - f T ≤ f (S ∪ D) - f S := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro S T _ _; simp
    | insert e D he ih =>
      intro S T hST hd
      rw [Finset.disjoint_insert_left] at hd
      have h1 := ih S T hST hd.2
      have h2 : f (insert e (T ∪ D)) - f (T ∪ D) ≤ f (insert e (S ∪ D)) - f (S ∪ D) :=
        h (S ∪ D) (T ∪ D) e (Finset.union_subset_union_left hST)
          (by simp [hd.1, he])
      have e1 : T ∪ insert e D = insert e (T ∪ D) := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      have e2 : S ∪ insert e D = insert e (S ∪ D) := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [e1, e2]
      linarith
  have h1 := key (A \ B) (A ∩ B) B Finset.inter_subset_right Finset.sdiff_disjoint
  have e1 : B ∪ A \ B = A ∪ B := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have e2 : A ∩ B ∪ A \ B = A := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  rw [e1, e2] at h1
  linarith

/-- An instance of the mission's model as an `Objective` of the source development. -/
def toObjective {n k : ℕ} {f : Finset (Fin n) → ℝ} (h : IsInstance k f) : Objective n where
  value := f
  nonnegative := h.2.1
  monotone := h.2.2.1
  submodular := lattice_of_dr f h.2.2.2

/-- A random trajectory of the source development as a trajectory law. -/
def toLaw {n : ℕ} (μ : RandomTrajectory n) : TrajLaw n := ⟨μ.prob, μ.prob_nonneg, μ.prob_sum⟩

theorem toLaw_valid {n k C : ℕ} {μ : RandomTrajectory n} (h : μ.Feasible k C) :
    (toLaw μ).Valid k := by
  intro A hA
  obtain ⟨h0, h1, -⟩ := h A (ne_of_gt hA)
  exact ⟨h0, h1⟩

theorem toLaw_consistent {n k C : ℕ} {μ : RandomTrajectory n} (h : μ.Feasible k C) {c : ℝ}
    (hc : (C : ℝ) ≤ c) : (toLaw μ).Consistent c := by
  intro A hA t
  obtain ⟨-, -, h2⟩ := h A (ne_of_gt hA)
  have h3 := h2 t
  unfold recourse at h3
  rw [Finset.union_comm]
  exact le_trans (by exact_mod_cast h3) hc

/-- The optimum `f(OPT_t)` is attained by a feasible set. -/
theorem optVal_attained {n : ℕ} (f : Finset (Fin n) → ℝ) (k t : ℕ) :
    ∃ A : Finset (Fin n), A ⊆ arrivedPrefix n t ∧ A.card ≤ k ∧ optVal f k t = f A := by
  obtain ⟨A, hA, hEq⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S ⊆ arrived n t ∧ S.card ≤ k)) ⟨∅, by simp⟩ f
  rw [Finset.mem_filter] at hA
  exact ⟨A, hA.2.1, hA.2.2, hEq⟩

theorem toLaw_approx {n k : ℕ} {μ : RandomTrajectory n} {f : Finset (Fin n) → ℝ} {a : ℝ}
    (h : ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
      A ⊆ arrivedPrefix n t.val → A.card ≤ k → a * f A ≤ μ.expectation f t) :
    (toLaw μ).Approx f k a := by
  intro t
  obtain ⟨A, hA, hk, hEq⟩ := optVal_attained f k t
  rw [hEq]
  exact h t A hA hk

/-- A randomized guarantee of the source development, in the mission's model. -/
theorem of_randomizedGuarantee {a e : ℝ} {C : ℕ} (h : RandomizedGuarantee a e C) {c : ℝ}
    (hc : (C : ℝ) ≤ c) (n k : ℕ) (f : Finset (Fin n) → ℝ) (hf : IsInstance k f) :
    ∃ L : TrajLaw n, L.Valid k ∧ L.Consistent c ∧ L.Approx f k (a - e) := by
  obtain ⟨μ, hμ, happ⟩ := h n k (toObjective hf)
  exact ⟨toLaw μ, toLaw_valid hμ, toLaw_consistent hμ hc, toLaw_approx happ⟩

/-! ## The hypothesis: the two models of the addition-robust problem -/

/-- The lattice form of submodularity implies diminishing returns. -/
theorem dr_of_lattice {n : ℕ} (f : Objective n) :
    SubsamplingSM.Offline.IsSubmodular f.value := by
  intro A B e hAB he
  have h := f.submodular (insert e A) B
  have e1 : insert e A ∪ B = insert e B := by
    ext x; simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hAB h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  have e2 : insert e A ∩ B = A := by
    ext x; simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h | h, hB⟩
      · exact absurd (h ▸ hB) he
      · exact h
    · intro h
      exact ⟨Or.inr h, hAB h⟩
  rw [e1, e2] at h
  linarith

/-- The mission's hypothesis (every addition-robust instance, over any ground type, with any
number of future elements and any budget, has an `α`-robust distribution) implies the source
development's `AdmitsAdditionRobust α`: a window instance with single arrivals is such an
instance, its future sequence being the elements added stage by stage. -/
theorem admits_of_platform {α : ℝ}
    (H : ∀ (X : Type) [DecidableEq X] (m : ℕ) (f : Finset X → ℝ) (Vnow : Finset X)
        (v : Fin m → X) (κ : ℕ), IsARInstance f Vnow v →
          ∃ μ : Finset X → ℝ, IsRobustDist f Vnow v κ α μ) :
    AdmitsAdditionRobust α := by
  intro n W hS
  choose v hv1 hv2 using hS
  -- the prefixes of the future sequence are the arrival sets
  have hpre : ∀ j : Fin (W.lastStage + 1), prefixSet v (j : ℕ) = W.arrivals j := by
    intro j
    induction j using Fin.induction with
    | zero =>
      rw [W.arrivals_zero]
      simp [prefixSet]
    | succ i ih =>
      rw [hv2 i, ← ih]
      ext x
      simp only [prefixSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Fin.val_succ, Fin.val_castSucc]
      constructor
      · rintro ⟨a, ha, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | h
        · exact Or.inr ⟨a, h, rfl⟩
        · exact Or.inl (congrArg v (Fin.ext h))
      · rintro (rfl | ⟨a, ha, rfl⟩)
        · exact ⟨i, Nat.lt_succ_self _, rfl⟩
        · exact ⟨a, Nat.lt_succ_of_lt ha, rfl⟩
  have hmem : ∀ i : Fin W.lastStage, v i ∈ W.arrivals i.succ := by
    intro i
    rw [hv2 i]
    exact Finset.mem_insert_self _ _
  have hlt : ∀ i j : Fin W.lastStage, i < j → v i ≠ v j := by
    intro i j hij heq
    have h2 : i.succ ≤ j.castSucc := by
      rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_of_lt hij
    have h3 : v i ∈ W.arrivals j.castSucc := W.arrivals_mono h2 (hmem i)
    exact hv1 j (heq ▸ h3)
  have hinj : Function.Injective v := by
    intro i j heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt i j h heq
    · exact hlt j i h heq.symm
  have hnot : ∀ i, v i ∉ W.present := fun i hi =>
    Finset.disjoint_left.1 (W.arrivals_disjoint i.succ) (hmem i) hi
  have hAR : IsARInstance W.objective.value W.present v :=
    ⟨W.objective.nonnegative, W.objective.monotone, dr_of_lattice W.objective, hinj, hnot⟩
  obtain ⟨μ, hμ0, hμ1, hμc, hμr⟩ :=
    H (Fin n) W.lastStage W.objective.value W.present v W.coreBudget hAR
  -- the two benchmarks agree
  have hbench : ∀ j : Fin (W.lastStage + 1),
      benchmark W.objective.value W.present v W.coreBudget j = W.benchmark j := by
    intro j
    unfold benchmark WindowInstance.benchmark
    rw [hpre j]
    apply le_antisymm
    · apply Finset.sup'_le
      intro O hO
      rw [Finset.mem_filter, Finset.mem_powerset] at hO
      exact W.candidate_optimal j O hO.1 hO.2
    · exact Finset.le_sup' (fun O => W.objective.value (O ∪ W.arrivals j))
        (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (W.candidate_subset j), W.candidate_card j⟩)
  -- extend `μ` by zero outside the subsets of `present`
  have hsum : ∀ g : Finset (Fin n) → ℝ,
      ∑ S, (if S ⊆ W.present then μ S else 0) * g S = ∑ S ∈ W.present.powerset, μ S * g S := by
    intro g
    rw [← Finset.sum_subset (Finset.subset_univ W.present.powerset)]
    · apply Finset.sum_congr rfl
      intro S hS
      rw [if_pos (Finset.mem_powerset.1 hS)]
    · intro S _ hS
      rw [if_neg (fun h => hS (Finset.mem_powerset.2 h)), zero_mul]
  have h1 : ∀ S, 0 ≤ (if S ⊆ W.present then μ S else 0) := by
    intro S
    by_cases h : S ⊆ W.present
    · rw [if_pos h]
      exact hμ0 S (Finset.mem_powerset.2 h)
    · rw [if_neg h]
  have h2 : (∑ S, (if S ⊆ W.present then μ S else 0)) = 1 := by
    have h := hsum (fun _ => 1)
    simp only [mul_one] at h
    rw [h]
    exact hμ1
  have h3 : ∀ S, (if S ⊆ W.present then μ S else 0) ≠ 0 →
      S ⊆ W.present ∧ S.card ≤ W.coreBudget := by
    intro S hS
    by_cases h : S ⊆ W.present
    · rw [if_pos h] at hS
      have hm := Finset.mem_powerset.2 h
      exact ⟨h, hμc S hm (lt_of_le_of_ne (hμ0 S hm) (Ne.symm hS))⟩
    · rw [if_neg h] at hS
      exact absurd rfl hS
  have h4 : ∀ j, α * W.benchmark j ≤
      ∑ S, (if S ⊆ W.present then μ S else 0) * W.objective.value (S ∪ W.arrivals j) := by
    intro j
    have h := hμr j
    rw [hbench j, hpre j] at h
    rw [hsum]
    exact h
  exact ⟨fun S => if S ⊆ W.present then μ S else 0, h1, h2, h3, h4⟩

end FullForesight.Randomized.Bridge

open FullForesight.Randomized in
theorem solution :
    ∃ c : ℝ, ∀ α γ : ℝ, 0 ≤ α → α ≤ 1 → γ ∈ Set.Ioo (0 : ℝ) (1 / 8) →
      (∀ (X : Type) [DecidableEq X] (m : ℕ) (f : Finset X → ℝ) (Vnow : Finset X)
        (v : Fin m → X) (κ : ℕ), IsARInstance f Vnow v →
          ∃ μ : Finset X → ℝ, IsRobustDist f Vnow v κ α μ) →
      ∀ (n k : ℕ) (f : Finset (Fin n) → ℝ), IsInstance k f →
        ∃ L : TrajLaw n, L.Valid k ∧ L.Consistent (c / γ ^ 2) ∧ L.Approx f k (α - 3 * γ) := by
  obtain ⟨K, hK⟩ := ConsistentSubmodular.additionRobustReduction
  refine ⟨K, fun α γ hα0 hα1 hγ H n k f hf => ?_⟩
  obtain ⟨C, hC, hG⟩ := hK γ hγ.1 hγ.2
  refine Bridge.of_randomizedGuarantee (hG α hα0 hα1 (Bridge.admits_of_platform H)) ?_ n k f hf
  rwa [one_div, inv_pow, ← div_eq_mul_inv] at hC
