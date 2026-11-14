-- Prove2me | solution 1 for FullForesight.Randomized.remark_1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:05:46.188006+00:00
-- url     : https://prove2.me/submissions/bbe71e58-ee7c-49c4-9550-d48ce1d29362

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants
import Definitions.Def_FullForesight_Randomized_Model
import Definitions.Def_FullForesight_Randomized_Coverage
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_randomizedUpperLimit
import Theorems.Thm_ConsistentSubmodular_psiRoot

namespace FullForesight.Randomized.Bridge

/-- The two encodings of `Ψ` agree. -/
theorem Psi_eq_psi (ξ : ℝ) : Psi ξ = ConsistentSubmodular.psi ξ := rfl

/-- The two encodings of `ξ⋆` agree: `Ψ` has no root at the endpoints `1/2` and `1`,
so the root set on `[1/2, 1]` is the root set on `(1/2, 1)`. -/
theorem xiStar_eq : xiStar = ConsistentSubmodular.xiStar := by
  unfold xiStar ConsistentSubmodular.xiStar
  congr 1
  ext ξ
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Psi_eq_psi]
  constructor
  · rintro ⟨⟨h1, h2⟩, h0⟩
    refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, h0⟩
    · rintro rfl
      norm_num [ConsistentSubmodular.psi] at h0
    · rintro rfl
      norm_num [ConsistentSubmodular.psi] at h0
  · rintro ⟨h1, h2, h0⟩
    exact ⟨⟨h1.le, h2.le⟩, h0⟩

end FullForesight.Randomized.Bridge

namespace FullForesight.Randomized.Bridge

open ConsistentSubmodular

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

/-- A trajectory law as a random trajectory of the source development. -/
def ofLaw {n : ℕ} (L : TrajLaw n) : RandomTrajectory n := ⟨L.w, L.nonneg, L.sum_eq_one⟩

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

theorem le_optVal {n : ℕ} (f : Finset (Fin n) → ℝ) (k t : ℕ) (A : Finset (Fin n))
    (hA : A ⊆ arrivedPrefix n t) (hk : A.card ≤ k) : f A ≤ optVal f k t :=
  Finset.le_sup' f (Finset.mem_filter.2 ⟨Finset.mem_univ _, hA, hk⟩)

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

theorem ofLaw_feasible {n k : ℕ} {L : TrajLaw n} {c : ℝ} (hv : L.Valid k)
    (hc : L.Consistent c) : (ofLaw L).Feasible k ⌊c⌋₊ := by
  intro A hA
  have hpos : 0 < L.w A := lt_of_le_of_ne (L.nonneg A) (Ne.symm hA)
  obtain ⟨h0, h1⟩ := hv A hpos
  refine ⟨h0, h1, fun t => ?_⟩
  unfold recourse
  rw [Finset.union_comm]
  exact Nat.le_floor (hc A hpos t)

/-- A time and a competitor beating the law by a factor below `α` refute `α`-approximation. -/
theorem not_approx {n k : ℕ} {L : TrajLaw n} {f : Finset (Fin n) → ℝ} {α β : ℝ}
    (t : Fin (n + 1)) (A : Finset (Fin n)) (hA : A ⊆ arrivedPrefix n t.val) (hk : A.card ≤ k)
    (hpos : 0 < f A) (hβ : 0 ≤ β) (hαβ : β < α) (h : (ofLaw L).expectation f t ≤ β * f A) :
    ¬ L.Approx f k α := by
  intro happ
  have h1 := happ t
  have h2 := le_optVal f k t A hA hk
  have h3 : L.expect f t = (ofLaw L).expectation f t := rfl
  have h4 : β * f A ≤ β * optVal f k t := mul_le_mul_of_nonneg_left h2 hβ
  have h5 : 0 < optVal f k t := lt_of_lt_of_le hpos h2
  have h6 : β * optVal f k t < α * optVal f k t := mul_lt_mul_of_pos_right hαβ h5
  linarith

end FullForesight.Randomized.Bridge

namespace FullForesight.Randomized.Bridge

open ConsistentSubmodular

/-- Coverage over a universe `Fin u`, as coverage by finite sets of naturals. -/
def natCover {n u : ℕ} (cover : Fin n → Finset (Fin u)) : Fin n → Finset ℕ :=
  fun i => (cover i).map Fin.valEmbedding

theorem coverage_natCover {n u : ℕ} (cover : Fin n → Finset (Fin u)) (A : Finset (Fin n)) :
    coverage (natCover cover) A = coverageValue cover A := by
  unfold coverage coverageValue natCover
  have h : (A.biUnion fun i => (cover i).map Fin.valEmbedding)
      = (A.biUnion cover).map Fin.valEmbedding := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_map]
    constructor
    · rintro ⟨i, hi, y, hy, rfl⟩
      exact ⟨y, ⟨i, hi, hy⟩, rfl⟩
    · rintro ⟨y, ⟨i, hi, hy⟩, rfl⟩
      exact ⟨i, hi, y, hy, rfl⟩
  rw [h, Finset.card_map]

theorem coverage_natCover' {n u : ℕ} (cover : Fin n → Finset (Fin u)) :
    coverage (natCover cover) = coverageValue cover :=
  funext (coverage_natCover cover)

end FullForesight.Randomized.Bridge

open FullForesight.Randomized FullForesight.Randomized.Bridge in
theorem solution :
    ∀ C δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ (n : ℕ) (s : Fin n → Finset ℕ), ∀ L : TrajLaw n, L.Valid k →
        L.Consistent C → ∀ α : ℝ, xiStar + δ < α → ¬ L.Approx (coverage s) k α := by
  intro C δ hδ
  obtain ⟨hξ, -⟩ := ConsistentSubmodular.psiRoot
  obtain ⟨k₀, hk₀⟩ := ConsistentSubmodular.randomizedUpperLimit ⌊C⌋₊ δ hδ
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨n, u, cover, hcov⟩ := hk₀ k hk
  refine ⟨n, natCover cover, fun L hv hc α hα => ?_⟩
  obtain ⟨t, A, hA, hAk, hlt⟩ := hcov (ofLaw L) (ofLaw_feasible hv hc)
  rw [xiStar_eq] at hα
  rw [coverage_natCover']
  have hβ : 0 < ConsistentSubmodular.xiStar + δ := by linarith
  have hE : 0 ≤ (ofLaw L).expectation (ConsistentSubmodular.coverageValue cover) t :=
    Finset.sum_nonneg fun S _ => mul_nonneg ((ofLaw L).prob_nonneg S)
      (by unfold ConsistentSubmodular.coverageValue; positivity)
  have hpos : 0 < ConsistentSubmodular.coverageValue cover A := by
    by_contra hneg
    have h0 : ConsistentSubmodular.coverageValue cover A ≤ 0 := not_lt.1 hneg
    have : (ConsistentSubmodular.xiStar + δ) * ConsistentSubmodular.coverageValue cover A ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hβ.le h0
    linarith
  exact not_approx t A hA hAk hpos hβ.le hα hlt.le
