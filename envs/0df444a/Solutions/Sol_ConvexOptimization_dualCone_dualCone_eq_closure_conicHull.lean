-- Prove2me | solution 1 for ConvexOptimization.dualCone_dualCone_eq_closure_conicHull
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-15T14:25:54.36822+00:00
-- url     : https://prove2.me/submissions/9bc4db00-4436-4cdd-b200-ca9f010b192a

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_conicHull

open Set ConvexOptimization
open scoped RealInnerProductSpace ENNReal

theorem solution {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    dualCone (dualCone K) = closure (conicHull K) := by
  let E := EuclideanSpace ℝ (Fin n)
  let C₀ : PointedCone ℝ E :=
    { carrier := conicHull K
      zero_mem' := by
        refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · simp
      add_mem' := by
        rintro x y ⟨m, θ, u, hθ, hu, rfl⟩ ⟨k, η, v, hη, hv, rfl⟩
        refine ⟨m + k, Fin.append θ η, Fin.append u v, ?_, ?_, ?_⟩
        · intro i
          refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
          · simpa using hθ j
          · simpa using hη j
        · intro i
          refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
          · simpa using hu j
          · simpa using hv j
        · rw [Fin.sum_univ_add]
          simp
      smul_mem' := by
        rintro ⟨a, ha⟩ x ⟨m, θ, u, hθ, hu, rfl⟩
        refine ⟨m, fun i ↦ a * θ i, u, fun i ↦ mul_nonneg ha (hθ i), hu, ?_⟩
        simp_rw [mul_smul]
        rw [Finset.smul_sum]
        change ∑ x, a • θ x • u x = ∑ x, a • θ x • u x
        rfl }
  let C : ProperCone ℝ E :=
    { toSubmodule := C₀.closure
      isClosed' := isClosed_closure }
  have hK_conic : K ⊆ conicHull K := by
    intro x hx
    refine ⟨1, fun _ ↦ 1, fun _ ↦ x, fun _ ↦ zero_le_one, fun _ ↦ hx, ?_⟩
    simp
  have hdual :
      ProperCone.dual (innerₗ E).flip (C : Set E) = ProperCone.dual (innerₗ E) K := by
    ext y
    simp only [ProperCone.mem_dual]
    constructor
    · intro hy x hx
      have hxC : x ∈ C := by
        exact subset_closure (hK_conic hx)
      simpa [real_inner_comm] using hy hxC
    · intro hy z hz
      have hconic : ∀ w ∈ conicHull K, 0 ≤ (innerₗ E) y w := by
        rintro w ⟨m, θ, u, hθ, hu, rfl⟩
        change 0 ≤ inner ℝ y (∑ i, θ i • u i)
        rw [inner_sum]
        simp_rw [inner_smul_right]
        exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hθ i) (by
          simpa [real_inner_comm] using hy (hu i))
      have hclosed : IsClosed {w : E | 0 ≤ (innerₗ E) y w} := by
        exact isClosed_Ici.preimage ((innerₗ E y).continuous_of_finiteDimensional)
      exact hclosed.closure_subset_iff.mpr hconic hz
  have hcustom₂ : dualCone (dualCone K) =
      (ProperCone.dual (innerₗ E) (dualCone K) : Set E) := rfl
  have hcustom : dualCone K = (ProperCone.dual (innerₗ E) K : Set E) := rfl
  rw [hcustom₂, hcustom, ← hdual]
  exact congr_arg SetLike.coe (ProperCone.dual_dual_flip (innerₗ E) C)
