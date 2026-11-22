-- Prove2me | solution 1 for Bl.DetNormLeProdRows.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:43.883929+00:00
-- url     : https://prove2.me/submissions/bef1503d-470f-4448-a117-fe46342ceb13

import Mathlib
import Definitions.Def_Formalism_GelfandTransference_Statement
import Definitions.Def_Lemmata_DetNormLeProdRows_DetNormLeProdRows
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.DetNormLeProdRows
private theorem det_norm_le_prod_rows (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ) :
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin ρ))‖ := by
  classical
  let v : Fin ρ → EuclideanSpace ℂ (Fin ρ) := fun i => WithLp.toLp 2 (A i)
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin ρ)) = Fintype.card (Fin ρ) := by simp
  let e := (EuclideanSpace.basisFun (Fin ρ) ℂ).toBasis
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h v
  have he : e.det v = A.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose A]
    congr 1
  have hbv : b.toBasis.det v = b.toBasis.det e * e.det v := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  have hb1 : ‖b.toBasis.det e‖ = 1 := by
    simp [e]
  have key : ‖A.det‖ = ‖b.toBasis.det v‖ := by
    rw [hbv, norm_mul, hb1, one_mul, he]
  rw [key, InnerProductSpace.gramSchmidtOrthonormalBasis_det h v, norm_prod]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  intro i _
  calc ‖inner ℂ (b i) (v i)‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]
end Bl.DetNormLeProdRows
end

set_option autoImplicit false
open Bl Bl.DetNormLeProdRows
namespace Bl.DetNormLeProdRows
theorem _root_.solution :
  Formalism.HadamardInequality.Hadamard := by
  intro ρ A
  have h0 := det_norm_le_prod_rows ρ A
  calc ‖A.det‖ ^ 2 ≤ (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin ρ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h0 2
    _ = ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [EuclideanSpace.norm_sq_eq]
end Bl.DetNormLeProdRows
