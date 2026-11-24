-- Prove2me | solution 1 for Formalism.L2.Pj.LieAlg.tri_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:16:20.884845+00:00
-- url     : https://prove2.me/submissions/e09cba02-052e-46e6-926d-537049899d42

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieAlg
open Submodule
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
namespace Formalism.L2.Pj.LieAlg
theorem _root_.solution {n m : ℕ} (P : (Fin n → K) → Prop) (v : Fin m → (Fin n → K))
    (hb : ∀ w, P w → ∃! cf : Fin m → K, w = ∑ i, cf i • v i) (C : Fin m → Fin m → K)
    (hCz : ∀ i j, i < j → C i j = 0) (hCd : ∀ i, C i i ≠ 0) :
    ∀ w, P w → ∃! d : Fin m → K, w = ∑ i, d i • ∑ j, C i j • v j := by
  classical
  let A : Matrix (Fin m) (Fin m) K := Matrix.of C
  have hA : A.IsLowerTriangular := fun i j h => hCz i j h
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular A hA]
    exact Finset.prod_ne_zero_iff.2 (fun i _ => hCd i)
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have expand : ∀ d : Fin m → K, ∑ i, d i • ∑ j, C i j • v j = ∑ j, (Matrix.vecMul d A) j • v j := by
    intro d
    simp only [Matrix.vecMul, dotProduct, A, Matrix.of_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  intro w hw
  obtain ⟨cf, hcf, huniq⟩ := hb w hw
  refine ⟨Matrix.vecMul cf A⁻¹, ?_, fun d hd => ?_⟩
  · show w = _
    rw [expand, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul A hu, Matrix.vecMul_one]
    exact hcf
  · have h1 : Matrix.vecMul d A = cf := huniq _ (by show w = _; rw [← expand]; exact hd)
    rw [← h1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hu, Matrix.vecMul_one]
end Formalism.L2.Pj.LieAlg
