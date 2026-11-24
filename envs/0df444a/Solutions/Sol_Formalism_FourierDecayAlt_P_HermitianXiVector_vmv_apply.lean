-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianXiVector.vmv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:33.139146+00:00
-- url     : https://prove2.me/submissions/6b695b03-c20e-4b3b-9510-8cc14144221f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.HermitianXiVector
open C2x5 FlagSpanVanishing
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianXiVector
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (a b y : Fin n → ℂ) :
    vecMulVec a (star (H *ᵥ b)) *ᵥ y = herm H y b • a := by
  have hH' : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    rwa [conjTranspose_apply] at this
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, herm, Pi.star_apply, star_sum, star_mul', hH', Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
end Formalism.FourierDecayAlt.P.HermitianXiVector
