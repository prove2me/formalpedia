-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.herm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:49:29.936795+00:00
-- url     : https://prove2.me/submissions/6fcdc06c-31c6-4ee9-866e-45ea8109da8d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (hH : Hᴴ = H) (u v : ι → ℂ) : conj (herm H u v) = herm H v u := by
  have hc : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    rwa [Matrix.conjTranspose_apply] at this
  show star (star v ⬝ᵥ (H *ᵥ u)) = star u ⬝ᵥ (H *ᵥ v)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
end Formalism.FourierDecayAlt.P.B2x8
