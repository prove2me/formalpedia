-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.herm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:49:17.113808+00:00
-- url     : https://prove2.me/submissions/fb7bbcaa-b00a-46ec-9479-0c54503a7839

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (hH : Hᴴ = H) (u v : ι → ℂ) : conj (herm H u v) = herm H v u := by
  have h : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    rwa [conjTranspose_apply] at this
  simp only [herm, dotProduct, mulVec, Pi.star_apply, starRingEnd_apply, star_sum, star_mul', star_star, h,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end Formalism.FourierDecayAlt.P.B2x5
