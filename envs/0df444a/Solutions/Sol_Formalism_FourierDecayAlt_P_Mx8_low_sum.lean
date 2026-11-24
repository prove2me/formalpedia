-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.low_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:50.020926+00:00
-- url     : https://prove2.me/submissions/d27aa69a-d041-4d3f-99b9-0860e75e4969

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx8
namespace Formalism.FourierDecayAlt.P.Mx8
theorem _root_.solution (hSh : SSShift) (hRho : RhoUp) (P : Par) (Y : ℂ) (hY : ∀ π, xC P π Y ≠ 0) :
    xA P Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j = weightedSumBis P Y := by
  rw [Finset.mul_sum, weightedSumBis]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, xA, ← map_mul]
  refine hSh P j _ _ fun π π' hU => ?_
  have hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1) := Finset.singleton_subset_iff.2 hj
  have h1 : xC P π' Y = xEx P {j} π' Y * (Y + (rho P π' j : ℂ)) := by
    rw [xC, xEx, ← Finset.prod_sdiff hsub, Finset.prod_singleton]
  have h2 : Y + (rho P π' j : ℂ) ≠ 0 := fun h0 => hY π' (by rw [h1, h0, mul_zero])
  have h3 : xEx P {j} π' Y = xEx P {j} π Y := by
    unfold xEx
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    rw [hRho P j π π' hU i hi.1, if_neg hi.2, add_zero]
  show xC P π' Y * (Y + (rho P π' j : ℂ))⁻¹ = xEx P {j} π Y
  rw [h1, mul_assoc, mul_inv_cancel₀ h2, mul_one, h3]
end Formalism.FourierDecayAlt.P.Mx8
