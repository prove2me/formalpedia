-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.sz_contK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:12:56.976597+00:00
-- url     : https://prove2.me/submissions/5b800083-b795-4644-b5b6-5b0ff068361c

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {r : ℕ} (s : ℕ) (K : Set (Fin r → ℂ)) (hK0 : ∀ c ∈ K, ∀ a, c a ≠ 0) :
    ContinuousOn (fun c : Fin r → ℂ => 2 * unitriangularFactorConstant c + ∑ a, ‖c a‖ + (s.factorial : ℝ) / ‖∏ a, c a‖) K := by
  have hp : ∀ (q : ℕ) (f : Fin q → Fin r), ContinuousOn (fun c : Fin r → ℂ => ‖∏ t, c (f t)‖) K :=
    fun q f => (continuous_finset_prod _ fun t _ => continuous_apply (f t)).norm.continuousOn
  have hne : ∀ (q : ℕ) (f : Fin q → Fin r), ∀ c ∈ K, ‖∏ t, c (f t)‖ ≠ 0 := fun q f c hc => by
    rw [norm_ne_zero_iff]; exact Finset.prod_ne_zero_iff.mpr fun t _ => hK0 c hc (f t)
  refine ((continuousOn_const.mul ?_).add ?_).add ?_
  · unfold unitriangularFactorConstant
    exact continuousOn_finset_sum _ fun i _ => continuousOn_const.div (hp _ _) (hne _ _)
  · exact continuousOn_finset_sum _ fun a _ => (continuous_apply a).norm.continuousOn
  · exact (continuousOn_const (c := (s.factorial : ℝ)) (s := K)).div (hp r id) (hne r id)
end Formalism.FourierDecayAlt.P.SliceLastLevel
