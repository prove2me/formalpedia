-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.ckOn_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:41:21.868023+00:00
-- url     : https://prove2.me/submissions/b910c4c7-e3b3-432d-9c0a-74cd821b2c46

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_phi_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_cd_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_continuous_phi_mu
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
set_option linter.style.haveILetI false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {n n' : B.Mat k r} (hn : n ∈ B.GV k r) (hn' : n' ∈ B.GV k r)
    {m : ℕ∞} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn m (B.GV k r) f) : B.CkOn m (B.GV k 0) (fun μ => f (phi k r c n n' μ)) := by
  intro μ₀ hμ₀
  obtain ⟨U, f', hU, hgU, hf', hagree⟩ := hf _ (phi_mem hc hn hn' hμ₀)
  refine ⟨phi k r c n n' ⁻¹' U, fun μ => f' (phi k r c n n' μ), hU.preimage (continuous_phi_mu c n n'), hgU, ?_, ?_⟩
  · exact hf'.comp ((tr_cd_phi c n n').mono (Set.subset_univ _) |>.of_le (by exact_mod_cast le_top))
      (fun μ hμ => hμ)
  · intro μ hμ hμG
    exact hagree _ hμ (phi_mem hc hn hn' hμG)
end Formalism.FourierDecayAlt.P.SliceLastLevel
