-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cutoff_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:08:35.462657+00:00
-- url     : https://prove2.me/submissions/5e377735-b46b-4a0b-91e5-3facf701419f

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_contDiff_Gf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.CutFSmooth := by
  intro k r Wp Wq _ _ _ _ Bs χ f ε hχ hf hε g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hff'⟩ := hf g₀ hg₀
  refine ⟨U, fun g => ((χ (Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • f' g, hU, hg₀U, ?_, ?_⟩
  · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun g : B.Mat k r => ((χ (Formalism.QuantumDeterminants.Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hχ.1.comp ((JCx1.contDiff_Gf Bs.z Bs.z').div_const ε))
    exact h1.contDiffOn.smul hf'
  · intro g hgU hgV
    simp only [D.cutF, hff' g hgU hgV]
end Formalism.FourierDecayAlt.P
