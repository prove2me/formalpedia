-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.decay.psd_two_cs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:54.452094+00:00
-- url     : https://prove2.me/submissions/a85741e4-7ecc-4e71-a18b-eb567dcb66de

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay


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
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.JCx1.decay
theorem _root_.solution (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.PosSemidef) :
    ‖M 0 1‖ ^ 2 ≤ (M 0 0).re * (M 1 1).re ∧ 0 ≤ (M 0 0).re ∧ 0 ≤ (M 1 1).re := by
  have hH := hM.1
  have h01 : star (M 0 1) = M 1 0 := hH.apply 1 0
  have h00 : star (M 0 0) = M 0 0 := hH.apply 0 0
  have h11 : star (M 1 1) = M 1 1 := hH.apply 1 1
  have hd0 : (M 0 0).im = 0 := Complex.conj_eq_iff_im.1 h00
  have hd1 : (M 1 1).im = 0 := Complex.conj_eq_iff_im.1 h11
  have hdet : 0 ≤ M.det := hM.det_nonneg
  have p0 : 0 ≤ M 0 0 := hM.diag_nonneg
  have p1 : 0 ≤ M 1 1 := hM.diag_nonneg
  rw [Matrix.det_fin_two, ← h01] at hdet
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.sq_norm, Complex.normSq_apply]
    have hre := (Complex.le_def.1 hdet).1
    simp only [Complex.zero_re, Complex.sub_re, Complex.mul_re, hd0, hd1, Complex.star_def,
      Complex.conj_re, Complex.conj_im] at hre
    nlinarith [hre]
  · have := (Complex.le_def.1 p0).1
    simpa using this
  · have := (Complex.le_def.1 p1).1
    simpa using this
end Formalism.FourierDecayAlt.P.JCx1.decay
