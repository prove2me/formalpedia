-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.hb_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:01:30.007236+00:00
-- url     : https://prove2.me/submissions/5f3d207b-f81a-4cde-901b-137ec6eb633e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' y s + star (hb k r' y s) + herm (Hpk k r') y y = 0 := by
  have h := herm_symm _ (Hpk_herm k r') y y
  have him : (herm (Hpk k r') y y).im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  apply Complex.ext
  · simp [hb]
  · simp [hb, him]
end Formalism.FourierDecayAlt.P.B2x4
