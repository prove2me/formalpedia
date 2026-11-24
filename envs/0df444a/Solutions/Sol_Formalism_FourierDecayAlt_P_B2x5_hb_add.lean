-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.hb_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:01:30.776088+00:00
-- url     : https://prove2.me/submissions/1c5a3be7-9255-4f80-81bd-f91336556598

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_add_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_Hherm

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
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) (s s' : ℝ) :
    hb k r' y s + hb k r' y' s' - herm (Hpk k r') y' y = hb k r' (y + y') (s + s' - (herm (Hpk k r') y' y).im) := by
  have h1 : herm (Hpk k r') (y + y') (y + y') =
      herm (Hpk k r') y y + herm (Hpk k r') y' y + (herm (Hpk k r') y y' + herm (Hpk k r') y' y') := by
    rw [herm_add_left, herm_add_right, herm_add_right]
    ring
  have h2 : (herm (Hpk k r') y y').re = (herm (Hpk k r') y' y).re := by
    rw [← herm_conj _ (Hherm k r') y' y, Complex.conj_re]
  simp only [hb]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, h1, h2]
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    ring
end Formalism.FourierDecayAlt.P.B2x5
