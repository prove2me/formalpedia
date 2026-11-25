-- Prove2me | solution 1 for Deduction.lemmaL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:50:19.799647+00:00
-- url     : https://prove2.me/submissions/6177a804-5d54-49e9-a51b-1484fe5c0556

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_poleData
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauWindow
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_WindowHypUOfWindowHyp
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_CharFamilyLFunctionNeZeroOfOneLeRe
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_lemmaL
import Theorems.Thm_Deduction_charFamily_LFunction_ne_zero_of_one_le_re
import Theorems.Thm_Deduction_landau_window
import Theorems.Thm_Deduction_poleData
import Theorems.Thm_Deduction_windowHypU_of_windowHyp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (F : CharFamily) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    ZeroFree F θ := by
  intro i s hs hzero
  obtain ⟨Φ, hP⟩ := poleData F
  have hZ := landau_window hP hθ hθ1 hδ (windowHypU_of_windowHyp F hδ h)
  by_cases h1 : 1 ≤ s.re
  · exact charFamily_LFunction_ne_zero_of_one_le_re F i s h1 hzero
  · have hmem : s ∈ zeroSet F := ⟨by linarith, i, Or.inl hzero⟩
    have := hZ s hmem
    linarith
end Deduction
