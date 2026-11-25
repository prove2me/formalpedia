-- Prove2me | solution 1 for Formalism.L2.LamCM.key_formula_link
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:16:36.383875+00:00
-- url     : https://prove2.me/submissions/bad35c1b-85cd-440b-8667-cd8990be0ce9

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
namespace Formalism.L2.LamCM
theorem _root_.solution : KeyCoreLink := by
  intro h
  obtain ⟨κ, h1, h2, h3, h4⟩ := h
  refine ⟨κ, h1, h2, ?_, h4.2⟩
  intro R K _ _ _ _ _ _ _ x xK hpb
  obtain ⟨u, hu, -⟩ := h3 R K x xK hpb
  exact ⟨u, hu⟩
end Formalism.L2.LamCM
