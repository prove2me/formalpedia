-- Prove2me | solution 1 for Formalism.L2.LamCM.hadamard_local_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:42:53.04736+00:00
-- url     : https://prove2.me/submissions/4aed604f-dab9-49b3-a4f4-fb73d4ffcee9

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne
import Theorems.Thm_Formalism_L2_LamCM_prod_span_le_of_loc
import Theorems.Thm_Formalism_L2_LamCM_hadamard_of_le

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
theorem _root_.solution : HadamardLoc0 := by
  intro K _ _ g abelian₂ ℓ U H La hLam hℓ hdet hLa hH hn hloc hsq
  have hle := prod_span_le_of_loc abelian₂ ℓ U.det hLam (fun j => (hℓ j).1) hdet hloc
  exact hadamard_of_le g abelian₂ ℓ U H La hLam hℓ hdet hLa hH hn hle hsq
end Formalism.L2.LamCM
