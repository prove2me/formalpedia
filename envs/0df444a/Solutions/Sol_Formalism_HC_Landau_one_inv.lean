-- Prove2me | solution 1 for Formalism.HC.Landau.one_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:56.181058+00:00
-- url     : https://prove2.me/submissions/11b22183-5715-4699-92e2-85ae2a5d7685

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_HC_Landau_eq_one_of_chi

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
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
namespace Formalism.HC.Landau
theorem _root_.solution : PChar.one.inv = PChar.one := eq_one_of_chi (inv_one (G := DirichletCharacter ℂ 1))
end Formalism.HC.Landau
