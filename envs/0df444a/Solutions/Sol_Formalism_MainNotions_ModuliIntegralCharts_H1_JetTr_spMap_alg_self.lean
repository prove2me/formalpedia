-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.spMap_alg_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:57:24.793112+00:00
-- url     : https://prove2.me/submissions/9621f6e2-d105-4ec0-91c5-2ab1c260ca79

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrC
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_JetTr_spMap_id__32fc6f0130a5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
theorem _root_.solution (R : Type) [CommRing R] : spMap (algebraMap R R) = 𝟙 (Sp R) := by
  first
  | exact spMap_id' R
  | (rw [Algebra.algebraMap_self]; exact spMap_id' R)
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
