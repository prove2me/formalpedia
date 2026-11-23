-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.jetAug_psJet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:18.632672+00:00
-- url     : https://prove2.me/submissions/bc425608-0848-42c2-b6c6-b3689d4aa2b3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_coeff_psTrunc


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {R ι : Type} [CommRing R]
variable [Fintype ι] [DecidableEq ι]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution (m : ℕ) (f : MvPowerSeries ι R) :
    jetAug (psJet m f) = MvPowerSeries.constantCoeff f := by
  show (MvPolynomial.aeval fun _ => (0 : R)) (psTrunc m f) = _
  rw [show (fun _ : ι => (0 : R)) = 0 from rfl, MvPolynomial.aeval_zero, Algebra.algebraMap_self_apply,
]
  show MvPolynomial.coeff 0 (psTrunc m f) = _
  rw [GermFun.coeff_psTrunc m f 0 (by simp)]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
