-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.ker_fst_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:52.526836+00:00
-- url     : https://prove2.me/submissions/2b0cc373-b3f4-47b4-9cae-2b52407b19f3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqTan
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
theorem _root_.solution : RingHom.ker (fstA (R := R)) ^ (1 + 1) = ⊥ := by
  have e : RingHom.ker (fstA (R := R)) ^ (1 + 1) = RingHom.ker (fstA (R := R)) * RingHom.ker (fstA (R := R)) := by
    first | exact pow_two _ | rw [pow_succ, pow_one]
  rw [e, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  rw [Ideal.mem_bot]
  have hr' : r.fst = 0 := by simpa [fstA] using hr
  have hs' : s.fst = 0 := by simpa [fstA] using hs
  first | (ext <;> simp [hr', hs']) | exact TrivSqZeroExt.ext (by simp [hr', hs']) (by simp [hr', hs'])
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
