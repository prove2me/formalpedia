-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.diag_cpy_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:54.14216+00:00
-- url     : https://prove2.me/submissions/02a331d9-a79d-47d0-9c4f-33fab84bd4b3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_diag_alt_alt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_copy_jet_variable
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_fin_one_pair_eq_local
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_jet_ext__4fc5f26daf9f
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable (d : ℕ)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
theorem _root_.solution (M : ℕ) (i : Fin 2) (a : Jet R (Fin 1 × Fin d) M) : diag d M (cpy d M i a) = a := by
  have : (diag (R := R) d M).comp (cpy d M i) = AlgHom.id R _ :=
    jet_ext' fun p => by rw [AlgHom.comp_apply, copy_jet_variable, diag_alt_alt, fin_one_pair_eq_local]; rfl
  exact DFunLike.congr_fun this a
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
