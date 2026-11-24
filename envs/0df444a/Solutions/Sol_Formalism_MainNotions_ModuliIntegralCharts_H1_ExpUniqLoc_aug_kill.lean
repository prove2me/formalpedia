-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.aug_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:53.485246+00:00
-- url     : https://prove2.me/submissions/24392eae-c7d5-45bf-8cc6-8253277d0adb

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_augmentation_jet_variable
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_kill_alt_alt
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
variable {n : ℕ}
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}
  (hx : IsUnivChart G n x)
include hx
omit hx
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
theorem _root_.solution (M : ℕ) (i : Fin 2) :
    (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R).comp (kill M i) = jetAug :=
  jet_ext' fun v => by
    rw [AlgHom.comp_apply, kill_alt_alt]
    split_ifs
    · rw [map_zero, augmentation_jet_variable]
    · rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
