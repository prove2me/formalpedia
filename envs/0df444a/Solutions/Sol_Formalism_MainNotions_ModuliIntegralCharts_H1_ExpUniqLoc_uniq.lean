-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.uniq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:52.070296+00:00
-- url     : https://prove2.me/submissions/367909a1-2448-4922-9acf-bc7412ffcf4a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_augOne
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
theorem _root_.solution {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ) (hk : RingHom.ker aug ^ (m + 1) = ⊥)
    {ψ₁ ψ₂ : JetR R (Fin n) m →ₐ[R] A} (h1 : aug.comp ψ₁ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) m)
    (h2 : aug.comp ψ₂ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) m) (e : spMap ψ₁ ≫ x m = spMap ψ₂ ≫ x m) :
    ψ₁ = ψ₂ := by
  have hy : spMap aug ≫ (spMap ψ₁ ≫ x m) = 1 := by
    rw [← Category.assoc, spMap_comp, h1, augOne hx]
  exact (hx.2.2 A aug m hk _ hy).unique ⟨h1, rfl⟩ ⟨h2, e⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
