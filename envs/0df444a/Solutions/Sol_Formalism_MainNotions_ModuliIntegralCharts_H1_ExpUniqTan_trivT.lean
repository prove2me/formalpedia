-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan.trivT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:18:48.911902+00:00
-- url     : https://prove2.me/submissions/ee40923e-11d0-4fa5-a3b8-71c983405114

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqTan
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqTan_one_of_tan
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_comp_cpy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_comp_sum
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_fin_one_pair_eq_local
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_triv
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
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}
  (hx : IsUnivChart G n x)
include hx
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
theorem _root_.solution [Algebra ℚ R] {d : ℕ} (δ : ∀ m, sp (R₀ := R) (Jet R (Fin 1 × Fin d) m) ⟶ G)
    (htr : ∀ m, spMap (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] Jet R (Fin 1 × Fin d) m) ≫ δ (m + 1) = δ m)
    (hhom : ∀ m, spMap (sumJ d m) ≫ δ m = (spMap (cpy d m 0) ≫ δ m) * (spMap (cpy d m 1) ≫ δ m))
    (ht : ∀ j : Fin d, spMap (jetTan ((0 : Fin 1), j) : Jet R (Fin 1 × Fin d) (0 + 1) →ₐ[R] DualNumber R) ≫ δ 1 = 1) :
    ∀ m, δ m = 1 := by
  refine triv hx δ htr hhom ?_
  have hu : spMap (jetAug : Jet R (Fin 1 × Fin d) 1 →ₐ[R] R) ≫ δ 1 = 1 := by
    have e := congrArg (fun f => spMap (jetAug : Jet R (Fin 2 × Fin d) 1 →ₐ[R] R) ≫ f) (hhom 1)
    simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, aug_comp_sum, aug_comp_cpy] at e
    exact _root_.mul_eq_left.1 e.symm
  refine one_of_tan hx (δ 1) hu fun ℓ => ?_
  have hℓ : ℓ = ((0 : Fin 1), ℓ.2) := (fin_one_pair_eq_local d ℓ).symm
  rw [hℓ]
  exact ht ℓ.2
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqTan
