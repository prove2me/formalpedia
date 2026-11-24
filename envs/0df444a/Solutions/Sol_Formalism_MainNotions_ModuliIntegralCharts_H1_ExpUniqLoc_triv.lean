-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:37.675904+00:00
-- url     : https://prove2.me/submissions/b6e0bbf1-0fc4-4872-a198-42509bc864bd

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_comp_sum
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_comp_cpy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_comp_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_ker_aug_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_one_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_uniq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_coord
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_top_step
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_mem_pow_of_trunc_eq_zero
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
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
theorem _root_.solution [Algebra ℚ R] {d : ℕ} (δ : ∀ m, sp (R₀ := R) (Jet R (Fin 1 × Fin d) m) ⟶ G)
    (htr : ∀ m, spMap (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] Jet R (Fin 1 × Fin d) m) ≫ δ (m + 1) = δ m)
    (hhom : ∀ m, spMap (sumJ d m) ≫ δ m = (spMap (cpy d m 0) ≫ δ m) * (spMap (cpy d m 1) ≫ δ m))
    (h1 : δ 1 = 1) : ∀ m, δ m = 1 := by
  have hu : ∀ m, spMap (jetAug : Jet R (Fin 1 × Fin d) m →ₐ[R] R) ≫ δ m = 1 := by
    intro m
    have e := congrArg (fun f => spMap (jetAug : Jet R (Fin 2 × Fin d) m →ₐ[R] R) ≫ f) (hhom m)
    simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, aug_comp_sum, aug_comp_cpy] at e
    exact _root_.mul_eq_left.1 e.symm
  have step : ∀ m, δ (m + 1) = 1 := by
    intro m
    induction m with
    | zero => exact h1
    | succ m ih =>
      obtain ⟨ψ, hψa, hψ⟩ := coord hx (jetAug : Jet R (Fin 1 × Fin d) (m + 1 + 1) →ₐ[R] R) (m + 1 + 1)
        (ker_aug_pow le_rfl) (δ (m + 1 + 1)) (hu _)
      have ht : (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1 + 1) →ₐ[R] Jet R (Fin 1 × Fin d) (m + 1)).comp ψ =
          (Algebra.ofId R _).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) (m + 1 + 1)) := by
        refine uniq hx (jetAug : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] R) (m + 1 + 1) (ker_aug_pow (by omega)) ?_ ?_ ?_
        · rw [← AlgHom.comp_assoc, aug_comp_trunc, hψa]
        · exact AlgHom.ext fun a => by simp
        · rw [← spMap_comp, Category.assoc, ← hψ, htr, ih, one_eq hx]
      have hz : ∀ j, ψ (zR (m + 1 + 1) j) ∈ Ij R (Fin 1 × Fin d) (m + 1 + 1) ^ (m + 1 + 1) := fun j => by
        apply mem_pow_of_trunc_eq_zero
        have := DFunLike.congr_fun ht (zR (m + 1 + 1) j)
        rw [AlgHom.comp_apply, AlgHom.comp_apply, ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zR, map_zero] at this
        exact this
      have h0 := top_step hx (by omega) ψ hψa hz (by rw [← hψ]; exact hhom _)
      have hψ0 : ψ = (Algebra.ofId R _).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) (m + 1 + 1)) :=
        ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by
          rw [h0 j, AlgHom.comp_apply, ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zR, map_zero]
      rw [hψ, hψ0, one_eq hx]
  intro m
  cases m with
  | zero => rw [← htr 0, step 0, comp_one']
  | succ m => exact step m
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
