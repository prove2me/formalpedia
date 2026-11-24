-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:36:39.842318+00:00
-- url     : https://prove2.me/submissions/bc665eaf-0b1f-457d-b0c4-74563b02bb89

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_ker_aug_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_cpyU_zR
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_augOne
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_one_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_uniq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_coord
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_cpyU
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_kill
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_kill_alt_alt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_mem_mul_of_kill
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
theorem _root_.solution (M : ℕ) : ∃ Φ : JetR R (Fin n) M →ₐ[R] Jet R (Fin 2 × Fin n) M,
    (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R).comp Φ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) M ∧
    (spMap (cpyU M 0) ≫ x M) * (spMap (cpyU M 1) ≫ x M) = spMap Φ ≫ x M ∧
    ∀ j, Φ (zR M j) - zz M ((0 : Fin 2), j) - zz M ((1 : Fin 2), j) ∈ Kp M 0 * Kp M 1 := by
  have hkk : RingHom.ker (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R) ^ (M + 1) = ⊥ := ker_aug_pow le_rfl
  have hone : ∀ i, spMap (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R) ≫ (spMap (cpyU M i) ≫ x M) = 1 := fun i => by
    rw [← Category.assoc, spMap_comp, aug_cpyU hx, augOne hx]
  have hP : spMap (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R) ≫
      ((spMap (cpyU M 0) ≫ x M) * (spMap (cpyU M 1) ≫ x M)) = 1 := by
    rw [MonObj.comp_mul, hone, hone, _root_.mul_one]
  obtain ⟨Φ, hΦa, hΦ⟩ := coord hx _ M hkk _ hP
  have e0 : (kill M 1).comp (cpyU M 0) = cpyU (R := R) (n := n) M 0 := ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by
    rw [AlgHom.comp_apply, cpyU_zR, kill_alt_alt, if_neg (by simp)]
  have e1 : (kill M 0).comp (cpyU M 1) = cpyU (R := R) (n := n) M 1 := ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by
    rw [AlgHom.comp_apply, cpyU_zR, kill_alt_alt, if_neg (by simp)]
  have z0 : ∀ i : Fin 2, (kill (R := R) (n := n) M i).comp (cpyU (R := R) (n := n) M i) =
      (Algebra.ofId R _).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) M) := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by
      rw [AlgHom.comp_apply, cpyU_zR, kill_alt_alt, if_pos rfl, AlgHom.comp_apply, ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zR, map_zero]
  have hk : ∀ i i' : Fin 2, (kill (R := R) (n := n) M i).comp (cpyU (R := R) (n := n) M i') = cpyU M i' →
      spMap (kill (R := R) (n := n) M i) ≫ ((spMap (cpyU (R := R) (n := n) M 0) ≫ x M) *
        (spMap (cpyU (R := R) (n := n) M 1) ≫ x M)) = spMap (cpyU (R := R) (n := n) M i') ≫ x M →
      (kill (R := R) (n := n) M i).comp Φ = cpyU M i' := by
    intro i i' _ hprod
    refine uniq hx (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R) M hkk ?_ (aug_cpyU hx M i') ?_
    · rw [← AlgHom.comp_assoc, aug_kill, hΦa]
    · rw [← spMap_comp, Category.assoc, ← hΦ, hprod]
  have k1 : (kill M 1).comp Φ = cpyU M 0 := hk 1 0 e0 (by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, e0, z0, one_eq hx, _root_.mul_one])
  have k0 : (kill M 0).comp Φ = cpyU M 1 := hk 0 1 e1 (by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, e1, z0, one_eq hx, _root_.one_mul])
  refine ⟨Φ, hΦa, hΦ, fun j => mem_mul_of_kill M _ ?_ ?_⟩
  · have h := DFunLike.congr_fun k0 (zR M j)
    rw [AlgHom.comp_apply, cpyU_zR] at h
    rw [map_sub, map_sub, h, kill_alt_alt, kill_alt_alt, if_pos rfl, if_neg (by simp), sub_zero, sub_self]
  · have h := DFunLike.congr_fun k1 (zR M j)
    rw [AlgHom.comp_apply, cpyU_zR] at h
    rw [map_sub, map_sub, h, kill_alt_alt, kill_alt_alt, if_neg (by simp), if_pos rfl, sub_zero, sub_self]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
