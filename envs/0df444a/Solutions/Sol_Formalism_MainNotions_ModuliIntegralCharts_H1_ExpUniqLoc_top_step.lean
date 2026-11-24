-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc.top_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:43.270929+00:00
-- url     : https://prove2.me/submissions/5e148210-bd61-467c-8fd5-9a6be9ba82aa

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_copy_jet_variable
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_diag_cpy_apply
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_diag_sum_apply
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_comp_sum
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_comp_cpy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_ker_aug_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_cpyU_zR
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_uniq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_law
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_Ij_pow_eq_bot
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_augmentation_jet_variable
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_eq_zero_of_mem_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_map_pow_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_sc_pow_mem
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_jet_ext__4fc5f26daf9f
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
theorem _root_.solution [Algebra ℚ R] {d M : ℕ} (hM : 2 ≤ M) (ψ : JetR R (Fin n) M →ₐ[R] Jet R (Fin 1 × Fin d) M)
    (hψa : (jetAug : Jet R (Fin 1 × Fin d) M →ₐ[R] R).comp ψ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) M)
    (hψ : ∀ j, ψ (zR M j) ∈ Ij R (Fin 1 × Fin d) M ^ M)
    (hhom : spMap (sumJ d M) ≫ (spMap ψ ≫ x M) =
      (spMap (cpy d M 0) ≫ spMap ψ ≫ x M) * (spMap (cpy d M 1) ≫ spMap ψ ≫ x M)) :
    ∀ j, ψ (zR M j) = 0 := by
  obtain ⟨Φ, hΦa, hΦ, hE⟩ := law hx M
  have hb : ∀ v : Fin 2 × Fin n, cpy d M v.1 (ψ (zR M v.2)) ∈ Ij R (Fin 2 × Fin d) M ^ M := fun v =>
    map_pow_mem _ (fun p => by rw [copy_jet_variable]; exact Ideal.subset_span ⟨_, rfl⟩) M (hψ v.2)
  obtain ⟨ev, hev⟩ : ∃ ev : Jet R (Fin 2 × Fin n) M →ₐ[R] Jet R (Fin 2 × Fin d) M,
      ∀ v, ev (zz M v) = cpy d M v.1 (ψ (zR M v.2)) := by
    refine ⟨liftJet (aeval fun v : Fin 2 × Fin n => cpy d M v.1 (ψ (zR M v.2))) ?_, fun v => ?_⟩
    · rw [← le_bot_iff, ← Ij_pow_eq_bot (R := R) (Fin 2 × Fin d) M]
      refine Ideal.pow_right_mono ?_ _
      rw [Ideal.span_le]
      rintro _ ⟨v, rfl⟩
      simp only [SetLike.mem_coe, aeval_X]
      exact Ideal.pow_le_self (by omega) (hb v)
    · show aeval _ (X v) = _
      rw [aeval_X]
  have ev_cpy : ∀ i, ev.comp (cpyU M i) = (cpy d M i).comp ψ := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by rw [AlgHom.comp_apply, cpyU_zR, hev, AlgHom.comp_apply]
  have haug2 : (jetAug : Jet R (Fin 2 × Fin d) M →ₐ[R] R).comp ev = jetAug := jet_ext' fun v => by
    have h1 := DFunLike.congr_fun (aug_comp_cpy (R := R) d M v.1) (ψ (zR M v.2))
    have h2 := DFunLike.congr_fun hψa (zR M v.2)
    rw [AlgHom.comp_apply] at h1 h2
    rw [AlgHom.comp_apply, hev, augmentation_jet_variable, h1, h2, ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zR]
  have hsum : (sumJ d M).comp ψ = ev.comp Φ := by
    refine uniq hx (jetAug : Jet R (Fin 2 × Fin d) M →ₐ[R] R) M (ker_aug_pow le_rfl) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, aug_comp_sum, hψa]
    · rw [← AlgHom.comp_assoc, haug2, hΦa]
    · calc spMap ((sumJ d M).comp ψ) ≫ x M = spMap (sumJ d M) ≫ (spMap ψ ≫ x M) := by
            rw [← spMap_comp, Category.assoc]
        _ = (spMap ((cpy d M 0).comp ψ) ≫ x M) * (spMap ((cpy d M 1).comp ψ) ≫ x M) := by
            rw [hhom, ← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc]
        _ = (spMap (ev.comp (cpyU M 0)) ≫ x M) * (spMap (ev.comp (cpyU M 1)) ≫ x M) := by
            rw [ev_cpy, ev_cpy]
        _ = spMap ev ≫ ((spMap (cpyU M 0) ≫ x M) * (spMap (cpyU M 1) ≫ x M)) := by
            rw [MonObj.comp_mul, ← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc]
        _ = spMap (ev.comp Φ) ≫ x M := by rw [hΦ, ← spMap_comp, Category.assoc]
  intro j
  have hmap : ∀ i, Ideal.map ev (Kp M i) ≤ Ij R (Fin 2 × Fin d) M ^ M := fun i => by
    rw [Kp, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j', rfl⟩, rfl⟩
    rw [SetLike.mem_coe, hev]
    exact hb (i, j')
  have hevE : ev (Φ (zR M j) - zz M ((0 : Fin 2), j) - zz M ((1 : Fin 2), j)) = 0 := by
    apply eq_zero_of_mem_pow (k := M + M) (by omega)
    have := Ideal.mem_map_of_mem ev (hE j)
    rw [Ideal.map_mul] at this
    rw [pow_add (Ij R (Fin 2 × Fin d) M) M M]
    exact Ideal.mul_mono (hmap 0) (hmap 1) this
  have hadd : sumJ d M (ψ (zR M j)) = cpy d M 0 (ψ (zR M j)) + cpy d M 1 (ψ (zR M j)) := by
    have e1 := DFunLike.congr_fun hsum (zR M j)
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at e1
    have e2 : ev (Φ (zR M j)) = ev (Φ (zR M j) - zz M ((0 : Fin 2), j) - zz M ((1 : Fin 2), j)) +
        ev (zz M ((0 : Fin 2), j)) + ev (zz M ((1 : Fin 2), j)) := by
      rw [map_sub, map_sub]; abel
    rw [e1, e2, hevE, zero_add, hev, hev]
  have h2 : sc M 2 (ψ (zR M j)) = (2 : R) • ψ (zR M j) := by
    rw [← diag_sum_apply, hadd, map_add, diag_cpy_apply, diag_cpy_apply, two_smul]
  have h3 : sc M 2 (ψ (zR M j)) = (2 : R) ^ M • ψ (zR M j) :=
    sub_eq_zero.1 (eq_zero_of_mem_pow le_rfl (sc_pow_mem (R := R) (κ := Fin 1 × Fin d) M 2 M (hψ j)))
  have h4 : ((2 : R) ^ M - 2) • ψ (zR M j) = 0 := by rw [sub_smul, ← h3, ← h2, sub_self]
  have hu : IsUnit ((2 : R) ^ M - 2) := by
    have hq : ((2 : ℚ) ^ M - 2) ≠ 0 := by
      have : (4 : ℚ) ≤ 2 ^ M := by
        calc (4 : ℚ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
      linarith
    have := (isUnit_iff_ne_zero.2 hq).map (algebraMap ℚ R)
    rwa [map_sub, map_pow, map_ofNat] at this
  exact (hu.smul_eq_zero).1 h4
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
