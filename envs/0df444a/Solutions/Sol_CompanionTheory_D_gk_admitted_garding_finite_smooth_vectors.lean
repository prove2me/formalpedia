-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.garding_finite_smooth_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:41:59.784692+00:00
-- url     : https://prove2.me/submissions/6a271893-80ad-4f17-a5b9-48a3d5523ec4

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingAvg
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_toM_mul
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_toM_one
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_emb_toM
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_toM_mem
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_toM
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_inUJ_of_mem_Kset
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_toM_inv_of_unitary
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_avg
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_T_comm
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_apply_alt
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_eq_zero_of_alt_alt
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_bump
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_nhds_close
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_preimage
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_strictHenselian_absolutely_closed_local_ring
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Gard
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution : GardingFin := by
  intro n ε H _ _ _ σ hσ Y _ hY v hv
  obtain ⟨⟨h1, hm⟩, hiso, hcont⟩ := hσ
  let ρ : UJ ε → H →L[ℂ] H := fun x => σ (toM x)
  have hρ : ∀ u, Continuous fun x => ρ x u := fun u =>
    (hcont u).comp_continuous emb_toM.continuous toM_mem
  have hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u) := fun x y u => by
    simp only [ρ, toM_mul, hm _ (toM_mem x) _ (toM_mem y), ContinuousLinearMap.comp_apply]
  have hρ1 : ∀ u, ρ 1 u = u := fun u => by simp only [ρ, toM_one, h1, one_apply_eq_self]
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close ρ hρ hρ1 Y
  have hVi : V⁻¹ ∈ 𝓝 (1 : UJ ε) := inv_mem_nhds_one _ hV
  rw [emb_toM.isInducing.nhds_eq_comap, mem_comap] at hVi
  obtain ⟨W, hW, hWV⟩ := hVi
  have hD : {y : Matrix (Fin n) (Fin n) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, hfk⟩ := exists_bump (inter_mem hW hD)
  let w : UJ ε → ℝ := fun x => f (toM x⁻¹)
  have hw : Continuous w := hf.continuous.comp (emb_toM.continuous.comp continuous_inv)
  have hc : HasCompactSupport w := by
    refine HasCompactSupport.intro (emb_toM.isCompact_preimage hS).inv fun x hx => ?_
    by_contra h
    exact hx (hfS _ h)
  have h0 : 0 ≤ w := fun x => hf0 _
  have hw1 : w 1 ≠ 0 := by simpa only [w, inv_one, toM_one] using hf1
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring (muG ε) ρ hρ (fun x u => hiso _ (toM_mem x) u) hw hc
  have hTK : ∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    obtain ⟨k', rfl⟩ := exists_toM (inUJ_of_mem_Kset hk)
    rw [hT, hT]
    refine T_comm (muG ε) ρ hρ hmul hw hc h0 hw1 k' (fun x => ?_) u
    simp only [w, _root_.mul_inv_rev, inv_inv]
    rw [← mul_assoc, toM_mul, toM_mul, toM_inv_of_unitary hk.1, hfk _ hk.1]
  have hinj : ∀ y ∈ Y, T y = 0 → y = 0 := by
    intro y hy hTy
    rw [hT] at hTy
    refine eq_zero_of_alt_alt (muG ε) ρ hρ hw hc h0 hw1 y (fun x hx => hclose x ?_ y hy) hTy
    have : x⁻¹ ∈ V⁻¹ := hWV (hSW (hfS _ hx)).1
    simpa using this
  obtain ⟨u, rfl⟩ := exists_preimage Y T (hY T hTK) hinj v hv
  intro g₀ _
  refine ⟨univ, fun g => ∫ x : UJ ε, f (toM x⁻¹ * g) • ρ x u ∂(muG ε), isOpen_univ, mem_univ _,
    (contDiff_avg (fun x => ρ x u) (hρ u) hf hS (fun B hB => (hSW hB).2) hfS).contDiffOn, fun g _ hg => ?_⟩
  obtain ⟨g', rfl⟩ := exists_toM (ε := ε) hg
  show ρ g' (T u) = _
  rw [hT, apply_alt (muG ε) ρ hρ hmul hw hc]
  simp only [w, _root_.mul_inv_rev, inv_inv, toM_mul]
end CompanionTheory.D.gk.admitted
