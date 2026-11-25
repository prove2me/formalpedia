-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.IsInv.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:40.016296+00:00
-- url     : https://prove2.me/submissions/d5032e8f-9973-4da1-b79d-26123b298ad6

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsBump_cpt
import Theorems.Thm_CompanionTheory_D_gk_Poul_isSm_avg
import Theorems.Thm_CompanionTheory_D_gk_Poul_exists_avg_ne
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_continuous
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_map_avg
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_exists_bd
import Theorems.Thm_CompanionTheory_D_gk_Poul_exists_riesz
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsInv_swap
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsInv_left
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}
variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {W : ι → List (Mat n)} {W' : ι' → List (Mat n)} {C : ℝ}
  {B : H → H' → ℂ}
namespace CompanionTheory.D.gk.Poul
namespace IsInv
theorem _root_.solution [(haar : Measure (MG G hG)).IsInvInvariant] (θ : Mat n →L[ℝ] Mat n)
    (hθ : ∀ x ∈ G, θ x = x⁻¹) (hB : IsInv G σ σ' W W' C B) (h : RepOn G σ) (h' : RepOn G σ')
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hc' : ∀ v, ContinuousOn (fun g => σ' g v) G)
    (hW : ∀ i, LieW G (W i)) (hW' : ∀ j, LieW G (W' j)) [Nontrivial H'] :
    ∃ y₀ z₀, IsSm G σ' y₀ ∧ y₀ ≠ 0 ∧ ∀ x, IsSm G σ x → B x y₀ = ⟪z₀, x⟫_ℂ := by
  obtain ⟨u, hu⟩ := exists_ne (0 : H')
  obtain ⟨φ₁, hφ₁, hy₁⟩ := exists_avg_ne hG θ hθ h' hc' hu
  have hs₁ := isSm_avg (hG := hG) h' hc' hφ₁ u
  set y₁ := avg hG φ₁ σ' u
  obtain ⟨φ, hφ, hy₀⟩ := exists_avg_ne hG θ hθ h' hc' hy₁
  have hs₀ := isSm_avg (hG := hG) h' hc' hφ y₁
  obtain ⟨D, hD⟩ := (hB.left hs₁).exists_bd (hG := hG) h hiso hW hφ.smooth hφ.cpt
  have key : ∀ x, IsSm G σ x → B x (avg hG φ σ' y₁) = ∫ g : MG G hG, φ g.mat • B (σ g.mat x) y₁ ∂haar := by
    intro x hx
    have h1 := (hB.swap.left hx).map_avg h' hW' hs₁ hφ.smooth.continuous hφ.cpt hs₀
    have h2 := congrArg star h1
    rw [star_star] at h2
    rw [h2, ← integral_inv_eq_self (fun g : MG G hG => φ g.mat • B (σ g.mat x) y₁), Complex.star_def,
      ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have e : B x (σ' g.mat y₁) = B (σ (g⁻¹).mat x) y₁ := by
      rw [← hB.inv _ g.mem _ _ (hx.apply h (g⁻¹).mem) hs₁, ← h.apply_mul g.mem (g⁻¹).mem, ← MG.mat_mul,
        mul_inv_cancel]
      show _ = B (σ 1 x) _
      rw [h.map_one]; rfl
    simp only [e, MG.mat_inv, hφ.symm _ g.mem, Complex.real_smul, map_mul, Complex.conj_ofReal,
      Complex.conj_conj]
  obtain ⟨z₀, hz₀⟩ := exists_riesz (G := G) (σ := σ) (l := fun x => B x (avg hG φ σ' y₁)) (hB.left hs₀).add
    (hB.left hs₀).smul (D := D) fun x hx => by rw [key x hx]; exact hD x hx
  exact ⟨_, z₀, hs₀, hy₀, hz₀⟩
end IsInv
end CompanionTheory.D.gk.Poul
