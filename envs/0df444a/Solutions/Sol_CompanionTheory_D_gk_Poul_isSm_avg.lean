-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.isSm_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:34:16.831555+00:00
-- url     : https://prove2.me/submissions/e0f9a56c-87fa-40af-bf10-02f631c77dcf

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsBump_cpt
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_of_contDiff
import Theorems.Thm_CompanionTheory_D_Upq_Sm_isCompact_supp
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_apply_alt
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_Phi
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_integral_comp
import Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_isCompact_mul_inv
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans
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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.gk.Poul
theorem _root_.solution (h : RepOn G σ) (hc : ∀ v, ContinuousOn (fun g => σ g v) G) {φ : Mat n → ℝ} (hφ : IsBump G φ)
    (u : H) : IsSm G σ (avg hG φ σ u) := by
  obtain ⟨S, hS, hd, hfS⟩ := hφ.supp
  have hρ : ∀ u, Continuous fun x : MG G hG => σ x.mat u := fun u =>
    (hc u).comp_continuous MG.continuous_mat fun g => g.mem
  have hq : Continuous fun x : MG G hG => ((x⁻¹).mat, σ x.mat u) :=
    (MG.continuous_mat.comp continuous_inv).prodMk (hρ u)
  have key := contDiff_integral_comp (haar : Measure (MG G hG)) _ (contDiff_Phi (H := H) hφ.smooth) _ hq fun g₀ => by
    refine ⟨Metric.closedBall g₀ 1, Metric.closedBall_mem_nhds _ one_pos, _,
      MG.isClosedEmbedding_mat.isCompact_preimage (isCompact_mul_inv (isCompact_closedBall g₀ 1) hS hd),
      fun g hg x hx => ?_⟩
    have : φ ((x⁻¹).mat * g) = 0 := by
      by_contra h0
      have hB := hfS _ h0
      refine hx ⟨(g, (x⁻¹).mat * g), ⟨hg, hB⟩, ?_⟩
      have hu : IsUnit ((x⁻¹).mat * g).det := isUnit_iff_ne_zero.2 (hd _ hB)
      have e : g = x.mat * ((x⁻¹).mat * g) := by
        rw [← Matrix.mul_assoc, ← MG.mat_mul, mul_inv_cancel]
        exact (Matrix.one_mul g).symm
      show g * ((x⁻¹).mat * g)⁻¹ = x.mat
      calc g * ((x⁻¹).mat * g)⁻¹ = x.mat * ((x⁻¹).mat * g) * ((x⁻¹).mat * g)⁻¹ := by rw [← e]
        _ = x.mat := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
    simp only [this, zero_smul]
  refine (SmOn.of_contDiff key).congr fun g hg => ?_
  have hw : Continuous fun x : MG G hG => φ x.mat := hφ.smooth.continuous.comp MG.continuous_mat
  have hcs : HasCompactSupport fun x : MG G hG => φ x.mat :=
    HasCompactSupport.intro (isCompact_supp hφ.cpt) fun x hx => image_eq_zero_of_notMem_tsupport hx
  have := apply_alt (haar : Measure (MG G hG)) (fun x : MG G hG => σ x.mat) hρ
    (fun x y u => h.apply_mul x.mem y.mem u) hw hcs (MG.mk hG g hg) u
  refine this.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
  show φ ((MG.mk hG g hg)⁻¹ * x).mat • _ = φ ((x⁻¹).mat * (MG.mk hG g hg).mat) • _
  rw [← hφ.symm _ (MG.mem _), ← MG.mat_inv, _root_.mul_inv_rev, inv_inv, MG.mat_mul]
end CompanionTheory.D.gk.Poul
