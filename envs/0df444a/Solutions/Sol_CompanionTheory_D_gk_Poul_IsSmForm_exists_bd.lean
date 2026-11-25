-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.IsSmForm.exists_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:05:21.902143+00:00
-- url     : https://prove2.me/submissions/013ab4a5-5bfb-4d3a-96ed-9bd06f77731e

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_continuous
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_avg_bd
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_norm_integral_dsW_le
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
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
variable {ι : Type} [Fintype ι] {W : ι → List (Mat n)} {C : ℝ} {l : H → ℂ}
namespace CompanionTheory.D.gk.Poul
namespace IsSmForm
theorem _root_.solution (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hW : ∀ i, LieW G (W i)) {φ : Mat n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ D : ℝ, ∀ v, IsSm G σ v → ‖∫ g : MG G hG, φ g.mat • l (σ g.mat v) ∂haar‖ ≤ D * ‖v‖ := by
  refine ⟨|C| * ∑ i, ∫ g : MG G hG, ‖LW (W i) φ g.mat‖ ∂haar, fun v hv => ?_⟩
  have h1 := hl.avg_bd (hG := hG) h hW hv hφ.continuous hc IsSm.zero
  have h0 : l 0 = 0 := by simpa using hl.smul 0 0 IsSm.zero
  have h0' : ∀ i, dsW σ (W i) 0 = 0 := fun i => by
    simpa using dsW_smul h (IsSm.zero (G := G) (σ := σ)) 0 (hW i)
  simp only [h0, h0', sub_zero] at h1
  refine h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).trans ?_)
  rw [mul_assoc, Finset.sum_mul]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => norm_integral_dsW_le h hiso hv hφ hc (hW i))
    (abs_nonneg _)
end IsSmForm
end CompanionTheory.D.gk.Poul
