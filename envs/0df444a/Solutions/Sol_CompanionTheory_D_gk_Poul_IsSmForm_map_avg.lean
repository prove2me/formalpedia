-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.IsSmForm.map_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:10.045636+00:00
-- url     : https://prove2.me/submissions/1847fc04-be26-4d7f-afc7-173b76d19830

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_gk_Poul_dsW_avg
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_avg_bd
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
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
variable {ι : Type} [Fintype ι] {W : ι → List (Mat n)} {C : ℝ} {l : H → ℂ}
namespace CompanionTheory.D.gk.Poul
namespace IsSmForm
theorem _root_.solution (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hW : ∀ i, LieW G (W i)) {v : H}
    (hv : IsSm G σ v) {φ : Mat n → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : IsSm G σ (avg hG φ σ v)) : l (avg hG φ σ v) = ∫ g : MG G hG, φ g.mat • l (σ g.mat v) ∂haar := by
  have := hl.avg_bd (hG := hG) h hW hv hφ hc hs
  simp only [dsW_avg h hv hφ hc (hW _), sub_self, norm_zero, Finset.sum_const_zero, mul_zero, norm_le_zero_iff,
    sub_eq_zero] at this
  exact this.symm
end IsSmForm
end CompanionTheory.D.gk.Poul
