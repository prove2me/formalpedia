-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.IsSmForm.continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:01:22.229817+00:00
-- url     : https://prove2.me/submissions/865d437e-fa5e-4f63-9cdd-50f35d716bf1

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_sub
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_sub
import Theorems.Thm_CompanionTheory_D_Upq_Sm_continuous_orbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_sub
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
omit [CompleteSpace H]
namespace CompanionTheory.D.gk.Poul
namespace IsSmForm
theorem _root_.solution (hl : IsSmForm G σ W C l) (h : RepOn G σ) (hW : ∀ i, LieW G (W i)) {v : H}
    (hv : IsSm G σ v) : Continuous fun g : MG G hG => l (σ g.mat v) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun g : MG G hG => C * ∑ i, ‖dsW σ (W i) (σ g.mat v) - dsW σ (W i) (σ g₀.mat v)‖ :=
    continuous_const.mul (continuous_finsetSum _ fun i _ => ((continuous_orbit h hv (hW i)).sub continuous_const).norm)
  have ht := hc.tendsto g₀
  simp only [sub_self, norm_zero, Finset.sum_const_zero, mul_zero] at ht
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => ?_) ht
  rw [← hl.sub (hv.apply h g.mem) (hv.apply h g₀.mem)]
  refine (hl.bd _ ((hv.apply h g.mem).sub (hv.apply h g₀.mem))).trans (le_of_eq ?_)
  simp only [dsW_sub h (hv.apply h g.mem) (hv.apply h g₀.mem) (hW _)]
end IsSmForm
end CompanionTheory.D.gk.Poul
