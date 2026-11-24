-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrc_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:45:13.193906+00:00
-- url     : https://prove2.me/submissions/60322a19-7258-4e08-98bc-e5523cfcde5c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_intOn
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_exists_vec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_tendsto_vec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {π : G → (H →L[ℂ] H)}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [TopologicalSpace.SeparableSpace H] (hmul : ∀ g h, π (g * h) = π g ∘L π h) (hone : π 1 = 1)
    (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ) :
    (rrc_C π)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_orthogonal] at hu
  have hz : ∀ v, (fun g => ⟪π g v, u⟫_ℂ) =ᵐ[μ] 0 := by
    intro v
    apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    · rw [locallyIntegrable_iff]
      intro k hk
      exact rrc_intOn hn hm hk.measure_lt_top v u
    · intro k hk
      obtain ⟨w, hw⟩ := rrc_exists_vec hn hm hk.measure_lt_top v
      rw [← hw u]
      exact hu w (rrc_tendsto_vec hmul hone hn hm hk hw)
  have hall : ∀ᵐ g ∂μ, ∀ n, ⟪π g (TopologicalSpace.denseSeq H n), u⟫_ℂ = 0 := ae_all_iff.2 fun n => hz _
  obtain ⟨g, hg⟩ := hall.exists
  have hfun : (fun v => ⟪π g v, u⟫_ℂ) = fun _ => 0 :=
    (TopologicalSpace.denseRange_denseSeq H).equalizer ((π g).continuous.inner continuous_const) continuous_const
      (funext hg)
  have h0 := congrFun hfun (π g⁻¹ u)
  have e1 : π g (π g⁻¹ u) = u := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, mul_inv_cancel, hone]; rfl
  simp only [e1] at h0
  exact inner_self_eq_zero.1 h0
end Formalism.MainNotions.LeviCoordinates
