-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrc_exists_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:44.170102+00:00
-- url     : https://prove2.me/submissions/e35e884e-093b-4ffe-b6e6-56a7ab5af6fc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrcTendstoVec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_bound
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrc_intOn

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
omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G] [μ.IsHaarMeasure]
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution (hn : ∀ g x, ‖π g x‖ = ‖x‖) (hm : ∀ x y, AEStronglyMeasurable (fun g => ⟪x, π g y⟫_ℂ) μ)
    {k : Set G} (hk : μ k < ⊤) (v : H) : ∃ w : H, ∀ u, ⟪w, u⟫_ℂ = ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ := by
  have hint := fun u => rrc_intOn hn hm hk v u
  let L : H →ₗ[ℂ] ℂ :=
    { toFun := fun u => ∫ g in k, ⟪π g v, u⟫_ℂ ∂μ
      map_add' := fun a b => by
        simp only [inner_add_right]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c a => by
        simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul _ _ }
  have hb : ∀ u, ‖L u‖ ≤ (‖v‖ * μ.real k) * ‖u‖ := fun u => by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ) hk (fun g _ => rrc_bound hn g v u)
    calc ‖L u‖ ≤ ‖v‖ * ‖u‖ * μ.real k := this
      _ = (‖v‖ * μ.real k) * ‖u‖ := by ring
  refine ⟨(InnerProductSpace.toDual ℂ H).symm (L.mkContinuous _ hb), fun u => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl
end Formalism.MainNotions.LeviCoordinates
