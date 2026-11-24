-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelIdx.levelIdx_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:37:38.120235+00:00
-- url     : https://prove2.me/submissions/bf7558d3-a57d-4967-a270-a8861fdd0d1c

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
import Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_card_reduction
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelIdx
open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct
variable (I : AutInst)
variable {I}
namespace Formalism.MainNotions.BridgeLevelIdx
theorem _root_.solution (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) := by
  classical
  obtain ⟨α, _, ρ, hcard, hρ⟩ := card_reduction hg hG
  let rp : α → I.Gf := fun a => if h : ∃ x ∈ I.Kset, ρ x = a then h.choose else 1
  have hcov : I.Kset ⊆ ⋃ a, (fun h => rp a * h) '' I.Kg g := by
    intro x hx
    have hex : ∃ x₀ ∈ I.Kset, ρ x₀ = ρ x := ⟨x, hx, rfl⟩
    refine Set.mem_iUnion.2 ⟨ρ x, (rp (ρ x))⁻¹ * x, ?_, by simp⟩
    have e : rp (ρ x) = hex.choose := by simp only [rp, dif_pos hex]
    rw [e]
    exact hρ _ hex.choose_spec.1 x hx hex.choose_spec.2
  have hone : ∀ a, μf ((fun h => rp a * h) '' I.Kg g) = μf (I.Kg g) := by
    intro a
    rw [Set.image_mul_left]
    exact measure_preimage_mul μf _ _
  calc μf I.Kset ≤ μf (⋃ a, (fun h => rp a * h) '' I.Kg g) := measure_mono hcov
    _ ≤ ∑ a, μf ((fun h => rp a * h) '' I.Kg g) := measure_iUnion_fintype_le _ _
    _ = (Fintype.card α : ℝ≥0∞) * μf (I.Kg g) := by
        simp only [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by gcongr
end Formalism.MainNotions.BridgeLevelIdx
