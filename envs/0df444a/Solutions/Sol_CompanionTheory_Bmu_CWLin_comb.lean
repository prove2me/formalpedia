-- Prove2me | solution 1 for CompanionTheory.Bmu.CWLin.comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:13:17.650809+00:00
-- url     : https://prove2.me/submissions/e3fd80b0-87dd-4122-ae7f-7bbd81028612

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {Hm : Mat n} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat n → (H →L[ℂ] H)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
omit [CompleteSpace H]
namespace CompanionTheory.Bmu
namespace CWLin
theorem _root_.solution {B₁ B₂ : H → V} (h₁ : CWLin Hm σ B₁) (h₂ : CWLin Hm σ B₂) (a b : ℂ) :
    CWLin Hm σ (fun v => a • B₁ v + b • B₂ v) := by
  refine ⟨fun x hx x' hx' => ?_, fun c x hx => ?_, ?_⟩
  · rw [h₁.add _ hx _ hx', h₂.add _ hx _ hx', smul_add, smul_add]; abel
  · rw [h₁.smul _ _ hx, h₂.smul _ _ hx, smul_add, smul_comm a c, smul_comm b c]
  · obtain ⟨C₁, W₁, hW₁, hb₁⟩ := h₁.bd
    obtain ⟨C₂, W₂, hW₂, hb₂⟩ := h₂.bd
    refine ⟨‖a‖ * |C₁| + ‖b‖ * |C₂|, W₁ ++ W₂, fun W hW => (List.mem_append.1 hW).elim (hW₁ W) (hW₂ W),
      fun v hv => ?_⟩
    rw [List.map_append, List.sum_append]
    set s₁ := (W₁.map fun W => ‖dsW σ W v‖).sum
    set s₂ := (W₂.map fun W => ‖dsW σ W v‖).sum
    have p₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
      obtain ⟨W, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    have p₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
      obtain ⟨W, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    have q₁ : ‖B₁ v‖ ≤ |C₁| * s₁ := (hb₁ v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₁)
    have q₂ : ‖B₂ v‖ ≤ |C₂| * s₂ := (hb₂ v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₂)
    have r₁ := mul_le_mul_of_nonneg_left q₁ (norm_nonneg a)
    have r₂ := mul_le_mul_of_nonneg_left q₂ (norm_nonneg b)
    have t₁ : 0 ≤ ‖a‖ * |C₁| * s₂ := by positivity
    have t₂ : 0 ≤ ‖b‖ * |C₂| * s₁ := by positivity
    calc ‖a • B₁ v + b • B₂ v‖ ≤ ‖a‖ * ‖B₁ v‖ + ‖b‖ * ‖B₂ v‖ := by
          rw [← norm_smul, ← norm_smul]; exact norm_add_le _ _
      _ ≤ _ := by nlinarith
end CWLin
end CompanionTheory.Bmu
