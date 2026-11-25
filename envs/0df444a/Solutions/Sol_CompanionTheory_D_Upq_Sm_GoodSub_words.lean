-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.GoodSub.words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:43.983458+00:00
-- url     : https://prove2.me/submissions/7a69049f-ddc9-40b6-a6fd-d6ca00303d4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
import Theorems.Thm_CompanionTheory_D_Upq_Sm_GoodSub_step
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G K : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.Upq.Sm
namespace GoodSub
theorem _root_.solution (hG : IsMatGroup G) (h : RepOn G σ) (hK : K ⊆ G) {T : Submodule ℂ H}
    (hT : GoodSub G K σ T) {w : H} (hw : w ∈ T) (m : ℕ) :
    ∃ (T' : Submodule ℂ H) (C : ℝ), GoodSub G K σ T' ∧ 0 ≤ C ∧ ∀ W : List (Mat n), LieW G W →
      (∀ X ∈ W, ‖X‖ ≤ 1) → W.length ≤ m → dsW σ W w ∈ T' ∧ ‖dsW σ W w‖ ≤ C := by
  induction m with
  | zero =>
    refine ⟨T, ‖w‖, hT, norm_nonneg _, fun W _ _ hW => ?_⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hW)]
    exact ⟨hw, le_rfl⟩
  | succ m ih =>
    obtain ⟨T₁, C₁, h₁, hC₁, hW₁⟩ := ih
    obtain ⟨T₂, C₂, h₂, hle, hC₂, hW₂⟩ := h₁.step hG h hK
    refine ⟨T₂, C₁ + C₂ * C₁, h₂, by positivity, fun W hL hn hW => ?_⟩
    cases W with
    | nil =>
      obtain ⟨a, b⟩ := hW₁ [] hL hn (Nat.zero_le _)
      exact ⟨hle a, b.trans (le_add_of_nonneg_right (by positivity))⟩
    | cons X W =>
      obtain ⟨a, b⟩ := hW₁ W (fun Y hY => hL Y (List.mem_cons_of_mem _ hY))
        (fun Y hY => hn Y (List.mem_cons_of_mem _ hY)) (by simpa using hW)
      obtain ⟨c, d⟩ := hW₂ X (hL X List.mem_cons_self) (hn X List.mem_cons_self) _ a
      refine ⟨c, d.trans ?_⟩
      exact (mul_le_mul_of_nonneg_left b hC₂).trans (le_add_of_nonneg_left hC₁)
end GoodSub
end CompanionTheory.D.Upq.Sm
