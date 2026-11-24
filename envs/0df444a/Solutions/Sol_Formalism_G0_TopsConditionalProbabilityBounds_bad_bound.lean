-- Prove2me | solution 1 for Formalism.G0.TopsConditionalProbabilityBounds.bad_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:24.175954+00:00
-- url     : https://prove2.me/submissions/1de9bc7e-1018-4f59-ba1f-d8c897ffa175

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartC
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityBounds_condProb_mono
import Theorems.Thm_Formalism_G0_TopsConditionalProbabilityBounds_condProb_disjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.G0
open Formalism.G0.TopsConditionalProbabilityBounds
open Finset
namespace Formalism.G0.TopsConditionalProbabilityBounds
theorem _root_.solution (n : ℕ) (δ : ℝ) (G : ℕ) (hn : 2 ≤ n) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (i : ℕ) (hi : i < n) :
    condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T) ≤ (1 - δ) ^ G := by
  rcases lt_or_ge (i + G) n with hlt | hge
  · calc condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T)
        ≤ condProb n δ (fun T => Disjoint (Icc (i + 1) (i + G)) T) := by
          apply condProb_mono n δ hδ0 hδ1
          rintro T _ ⟨_, hT⟩
          rw [disjoint_left]
          intro x hx hxT
          rw [mem_Icc] at hx
          have := hT (x - i) (by omega) (by omega)
          rw [show i + (x - i) = x by omega, Nat.mod_eq_of_lt (by omega)] at this
          exact this hxT
      _ = (1 - δ) ^ (Icc (i + 1) (i + G)).card := by
          apply condProb_disjoint n δ _ _ _ (by omega)
          · intro x hx
            rw [mem_Icc] at hx
            rw [mem_range]
            omega
          · rw [mem_Icc]
            omega
      _ = (1 - δ) ^ G := by
          rw [Nat.card_Icc]
          congr 1
          omega
  · calc condProb n δ (fun T => i ∈ T ∧ ∀ d, 1 ≤ d → d ≤ G → (i + d) % n ∉ T)
        ≤ condProb n δ (fun _ => False) := by
          apply condProb_mono n δ hδ0 hδ1
          rintro T h0T ⟨_, hT⟩
          have := hT (n - i) (by omega) (by omega)
          rw [show i + (n - i) = n by omega, Nat.mod_self] at this
          exact this h0T
      _ = 0 := by
          unfold condProb
          simp
      _ ≤ (1 - δ) ^ G := pow_nonneg (by linarith) _
end Formalism.G0.TopsConditionalProbabilityBounds
