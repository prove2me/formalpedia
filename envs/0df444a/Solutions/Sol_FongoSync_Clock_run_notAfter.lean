-- Prove2me | solution 1 for FongoSync.Clock.run_notAfter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:02:17.129286+00:00
-- url     : https://prove2.me/submissions/c5fa89f3-e83c-494a-b61f-c46de6dc67d9


import Definitions.Def_FongoSync_Clock
import Theorems.Thm_FongoSync_Hlc_notAfter_trans
import Theorems.Thm_FongoSync_Hlc_notAfter_refl
import Theorems.Thm_FongoSync_Clock_tick_before
import Theorems.Thm_FongoSync_Clock_tick_last
import Theorems.Thm_FongoSync_Clock_observe_notAfter

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Clock
theorem _root_.solution (c : Clock) (events : List Event) :
    c.last.NotAfter (c.run events).1.last ∧ ∀ r ∈ (c.run events).2, r.NotAfter (c.run events).1.last := by
  induction events generalizing c with
  | nil => exact ⟨Hlc.notAfter_refl _, by simp [Clock.run]⟩
  | cons e rest ih =>
    cases e with
    | tick wall =>
      have ⟨h₁, h₂⟩ := ih (c.tick wall).2
      have step : c.last.NotAfter (c.tick wall).2.last := by
        have := c.tick_before wall
        unfold Hlc.Before at this; unfold Hlc.NotAfter; rw [Clock.tick_last]; omega
      refine ⟨Hlc.notAfter_trans step h₁, ?_⟩
      intro r hr
      simp only [Clock.run, List.mem_cons] at hr
      rcases hr with rfl | hr
      · rw [← Clock.tick_last]; exact h₁
      · exact h₂ r hr
    | observe remote =>
      have ⟨h₁, h₂⟩ := ih (c.observe remote)
      have ⟨s₁, s₂⟩ := c.observe_notAfter remote
      refine ⟨Hlc.notAfter_trans s₁ h₁, ?_⟩
      intro r hr
      simp only [Clock.run] at hr
      by_cases he : remote.encodable
      · simp only [he, ↓reduceIte, List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact Hlc.notAfter_trans (s₂ he) h₁
        · exact h₂ r hr
      · simp only [he, ↓reduceIte] at hr
        exact h₂ r hr
end Clock
end FongoSync
