-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump11_eventwise_trim_to_original_ae_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:39:37.966297+00:00
-- url     : https://prove2.me/submissions/2abe8fc7-cd23-4e17-a714-eababd451d3f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (f g : Ω → ℝ)
    (hf : Integrable f (P.trim hm))
    (hg : Integrable g (P.trim hm))
    (hEvent : ∀ A : Set Ω, MeasurableSet[m] A →
      (P.trim hm) A < ⊤ →
      (∫ ω in A, f ω ∂(P.trim hm)) ≤
      (∫ ω in A, g ω ∂(P.trim hm))) :
    ∀ᵐ ω ∂P, f ω ≤ g ω := by
  classical
  apply ae_of_ae_trim hm
  exact ae_le_of_forall_setIntegral_le hf hg
    (fun A hA hFinite => hEvent A hA hFinite)
