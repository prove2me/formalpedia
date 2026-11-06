-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_masked_contact_tail_intersection_eq_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:08:33.640857+00:00
-- url     : https://prove2.me/submissions/be5e1af8-cbfb-493f-8cb4-1d483d7f2877

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The only point surviving every original shrinking contact tail is its payment-masked right endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (τ : ℝ≥0)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    (⋂ n : ℕ, paymentTimes (ruinTime X x D ω) ∩
      Ioc ((τ : ℝ) - δ n) (τ : ℝ)) =
        paymentTimes (ruinTime X x D ω) ∩ ({(τ : ℝ)} : Set ℝ) := by
  ext t
  constructor
  · intro ht
    have hAll (n : ℕ) :
        t ∈ paymentTimes (ruinTime X x D ω) ∩
          Ioc ((τ : ℝ) - δ n) (τ : ℝ) :=
      Set.mem_iInter.mp ht n
    have hUpper : t ≤ (τ : ℝ) := (hAll 0).2.2
    have htEq : t = (τ : ℝ) := by
      rcases lt_or_eq_of_le hUpper with hlt | heq
      · have hgap : (0 : ℝ) < (τ : ℝ) - t := sub_pos.mpr hlt
        have hEventually : ∀ᶠ n : ℕ in atTop, δ n < (τ : ℝ) - t :=
          hδ.eventually (isOpen_Iio.mem_nhds hgap)
        obtain ⟨n, hn⟩ := hEventually.exists
        have hLower : (τ : ℝ) - δ n < t := (hAll n).2.1
        linarith
      · exact heq
    exact ⟨(hAll 0).1, htEq⟩
  · rintro ⟨hPay, htEq⟩
    subst t
    apply Set.mem_iInter.mpr
    intro n
    exact ⟨hPay, ⟨by linarith [hδpos n], le_rfl⟩⟩
