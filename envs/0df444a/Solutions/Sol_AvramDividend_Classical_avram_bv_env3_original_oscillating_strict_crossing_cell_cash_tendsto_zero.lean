-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_oscillating_strict_crossing_cell_cash_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:33:52.372197+00:00
-- url     : https://prove2.me/submissions/0e65a302-eccc-443a-88df-8cc8f800dabc

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A convergent, possibly oscillating last-cell left endpoint can be bounded
    against any strictly subterminal monotone reference mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds (T : ℝ)))
    (b : ℕ → ℝ) (hb : Monotone b)
    (hbelow : ∀ n, b n < (T : ℝ))
    (hblim : Tendsto b atTop (nhds (T : ℝ))) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioo (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by
  let F : ℝ → ℝ≥0∞ := fun z =>
    ∫⁻ t in paymentTimes σ ∩ Ioo z (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hreference : Tendsto (fun n => F (b n)) atTop (nhds 0) := by
    simpa only [F] using
      (avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
        D hD ω σ T q hq b hb hblim)
  have hoscillating : Tendsto (fun n => F (a n)) atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro y hy
      exact False.elim ((not_lt_of_ge bot_le) hy)
    · intro y hy
      have hbound : ∀ᶠ k in atTop, F (b k) < y :=
        (tendsto_order.1 hreference).2 y hy
      obtain ⟨k, hk⟩ := hbound.exists
      have hevent : ∀ᶠ n in atTop, b k < a n :=
        ha.eventually (isOpen_Ioi.mem_nhds (hbelow k))
      filter_upwards [hevent] with n hn
      have hsubset :
          paymentTimes σ ∩ Ioo (a n) (T : ℝ) ⊆
          paymentTimes σ ∩ Ioo (b k) (T : ℝ) := by
        intro t ht
        exact ⟨ht.1, lt_trans hn ht.2.1, ht.2.2⟩
      have hle : F (a n) ≤ F (b k) := by
        exact lintegral_mono_set
          (f := fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))
          (μ := dividendMeasure D ω) hsubset
      exact lt_of_le_of_lt hle hk
  simpa only [F] using hoscillating
