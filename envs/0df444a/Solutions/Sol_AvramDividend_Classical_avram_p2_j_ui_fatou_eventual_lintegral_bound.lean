-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_fatou_eventual_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:36:04.165195+00:00
-- url     : https://prove2.me/submissions/3761b131-3122-4598-9b73-bd60e667d80e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

/-! A.e. limits preserve eventual ENNReal lintegral bounds by Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ENNReal) (V : Ω → ENNReal)
    (K : ENNReal) (hm : ∀ n, Measurable (F n))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (V ω)))
    (hB : ∀ᶠ n : ℕ in atTop, (∫⁻ ω, F n ω ∂P) ≤ K) :
    (∫⁻ ω, V ω ∂P) ≤ K := by
  have hlim : ∀ᵐ ω ∂P,
      V ω = Filter.liminf (fun n => F n ω) atTop := by
    filter_upwards [hae] with ω hω
    exact hω.liminf_eq.symm
  have hFatou : (∫⁻ ω, V ω ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop := by
    rw [lintegral_congr_ae hlim]
    exact lintegral_liminf_le hm
  exact hFatou.trans
    ((Filter.liminf_le_liminf hB).trans (by rw [liminf_const]))
