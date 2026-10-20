-- Prove2me | solution 1 for AvramDividend.Classical.chat03_two_sided_grid_stopped_compensated_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T18:19:31.975988+00:00
-- url     : https://prove2.me/submissions/43dfd9b4-fda7-4f5d-b0cb-0d6e2e942b7e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-!
Uniformly finite grid optional sampling gives actual Bochner integrability
of the exponential stopped at the strict first two-sided grid exit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Integrable (fun ω =>
      Real.exp (θ * X.X (clock (K ω)) ω -
        ((clock (K ω)) : ℝ) * X.ψ θ)) P := by
  let Z : ℕ → Ω → ℝ := fun k ω => X.X (clock k) ω
  let Y : ℕ → Ω → ℝ := fun k ω =>
    max (Z k ω - upper) (lower - Z k ω)
  let M : ℕ → Ω → ℝ := fun k ω =>
    Real.exp (θ * Z k ω - ((clock k) : ℝ) * X.ψ θ)
  have hZ : Adapted H Z := by
    intro k
    change Measurable[H k] (X.X (clock k))
    rw [hH k]
    exact X.adapted (clock k)
  have hY : Adapted H Y := by
    intro k
    exact ((hZ k).sub measurable_const).max
      (measurable_const.sub (hZ k))
  have hτ : IsStoppingTime H (fun ω => (K ω : WithTop ℕ)) := by
    intro i
    have hhit := (hY.isStoppingTime_hittingBtwn
      (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (n := 0) (n' := m)) i
    convert hhit using 1
    ext ω
    simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
    rw [hK ω]
    change ((hittingBtwn Y (Set.Ioi (0 : ℝ)) 0 m ω : ℕ) : WithTop ℕ) ≤ (i : WithTop ℕ) ↔
      hittingBtwn Y (Set.Ioi (0 : ℝ)) 0 m ω ≤ i
    constructor <;> intro h <;> exact_mod_cast h
  have hKbd : ∀ ω, (K ω : WithTop ℕ) ≤ (m : WithTop ℕ) := by
    intro ω
    rw [hK ω]
    exact_mod_cast
      (hittingBtwn_le (u := Y) (s := Set.Ioi (0 : ℝ))
        (n := 0) (m := m) ω)
  have hM : Martingale M H P := by
    exact chat03_martingale_sampled_filtration_reindex_corrected
      (fun t ω => Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ))
      (levy_compensated_exponential_martingale X θ hθ)
      clock hc H hH
  have hInt : Integrable
      (stoppedValue M (fun ω => (K ω : WithTop ℕ))) P :=
    integrable_stoppedValue ℕ hτ hM.integrable hKbd
  change Integrable (fun ω => M (K ω) ω) P at hInt
  exact hInt
