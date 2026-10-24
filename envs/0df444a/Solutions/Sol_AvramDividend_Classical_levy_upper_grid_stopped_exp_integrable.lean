-- Prove2me | solution 1 for AvramDividend.Classical.levy_upper_grid_stopped_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:25:21.31681+00:00
-- url     : https://prove2.me/submissions/3254f23a-5b6c-48b3-8506-e3fbe247e8ba

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω) :
    Integrable (fun ω => Real.exp
      (θ * X.X (clock (K ω)) ω - ((clock (K ω)) : ℝ) * X.ψ θ)) P := by
  let Z : ℕ → Ω → ℝ := fun k ω => X.X (clock k) ω
  let M : ℕ → Ω → ℝ := fun k ω =>
    Real.exp (θ * Z k ω - ((clock k) : ℝ) * X.ψ θ)
  have hZ : Adapted H Z := by
    intro k
    change Measurable[H k] (X.X (clock k))
    rw [hH k]
    exact X.adapted (clock k)
  have hτ : IsStoppingTime H (fun ω => (K ω : WithTop ℕ)) := by
    intro i
    have hhit := (hZ.isStoppingTime_hittingBtwn
      (s := Ioi z) measurableSet_Ioi (n := 0) (n' := m)) i
    convert hhit using 1
    ext ω
    simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
    rw [hK ω]
    change ((hittingBtwn Z (Ioi z) 0 m ω : ℕ) : WithTop ℕ) ≤
      (i : WithTop ℕ) ↔ hittingBtwn Z (Ioi z) 0 m ω ≤ i
    constructor <;> intro h <;> exact_mod_cast h
  have hKbd : ∀ ω, (K ω : WithTop ℕ) ≤ (m : WithTop ℕ) := by
    intro ω
    rw [hK ω]
    exact_mod_cast (hittingBtwn_le
      (u := Z) (s := Ioi z) (n := 0) (m := m) ω)
  have hM : Martingale M H P := by
    exact chat03_martingale_sampled_filtration_reindex_corrected
      (fun t ω => Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))
      (levy_compensated_exponential_martingale X θ hθ)
      clock hc H hH
  have hInt : Integrable
      (stoppedValue M (fun ω => (K ω : WithTop ℕ))) P :=
    integrable_stoppedValue ℕ hτ hM.integrable hKbd
  change Integrable (fun ω => M (K ω) ω) P at hInt
  exact hInt
