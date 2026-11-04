-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_approximation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:31:29.312734+00:00
-- url     : https://prove2.me/submissions/62eb8b27-270a-493e-acb9-c0395b58ca38

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

theorem solution
    {ι : Type*} (l : Filter ι) (f : ι → ℝ) (a : ℝ)
    (happrox : ∀ δ : ℝ, 0 < δ →
      ∃ q : ι → ℝ, ∃ b : ℝ,
        Tendsto q l (nhds b) ∧
        (∀ᶠ i in l, |f i - q i| ≤ δ) ∧ |a - b| ≤ δ) :
    Tendsto f l (nhds a) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε / 3 := by linarith
  obtain ⟨q, b, hq, herror, hlimit⟩ := happrox (ε / 3) hδ
  have hnear : ∀ᶠ i in l, |q i - b| < ε / 3 := by
    have hevent := (Metric.tendsto_nhds.mp hq) (ε / 3) hδ
    filter_upwards [hevent] with i hi
    simpa only [Real.dist_eq] using hi
  filter_upwards [herror, hnear] with i he hi
  have htri₁ : |f i - a| ≤ |f i - q i| + |q i - a| :=
    abs_sub_le (f i) (q i) a
  have htri₂ : |q i - a| ≤ |q i - b| + |b - a| :=
    abs_sub_le (q i) b a
  rw [abs_sub_comm a b] at hlimit
  rw [Real.dist_eq]
  linarith
