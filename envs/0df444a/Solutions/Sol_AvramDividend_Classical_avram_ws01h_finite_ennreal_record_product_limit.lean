-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_finite_ennreal_record_product_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:26:06.164059+00:00
-- url     : https://prove2.me/submissions/aa16136b-0d3b-497a-aa1f-df0bfa329776

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.ENNReal.Operations

open Filter
open scoped ENNReal Topology
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A finite, original positive-rate renewal product identity persists
under exact extended-nonnegative-real convergence. -/
theorem solution
    (f g h : ℕ → ℝ≥0∞) (c Cx Ca K : ℝ≥0∞)
    (hc : c ≠ ⊤) (hCa : Ca ≠ ⊤) (hK : K ≠ ⊤)
    (hf : Tendsto f atTop (𝓝 Cx))
    (hg : Tendsto g atTop (𝓝 Ca))
    (hh : Tendsto h atTop (𝓝 K))
    (hfactor : ∀ n : ℕ, f n = c * (g n * h n)) :
    Cx = c * (Ca * K) := by
  have hCaK : Ca * K ≠ ⊤ := ENNReal.mul_ne_top hCa hK
  have hgh : Tendsto (fun n : ℕ => g n * h n) atTop (𝓝 (Ca * K)) :=
    ENNReal.Tendsto.mul hg (Or.inr hK) hh (Or.inr hCa)
  have hcT : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
    tendsto_const_nhds
  have hfull :
      Tendsto (fun n : ℕ => c * (g n * h n)) atTop (𝓝 (c * (Ca * K))) :=
    ENNReal.Tendsto.mul hcT (Or.inr hCaK) hgh (Or.inr hc)
  have hfun : f = fun n : ℕ => c * (g n * h n) := funext hfactor
  rw [hfun] at hf
  exact tendsto_nhds_unique hf hfull
