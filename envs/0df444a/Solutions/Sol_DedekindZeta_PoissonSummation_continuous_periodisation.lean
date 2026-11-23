-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.continuous_periodisation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:03:21.55446+00:00
-- url     : https://prove2.me/submissions/74327c1f-0783-49eb-bed6-15fdc53cdbd3

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution : Continuous (periodisation L f) := by
  classical
  -- Continuity is local; we prove `ContinuousAt` at every point `x₀` by exhibiting
  -- a uniform (cofinite) Schwartz tail bound on the open ball `Metric.ball x₀ 1`.
  rw [continuous_iff_continuousAt]
  intro x₀
  set d : ℕ := Module.finrank ℤ L with hd
  set N : ℕ := d + 1 with hN
  -- The real exponent `s = -(d+1) < -d` controlling the lattice sum.
  set s : ℝ := -(N : ℝ) with hs
  have hsd : s < -(Module.finrank ℤ L : ℝ) := by
    rw [hs, hN, ← hd]; push_cast; linarith
  -- The neighbourhood: the unit ball around `x₀`. On it `‖x‖ ≤ C₀ := ‖x₀‖ + 1`.
  set C₀ : ℝ := ‖x₀‖ + 1 with hC₀
  have hC₀pos : 0 < C₀ := by positivity
  have hxle : ∀ x ∈ Metric.ball x₀ 1, ‖x‖ ≤ C₀ := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
      _ ≤ ‖x₀‖ + 1 := by have h := hx.le; gcongr
  -- Schwartz decay with `k = N`: `‖y‖ ^ N * ‖f y‖ ≤ C`.
  obtain ⟨C, hCpos, hC⟩ := f.decay N 0
  have hC' : ∀ y : V, ‖y‖ ^ N * ‖(f : V → ℂ) y‖ ≤ C := by
    intro y; have := hC y; rwa [norm_iteratedFDeriv_zero] at this
  -- The dominating function `u v = C · 2^N · ‖v‖ ^ s`, summable over the lattice.
  set u : L → ℝ := fun v => C * 2 ^ N * ‖(v : V)‖ ^ s with hu_def
  have husum : Summable u := by
    have h0 := ZLattice.summable_norm_sub_rpow L s hsd 0
    have h0' : Summable fun v : L => ‖(v : V)‖ ^ s := by
      refine h0.congr fun v => ?_; rw [sub_zero]
    exact h0'.mul_left (C * 2 ^ N)
  -- The lattice inclusion tends to `cocompact V` along `cofinite`, so `‖v‖ → ∞`.
  have hLclosed : IsClosed (X := V) (L : Set V) :=
    @AddSubgroup.isClosed_of_discrete _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hcoe : Filter.Tendsto ((↑) : L → V) Filter.cofinite (Filter.cocompact V) :=
    tendsto_cofinite_cocompact_of_discrete
      hLclosed.isClosedEmbedding_subtypeVal.tendsto_cocompact
  have hnorm : Filter.Tendsto (fun v : L => ‖(v : V)‖) Filter.cofinite Filter.atTop :=
    tendsto_norm_cocompact_atTop.comp hcoe
  -- The eventual (cofinite) uniform tail bound on the ball.
  have hfu : ∀ᶠ v : L in Filter.cofinite,
      ∀ x ∈ Metric.ball x₀ 1, ‖(fun x => (f : V → ℂ) (x + v)) x‖ ≤ u v := by
    filter_upwards [hnorm.eventually_ge_atTop (2 * C₀)] with v hv x hx
    have hxC₀ : ‖x‖ ≤ C₀ := hxle x hx
    have hbpos : 0 < ‖(v : V)‖ := lt_of_lt_of_le (by positivity) hv
    -- `a := ‖x + v‖ ≥ ‖v‖ / 2 > 0`.
    have hage : ‖(v : V)‖ / 2 ≤ ‖x + (v : V)‖ := by
      have h1 : ‖(v : V)‖ - ‖x‖ ≤ ‖x + (v : V)‖ := by
        have htri : ‖(v : V)‖ ≤ ‖x + (v : V)‖ + ‖x‖ := by
          calc ‖(v : V)‖ = ‖(x + (v : V)) - x‖ := by rw [add_sub_cancel_left]
            _ ≤ ‖x + (v : V)‖ + ‖x‖ := norm_sub_le _ _
        linarith
      have h2 : ‖(v : V)‖ / 2 ≤ ‖(v : V)‖ - ‖x‖ := by
        have : ‖x‖ ≤ ‖(v : V)‖ / 2 := by
          have : C₀ ≤ ‖(v : V)‖ / 2 := by linarith
          linarith
        linarith
      linarith
    have hapos : 0 < ‖x + (v : V)‖ := lt_of_lt_of_le (by positivity) hage
    -- From decay: `‖f(x+v)‖ ≤ C / ‖x+v‖^N`.
    have hfle : ‖(f : V → ℂ) (x + (v : V))‖ ≤ C / ‖x + (v : V)‖ ^ N := by
      rw [le_div_iff₀ (by positivity)]
      have := hC' (x + (v : V))
      linarith [this, mul_comm (‖x + (v:V)‖ ^ N) (‖(f:V→ℂ) (x+(v:V))‖)]
    -- `‖x+v‖^N ≥ (‖v‖/2)^N = ‖v‖^N / 2^N`.
    have hpow : (‖(v : V)‖ / 2) ^ N ≤ ‖x + (v : V)‖ ^ N := by
      gcongr
    have hpow' : ‖(v : V)‖ ^ N / 2 ^ N ≤ ‖x + (v : V)‖ ^ N := by
      rw [div_pow] at hpow; exact hpow
    -- Combine and rewrite `‖v‖^s = (‖v‖^N)⁻¹`.
    have hrpow : ‖(v : V)‖ ^ s = (‖(v : V)‖ ^ N)⁻¹ := by
      rw [hs, Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    show ‖(f : V → ℂ) (x + (v : V))‖ ≤ C * 2 ^ N * ‖(v : V)‖ ^ s
    rw [hrpow]
    have hvN : (0 : ℝ) < ‖(v : V)‖ ^ N := by positivity
    calc ‖(f : V → ℂ) (x + (v : V))‖
        ≤ C / ‖x + (v : V)‖ ^ N := hfle
      _ ≤ C / (‖(v : V)‖ ^ N / 2 ^ N) := by
            apply div_le_div_of_nonneg_left (le_of_lt hCpos) (by positivity) hpow'
      _ = C * 2 ^ N * (‖(v : V)‖ ^ N)⁻¹ := by
            rw [div_div_eq_mul_div, div_eq_mul_inv]
  -- Uniform convergence of the partial sums on the ball, hence continuity there.
  have hcont : ∀ v : L, Continuous (fun x => (f : V → ℂ) (x + v)) := fun v =>
    f.continuous.comp (by fun_prop)
  have htu : TendstoUniformlyOn
      (fun t : Finset L => fun x => ∑ v ∈ t, (f : V → ℂ) (x + v))
      (periodisation L f) Filter.atTop (Metric.ball x₀ 1) := by
    have := tendstoUniformlyOn_tsum_of_cofinite_eventually husum hfu
    exact this
  have hcontOn : ContinuousOn (periodisation L f) (Metric.ball x₀ 1) :=
    htu.continuousOn (Filter.Eventually.frequently <| Filter.Eventually.of_forall fun t =>
      continuousOn_finsetSum t fun v _ => (hcont v).continuousOn)
  exact hcontOn.continuousAt (Metric.ball_mem_nhds x₀ one_pos)
end DedekindZeta.PoissonSummation
