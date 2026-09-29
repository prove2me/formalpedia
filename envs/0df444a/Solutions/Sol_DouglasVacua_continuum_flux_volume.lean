-- Prove2me | solution 1 for DouglasVacua.continuum_flux_volume
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:52:27.315978+00:00
-- url     : https://prove2.me/submissions/40abd1b4-d4ea-49f1-9338-048ce46c4b90

import Mathlib

open Real MeasureTheory

lemma dvSqrtPow (x : ℝ) (hx : 0 ≤ x) (J : ℕ) : Real.sqrt x ^ J = x ^ ((J : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

lemma dvFluxVolume (J : ℕ) (c V : ℝ) (hc : 0 < c) (hV : 0 ≤ V) :
    volume {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V} =
      ENNReal.ofReal (π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1) *
        (V / c) ^ ((J : ℝ) / 2)) := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    have hU : {x : Fin 0 → ℝ | c * ∑ i, x i ^ 2 ≤ V} = Set.univ := by
      ext x
      simp [hV]
    rw [hU, volume_pi, Measure.pi_univ]
    simp
  · have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
    have hVc : 0 ≤ V / c := div_nonneg hV hc.le
    set r := Real.sqrt (V / c) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hS : {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V} =
        (WithLp.toLp 2) ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin J)) r) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_closedBall_zero_iff]
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hr0 two_ne_zero, EuclideanSpace.norm_sq_eq,
        hr, Real.sq_sqrt hVc, le_div_iff₀ hc, mul_comm]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hS, (PiLp.volume_preserving_toLp (Fin J)).measure_preimage
      measurableSet_closedBall.nullMeasurableSet, EuclideanSpace.volume_closedBall,
      Fintype.card_fin, ← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_mul (pow_nonneg hr0 _)]
    congr 1
    rw [hr, dvSqrtPow _ hVc, dvSqrtPow _ Real.pi_pos.le]
    ring

open Real MeasureTheory in
theorem solution (J : ℕ) (c V : ℝ) (hc : 0 < c) (hV : 0 ≤ V) :
    volume {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V} =
      ENNReal.ofReal (π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1) *
        (V / c) ^ ((J : ℝ) / 2)) := by
  exact dvFluxVolume J c V hc hV

