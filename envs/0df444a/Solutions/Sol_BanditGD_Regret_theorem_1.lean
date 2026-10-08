-- Prove2me | solution 1 for BanditGD.Regret.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:05:17.968016+00:00
-- url     : https://prove2.me/submissions/7dbd3181-dad3-40dc-b87f-7b1f3c2ceebc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_RegretBandits_Nonlinear_OSGD
import Definitions.Def_BanditGD_Regret_Setting
import Theorems.Thm_BanditGD_Regret_eq_10

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

theorem bgd_param_algebra (r R d C : ℝ) (n : ℕ) (hr : 0 < r) (hR : 0 < R) (hd : 1 ≤ d)
    (hC : 0 < C) (hn : (3 * R * d / (2 * r)) ^ 2 ≤ (n : ℝ)) (δ α : ℝ)
    (hδ : δ = (r * R ^ 2 * d ^ 2 / (12 * n)) ^ ((1 : ℝ) / 3))
    (hα : α = (3 * R * d / (2 * r * Real.sqrt n)) ^ ((1 : ℝ) / 3)) :
    1 ≤ n ∧ 0 < δ ∧ δ < α * r ∧ α ≤ 1 ∧
    R * d * C * Real.sqrt n / δ + 3 * δ * (2 * C / (α * r)) * n + 2 * α * C * n
      ≤ 3 * C * (n : ℝ) ^ ((5 : ℝ) / 6) * (12 * d * R / r) ^ ((1 : ℝ) / 3) := by
  have hA : 0 < 3 * R * d / (2 * r) := by positivity
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hn1 : 1 ≤ n := by exact_mod_cast hnpos
  set N : ℝ := (n : ℝ) ^ ((1 : ℝ) / 6) with hNdef
  set K : ℝ := (12 * d * R / r) ^ ((1 : ℝ) / 3) with hKdef
  have hN0 : 0 < N := Real.rpow_pos_of_pos hnpos _
  have hK0 : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  have hN6 : N ^ 6 = n := by
    rw [hNdef, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have hK3 : K ^ 3 = 12 * d * R / r := by
    rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hsq : Real.sqrt n = N ^ 3 := by
    rw [← hN6, show N ^ 6 = (N ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h56 : (n : ℝ) ^ ((5 : ℝ) / 6) = N ^ 5 := by
    rw [hNdef, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have hcube : ∀ x y : ℝ, 0 ≤ y → x = y ^ 3 → x ^ ((1 : ℝ) / 3) = y := by
    intro x y hy hxy
    rw [hxy, ← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num
  have hδ' : δ = r * K ^ 2 / (12 * N ^ 2) := by
    rw [hδ]; apply hcube _ _ (by positivity)
    have e : (r * K ^ 2 / (12 * N ^ 2)) ^ 3 = r ^ 3 * (K ^ 3) ^ 2 / (1728 * N ^ 6) := by ring
    rw [e, hK3, hN6]; field_simp; ring
  have hα' : α = K / (2 * N) := by
    rw [hα]; apply hcube _ _ (by positivity)
    have e : (K / (2 * N)) ^ 3 = K ^ 3 / (8 * N ^ 3) := by ring
    rw [e, hK3, hsq]; field_simp; ring
  have hKN : K ≤ 2 * N := by
    have h1 : K ^ 6 ≤ (2 * N) ^ 6 := by
      have e : K ^ 6 = 64 * (3 * R * d / (2 * r)) ^ 2 := by
        rw [show K ^ 6 = (K ^ 3) ^ 2 by ring, hK3]; field_simp; ring
      rw [e, show (2 * N) ^ 6 = 64 * N ^ 6 by ring, hN6]; linarith
    exact (pow_le_pow_iff_left₀ hK0.le (by positivity) (by norm_num)).1 h1
  refine ⟨hn1, by rw [hδ']; positivity, ?_, ?_, ?_⟩
  · rw [hδ', hα']
    have e : r * K ^ 2 / (12 * N ^ 2) = (K / (2 * N) * r) * (K / (6 * N)) := by
      field_simp; ring
    rw [e]
    refine mul_lt_of_lt_one_right (by positivity) ?_
    rw [div_lt_one (by positivity)]; linarith
  · rw [hα', div_le_one (by positivity)]; exact hKN
  · have hRd : R * d = K ^ 3 * r / 12 := by rw [hK3]; field_simp
    rw [hsq, h56, hδ', hα', hRd, ← hN6]
    apply le_of_eq
    field_simp
    ring

theorem solution {d : ℕ} (hd : 1 ≤ d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    (r R : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (hSR : S ⊆ Metric.closedBall 0 R)
    (C : ℝ) (hC : 0 < C) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hum : ∀ t, Measurable (u t))
    (hind : ProbabilityTheory.iIndepFun u P)
    (hlaw : ∀ t, P.map (u t) = RegretBandits.Nonlinear.uniformSphere d)
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (hn : (3 * R * d / (2 * r)) ^ 2 ≤ (n : ℝ))
    (ν δ α : ℝ) (hν : ν = R / (C * Real.sqrt n))
    (hδ : δ = (r * R ^ 2 * d ^ 2 / (12 * n)) ^ ((1 : ℝ) / 3))
    (hα : α = (3 * R * d / (2 * r * Real.sqrt n)) ^ ((1 : ℝ) / 3))
    (hrun : ∀ ω, BanditGD.Regret.IsBGDRun S α δ ν c (fun t => u t ω) (fun t => y t ω)) :
    RegretBandits.Nonlinear.pseudoRegret S c P (fun t ω => y t ω + δ • u t ω) n
      ≤ 3 * C * (n : ℝ) ^ ((5 : ℝ) / 6) * (12 * d * R / r) ^ ((1 : ℝ) / 3) := by
  have hR : 0 < R := by
    let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single (⟨0, hd⟩ : Fin d) r
    have he : ‖e‖ = r := by simp [e, abs_of_pos hr]
    have hmem : e ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R :=
      hSR (hrS (by simp [he]))
    have : ‖e‖ ≤ R := by simpa using hmem
    linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hn1, hδ0, hδα, hα1, hb⟩ := bgd_param_algebra r R d C n hr hR hd' hC hn δ α hδ hα
  exact (BanditGD.Regret.eq_10 hd S hSconv hSclosed r R hr hrS hSR C hC c hcconv hcbdd P u hum
    hind hlaw y n hn1 ν δ α hν hδ0 hδα hα1 hrun).trans hb
