-- Prove2me | solution 1 for CosmoConstCentury.critical_density_classification
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:36:25.733401+00:00
-- url     : https://prove2.me/submissions/793a2835-9562-4bb5-bdab-eef0b7a68a50

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace CosmoConstCentury

theorem p50abfc67_key (G c k : ℝ) (hG : 0 < G) (hc : 0 < c) (I : Set ℝ)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c 0 k I R ρ) (t : ℝ) (ht : t ∈ I) :
    ρ t - criticalDensity G (hubbleParam R t)
      = (3 * k * c ^ 2) / (R t ^ 2 * (8 * Real.pi * G)) := by
  obtain ⟨hR, -, h1, -⟩ := hsol t ht
  unfold criticalDensity hubbleParam
  unfold einsteinKappa at h1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hR2 : R t ^ 2 ≠ 0 := by positivity
  have hc2 : c ^ 2 ≠ 0 := by positivity
  have ha : 8 * Real.pi * G ≠ 0 := by positivity
  have hρ : ρ t = (3 * deriv R t ^ 2 / R t ^ 2 + 3 * k * c ^ 2 / R t ^ 2) / (8 * Real.pi * G) := by
    rw [eq_div_iff ha]
    have : 8 * Real.pi * G / c ^ 2 * c ^ 2 * ρ t = ρ t * (8 * Real.pi * G) := by
      field_simp
    rw [← this, ← h1]; ring
  rw [hρ, div_pow]
  field_simp
  ring

end CosmoConstCentury

open CosmoConstCentury in
theorem solution (G c k : ℝ) (hG : 0 < G) (hc : 0 < c) (I : Set ℝ)
    (R ρ : ℝ → ℝ) (hsol : IsFriedmannSolution G c 0 k I R ρ) (t : ℝ) (ht : t ∈ I) :
    (0 < k ↔ criticalDensity G (hubbleParam R t) < ρ t) ∧
    (k = 0 ↔ ρ t = criticalDensity G (hubbleParam R t)) ∧
    (k < 0 ↔ ρ t < criticalDensity G (hubbleParam R t)) := by
  have key := p50abfc67_key G c k hG hc I R ρ hsol t ht
  obtain ⟨hR, -⟩ := hsol t ht
  have hpi : 0 < Real.pi := Real.pi_pos
  have hD : 0 < R t ^ 2 * (8 * Real.pi * G) := by positivity
  have hc2 : 0 < 3 * c ^ 2 := by positivity
  set d := ρ t - criticalDensity G (hubbleParam R t) with hd
  have hP : 0 < 3 * c ^ 2 / (R t ^ 2 * (8 * Real.pi * G)) := div_pos hc2 hD
  set P := 3 * c ^ 2 / (R t ^ 2 * (8 * Real.pi * G)) with hPdef
  have hdk : d = k * P := by
    rw [key, hPdef]; ring
  refine ⟨⟨fun hk => ?_, fun h => ?_⟩, ⟨fun hk => ?_, fun h => ?_⟩, ⟨fun hk => ?_, fun h => ?_⟩⟩
  · have : 0 < d := by rw [hdk]; exact mul_pos hk hP
    linarith
  · have : 0 < d := by linarith
    rw [hdk] at this
    exact (pos_iff_pos_of_mul_pos this).mpr hP
  · have : d = 0 := by rw [hdk, hk, zero_mul]
    linarith
  · have : d = 0 := by linarith
    rw [hdk] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hP)
  · have : d < 0 := by rw [hdk]; exact mul_neg_of_neg_of_pos hk hP
    linarith
  · have : d < 0 := by linarith
    rw [hdk] at this
    by_contra hn
    have : 0 ≤ k * P := mul_nonneg (not_lt.mp hn) hP.le
    linarith
