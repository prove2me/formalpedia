-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.eligible_high_credit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:40.055805+00:00
-- url     : https://prove2.me/submissions/c61d3236-2b82-495e-8a7e-1623442ce1bd

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

section

noncomputable section

namespace ConsistentSubmodular

namespace LowRollback

variable {m aCount : ℕ}

theorem parent_floor_of_attainment (k d₀ d p W : ℝ)
    (hk4 : k ≤ 4) (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hp : W + d₀ ≤ p) : 0 ≤ parentFloor k d₀ d p := by
  have heq : parentFloor k d₀ d p = (4 - k) * (p - W - d₀) := by
    unfold parentFloor
    nlinarith only [hatt]
  rw [heq]
  exact mul_nonneg (sub_nonneg.mpr hk4) (by linarith)

end LowRollback

end ConsistentSubmodular

end

end

section

namespace ConsistentSubmodular.LowRollback

theorem child_linear_floor (q d p : ℝ)
    (_hq : 0 ≤ q) (hq1 : q ≤ 1) (hp : 3 / 10 ≤ p) (hp5 : p ≤ 5 / 4)
    (hchild : 0 ≤ cpoly q * d - npoly q - apoly q * p) :
    0 ≤ d - 3 / 16 - p / 20 := by
  have hs : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hc : 0 < cpoly q := by
    have h1 : 0 ≤ 25 * (1 - q) + 8 * (1 - q) ^ 2 + (1 - q) ^ 3 := by positivity
    unfold cpoly
    nlinarith only [h1]
  let B := fun p : ℝ => cpoly q * (3 / 16 + p / 20) - npoly q - apoly q * p
  have hJ : 0 ≤ 912 - 2356 * q + 1789 * q ^ 2 - 319 * q ^ 3 := by
    have hcube := mul_nonpos_of_nonpos_of_nonneg
      (show q - 1 ≤ 0 by linarith) (sq_nonneg (q - 1))
    nlinarith [sq_nonneg (1664 * (q - 1) + 265)]
  have hB0 : B (3 / 10) ≤ 0 := by
    dsimp [B, cpoly, npoly, apoly]
    nlinarith only [hJ]
  have hB1 : B (5 / 4) ≤ 0 := by
    have := mul_nonneg (sq_nonneg q) (show 0 ≤ 4 - q by linarith)
    dsimp [B, cpoly, npoly, apoly]
    nlinarith only [this]
  have hB : B p ≤ 0 := by
    have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp5) hB0
    have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp) hB1
    dsimp [B] at *
    nlinarith only [h1, h2]
  have hid : cpoly q * d - npoly q - apoly q * p =
      cpoly q * (d - 3 / 16 - p / 20) + B p := by dsimp [B]; ring
  nlinarith only [hchild, hid, hB, hc]

theorem eligible_high_polynomials (k : ℝ) (hk : 20 / 11 ≤ k) (hk5 : k ≤ 5 / 2) :
    0 < k ^ 2 - 44 * k + 184 ∧ 0 < k ^ 2 - k + 3 ∧
      0 < -19 * k ^ 3 - 91 * k ^ 2 + 1052 * k - 1440 ∧
      0 < 5 * k ^ 3 + 107 * k ^ 2 - 473 * k + 480 := by
  have hk0 : 0 ≤ k := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [sq_nonneg k]
  · nlinarith [sq_nonneg (k - 1 / 2)]
  · have hsq := mul_nonneg (show 0 ≤ 5 / 2 - k by linarith)
      (show 0 ≤ 5 / 2 + k by linarith)
    have hc : 0 ≤ -19 * (k ^ 2 + (20 / 11 : ℝ) * k + (20 / 11 : ℝ) ^ 2) -
        91 * (k + 20 / 11) + 1052 := by nlinarith
    have := mul_nonneg (sub_nonneg.mpr hk) hc
    nlinarith only [this]
  · have h1 := mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg (k - 2))
    nlinarith [sq_nonneg ((2994 / 11 : ℝ) * (k - 2) + 15)]

end ConsistentSubmodular.LowRollback

end

section

open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (k q d₀ d p W : ℝ)
    (hk : 20 / 11 ≤ k) (hk3 : k < 3) (hq : 0 < q) (hq1 : q ≤ 1)
    (hd₀ : 0 ≤ d₀) (hd₀d : d₀ ≤ d) (hd : 319 / 1600 ≤ d) (hd4 : d ≤ 1 / 4)
    (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hpW : W + d₀ ≤ p) (hpC : p ≤ ceiling k d₀)
    (hchild : 0 ≤ cpoly q * d - npoly q - apoly q * p) :
    0 < U k d₀ d p W := by
  have hk0 : 0 < k := by linarith
  have h3 : 0 < 3 - k := by linarith
  have h4 : 0 < 4 - k := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hF1 := parent_floor_of_attainment k d₀ d p W (by linarith) hatt hpW
  have hDterm := mul_nonneg h4.le hd₀
  have hp3 : 3 / 10 ≤ p := by
    by_contra hn
    have h1 := mul_nonpos_of_nonneg_of_nonpos h3.le (show p - 3 / 10 ≤ 0 by linarith)
    have h2 := mul_nonneg hk0.le (sub_nonneg.mpr hd)
    unfold parentFloor at hF1
    nlinarith
  have hp5 : p ≤ 5 / 4 := by
    have hprod := mul_nonneg h4.le (show 0 ≤ 1 / 4 - d₀ by linarith)
    have hid : k * (5 / 4 - ceiling k d₀) = 3 * (4 - k) * (1 / 4 - d₀) := by
      unfold ceiling
      field_simp
      ring
    nlinarith
  have hF2 := child_linear_floor q d p hq.le hq1 hp3 hp5 hchild
  have hcombined : (15 / 4 : ℝ) * (3 - k) + 2 * (4 - k) * d₀ ≤ (60 - 21 * k) * d := by
    have hmul := mul_nonneg h3.le hF2
    unfold parentFloor at hF1
    nlinarith
  have hcoef : 0 < 60 - 21 * k := by
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hd0
    nlinarith
  have hk5 : k ≤ 5 / 2 := by
    have := mul_nonneg hcoef.le (sub_nonneg.mpr hd4)
    nlinarith
  have h7 : 0 < 20 - 7 * k := by linarith
  obtain ⟨hA, hB, hG, hF⟩ := eligible_high_polynomials k hk hk5
  have hW : W = (p + k * d + (4 - k) * d₀) / (4 - k) := by
    apply (eq_div_iff (ne_of_gt h4)).mpr
    nlinarith only [hatt]
  have hid : 12 * k * (4 - k) * (20 - 7 * k) * U k d₀ d p W =
      4 * k * (k ^ 2 - 44 * k + 184) * parentFloor k d₀ d p +
      80 * k * (4 - k) * (k ^ 2 - k + 3) * (d - 3 / 16 - p / 20) +
      4 * (4 - k) * (-19 * k ^ 3 - 91 * k ^ 2 + 1052 * k - 1440) * d₀ +
      3 * (4 - k) * (5 * k ^ 3 + 107 * k ^ 2 - 473 * k + 480) := by
    rw [hW]
    unfold U ceiling parentFloor
    field_simp
    ring
  have h1 : 0 ≤ 4 * k * (k ^ 2 - 44 * k + 184) * parentFloor k d₀ d p := by positivity
  have h2 : 0 ≤ 80 * k * (4 - k) * (k ^ 2 - k + 3) * (d - 3 / 16 - p / 20) := by positivity
  have h3' : 0 ≤ 4 * (4 - k) * (-19 * k ^ 3 - 91 * k ^ 2 + 1052 * k - 1440) * d₀ := by positivity
  have h4' : 0 < 3 * (4 - k) * (5 * k ^ 3 + 107 * k ^ 2 - 473 * k + 480) := by positivity
  have hden : 0 < 12 * k * (4 - k) * (20 - 7 * k) := by positivity
  nlinarith only [hid, h1, h2, h3', h4', hden]

end
