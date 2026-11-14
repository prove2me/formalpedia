-- Prove2me | solution 1 for ConsistentSubmodular.fourThirds_low_baseline_relay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:06.798004+00:00
-- url     : https://prove2.me/submissions/d5b71dec-b31c-4a6c-94bb-3ed079d46284

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_FourThirdsBoundary
import Theorems.Thm_ConsistentSubmodular_fourThirds_boundary_edge

section

namespace ConsistentSubmodular

variable (H P c α β L G R y A δ w q d d₀ kpar u z T Pt g a η n b : ℝ)

theorem quadratic_overlap_bound (x : ℝ) : x * (1 - x) ≤ (1 : ℝ) / 4 := by
  nlinarith [sq_nonneg (x - (1 : ℝ) / 2)]

end ConsistentSubmodular

end

section

open ConsistentSubmodular

theorem solution (p d q δ w b z : ℝ)
    (hp : 0 < p) (hp2 : p ≤ 1 / 2) (hdlow : p / 2 ≤ d) (hd4 : d < 1 / 4)
    (hcredit : d ≤ p * (1 - p)) (hq : (4 : ℝ) / 3 ≤ q) (hq2 : q ≤ 2)
    (hδ : 0 ≤ δ) (hb : p + d ≤ b)
    (hratio : (3 - q) * w = q * δ + b + 3 * d)
    (hfail : b + w < 2 * (1 - d) - 3 * (1 - 4 * d) / q)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < 1 / 4 - d - δ * z - (1 - d - δ - w) * z * (1 - z) := by
  let L := p + d
  let W := fourThirdsBoundaryWeight p d q
  let E := fourThirdsBoundaryDelta p d q
  let w₀ := (L + 3 * d) / (3 - q)
  let J₀ := 1 / 4 - d - (1 - d - w₀) * z * (1 - z)
  let Jstar := 1 / 4 - d - E * z - (1 - d - E - W) * z * (1 - z)
  let J := 1 / 4 - d - δ * z - (1 - d - δ - w) * z * (1 - z)
  have hqpos : 0 < q := by linarith
  have hq0 : q ≠ 0 := ne_of_gt hqpos
  have h3pos : 0 < 3 - q := by linarith
  have h30 : 3 - q ≠ 0 := ne_of_gt h3pos
  have hd : 0 ≤ d := by linarith
  have hL : 2 * d < L := by
    dsimp [L]
    nlinarith [sq_pos_of_pos hp]
  have hbL : 0 ≤ b - L := sub_nonneg.mpr hb
  have hstar : (3 - q) * W = q * E + L + 3 * d := by
    dsimp [E, fourThirdsBoundaryDelta, W, L]
    field_simp
    ring
  have hzero : (3 - q) * w₀ = L + 3 * d := by
    dsimp [w₀]
    field_simp
  have hfail' : b + w < W + L := by
    dsimp [W, fourThirdsBoundaryWeight, L]
    linarith
  have hδE : δ < E := by
    have h1 := mul_lt_mul_of_pos_left hfail' h3pos
    have h2 := mul_nonneg (show 0 ≤ 4 - q by linarith) hbL
    have hqδ : q * δ < q * E := by nlinarith only [h1, h2, hratio, hstar]
    by_contra hn
    have := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hqpos.le
    linarith
  have hE : 0 < E := lt_of_le_of_lt hδ hδE
  have hw₀ : 3 * d < w₀ := by
    apply (lt_div_iff₀ h3pos).2
    have := mul_nonneg (sub_nonneg.mpr hq) hd
    nlinarith
  have hJ₀ : 0 < J₀ := by
    dsimp [J₀]
    by_cases ho : 0 ≤ 1 - d - w₀
    · have hquad := mul_le_mul_of_nonneg_left (quadratic_overlap_bound z) ho
      nlinarith
    · have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ho)
        (mul_nonneg hz (sub_nonneg.mpr hz1))
      nlinarith
  have hJstar : 0 ≤ Jstar :=
    fourThirds_boundary_edge p d q z hp.le hp2 hdlow hd4 hcredit hq hz hz1
  have hid : (3 - q) * E * J =
      (3 - q) * (E - δ) * J₀ + (3 - q) * δ * Jstar +
        E * (b - L) * z * (1 - z) := by
    dsimp [J, J₀, Jstar]
    linear_combination (E * z * (1 - z)) * hratio - (δ * z * (1 - z)) * hstar -
      ((E - δ) * z * (1 - z)) * hzero
  have hterm1 : 0 < (3 - q) * (E - δ) * J₀ :=
    mul_pos (mul_pos h3pos (sub_pos.mpr hδE)) hJ₀
  have hterm2 : 0 ≤ (3 - q) * δ * Jstar :=
    mul_nonneg (mul_nonneg h3pos.le hδ) hJstar
  have hterm3 : 0 ≤ E * (b - L) * z * (1 - z) :=
    mul_nonneg (mul_nonneg (mul_nonneg hE.le hbL) hz) (sub_nonneg.mpr hz1)
  have hpositive : 0 < ((3 - q) * E) * J := by linarith only [hid, hterm1, hterm2, hterm3]
  exact (mul_pos_iff_of_pos_left (mul_pos h3pos hE)).mp hpositive

end
