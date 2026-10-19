-- Prove2me | solution 1 for CohnElkies.saddleSource_scaled_cubic_window_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/d940d67e-1583-4241-9746-810d253c4b62

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ η V M K c z T : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (hc : 0 < c)
    (hK : 0 ≤ K) (hz : 0 ≤ z)
    (hmoment : η ^ 2 * M ≤ K)
    (hvariance : c ≤ η * V)
    (hT : |T| ≤ z / Real.sqrt (ℓ * V)) :
    (ℓ * M / 6) * |T| ^ 3 ≤
      (K / (6 * c * Real.sqrt c)) *
        (z ^ 3 / Real.sqrt (ℓ * η)) := by
  have hV : 0 < V := by
    nlinarith [hvariance, mul_pos hη hc]
  have hs : 0 < Real.sqrt (ℓ * V) :=
    Real.sqrt_pos.2 (mul_pos hℓ hV)
  have ht : 0 < Real.sqrt (ℓ * η) :=
    Real.sqrt_pos.2 (mul_pos hℓ hη)
  have hw : 0 < Real.sqrt (η * V) :=
    Real.sqrt_pos.2 (mul_pos hη hV)
  have hcroot : 0 < Real.sqrt c :=
    Real.sqrt_pos.2 hc
  have hm : M ≤ K / η ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hη)).2
    nlinarith
  have hcross :
      Real.sqrt (ℓ * V) * η =
        Real.sqrt (ℓ * η) * Real.sqrt (η * V) := by
    have heq :
        (Real.sqrt (ℓ * V) * η) ^ 2 =
          (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) ^ 2 := by
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hℓ.le hV.le),
        Real.sq_sqrt (mul_nonneg hℓ.le hη.le),
        Real.sq_sqrt (mul_nonneg hη.le hV.le)]
      ring
    nlinarith [mul_pos hs hη,
      mul_pos ht hw]
  have hwlower : Real.sqrt c ≤ Real.sqrt (η * V) :=
    Real.sqrt_le_sqrt hvariance
  have hratio :
      ℓ * Real.sqrt (ℓ * η) *
          (Real.sqrt (η * V)) ^ 3 =
        η ^ 2 * (Real.sqrt (ℓ * V)) ^ 3 := by
    have htsquare :
        (Real.sqrt (ℓ * η)) ^ 2 = ℓ * η :=
      Real.sq_sqrt (mul_nonneg hℓ.le hη.le)
    calc
      ℓ * Real.sqrt (ℓ * η) *
          (Real.sqrt (η * V)) ^ 3 =
        (((Real.sqrt (ℓ * η)) ^ 2 / η) *
          Real.sqrt (ℓ * η) *
          (Real.sqrt (η * V)) ^ 3) := by
        rw [htsquare]
        field_simp [hη.ne']
      _ =
        (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) ^ 3 /
          η := by ring
      _ =
        (Real.sqrt (ℓ * V) * η) ^ 3 / η := by
        rw [hcross]
      _ = η ^ 2 * (Real.sqrt (ℓ * V)) ^ 3 := by
        field_simp [hη.ne']
  calc
    (ℓ * M / 6) * |T| ^ 3 ≤
        (ℓ * (K / η ^ 2) / 6) *
          (z / Real.sqrt (ℓ * V)) ^ 3 := by
      gcongr
    _ = (K / 6) * z ^ 3 /
        (Real.sqrt (ℓ * η) *
          (Real.sqrt (η * V)) ^ 3) := by
      field_simp [hη.ne', hs.ne', ht.ne', hw.ne']
      calc
        ℓ * K * z ^ 3 * Real.sqrt (ℓ * η) *
            (Real.sqrt (η * V)) ^ 3 =
          K * z ^ 3 *
            (ℓ * Real.sqrt (ℓ * η) *
              (Real.sqrt (η * V)) ^ 3) := by ring
        _ = K * z ^ 3 *
          (η ^ 2 * (Real.sqrt (ℓ * V)) ^ 3) := by
          rw [hratio]
        _ = K * η ^ 2 * z ^ 3 *
          (Real.sqrt (ℓ * V)) ^ 3 := by ring
    _ ≤ (K / 6) * z ^ 3 /
        (Real.sqrt (ℓ * η) *
          (Real.sqrt c) ^ 3) := by
      gcongr
    _ = (K / (6 * c * Real.sqrt c)) *
        (z ^ 3 / Real.sqrt (ℓ * η)) := by
      have hcsquare : (Real.sqrt c) ^ 2 = c :=
        Real.sq_sqrt hc.le
      field_simp [ht.ne', hc.ne', hcroot.ne']
      rw [hcsquare]
end CohnElkies
