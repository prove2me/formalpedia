-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.floor_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:49:44.957861+00:00
-- url     : https://prove2.me/submissions/59c445ad-efdd-47ea-8a2e-a03edb5fbbbb

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_lt_one
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_A_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_floorJ_bound
section
namespace FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
namespace Normalized
private theorem floorR_lower
    {K e u v : ℝ}
    (hK : 1 ≤ K) (he0 : 0 ≤ e)
    (hEll0 : 0 ≤ floorEll u v K)
    (hEll1 : floorEll u v K ≤ 1)
    (hW0 : 0 ≤ floorW u v K)
    (hWUpper : floorW u v K ≤ (K + 1) / (2 * K))
    (hEta : (K + e) / (16 + K + e) ≤ floorEta u v) :
    (K ^ 2 + e ^ 2) / 384 ≤ floorR K e u v := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hQpos : 0 < 16 + K + e := by linarith
  by_cases hcase : K / 2 ≤ e * floorEta u v
  · have hinner :
        0 ≤ e * floorEta u v -
          (K - 1 + floorEll u v K) / 2 := by
      have : K - 1 + floorEll u v K ≤ K := by linarith
      linarith
    have hsecond :
        0 ≤ floorW u v K / 2 *
          (e * floorEta u v -
            (K - 1 + floorEll u v K) / 2) := by
      positivity
    have hfirst :
        (4 * K ^ 2 + 6 * K + e ^ 2) / 96 ≤
          (5 * K ^ 2 + 12 * K + 9 + 2 * e ^ 2 -
            2 * K * e - 6 * e) / 96 := by
      nlinarith [sq_nonneg (K + 3 - e)]
    unfold floorR
    nlinarith [sq_nonneg K, sq_nonneg e]
  · have hcase' :
        e * floorEta u v - K / 2 < 0 := by linarith
    have hinner :
        e * floorEta u v - K / 2 ≤
          e * floorEta u v -
            (K - 1 + floorEll u v K) / 2 := by
      linarith
    have hfirstProduct :
        floorW u v K / 2 *
              (e * floorEta u v - K / 2) ≤
          floorW u v K / 2 *
              (e * floorEta u v -
                (K - 1 + floorEll u v K) / 2) :=
      mul_le_mul_of_nonneg_left hinner (by positivity)
    have hupperNonneg : 0 ≤ (K + 1) / (4 * K) := by positivity
    have hWdiv :
        floorW u v K / 2 ≤ (K + 1) / (4 * K) := by
      calc
        floorW u v K / 2 ≤ ((K + 1) / (2 * K)) / 2 :=
          div_le_div_of_nonneg_right hWUpper (by norm_num)
        _ = (K + 1) / (4 * K) := by ring
    have hsecondProduct :
        (K + 1) / (4 * K) *
              (e * floorEta u v - K / 2) ≤
          floorW u v K / 2 *
              (e * floorEta u v - K / 2) := by
      exact mul_le_mul_of_nonpos_right hWdiv hcase'.le
    have hEtaMul :
        e * ((K + e) / (16 + K + e)) ≤
          e * floorEta u v :=
      mul_le_mul_of_nonneg_left hEta he0
    have hthirdProduct :
        (K + 1) / (4 * K) *
              (e * ((K + e) / (16 + K + e)) - K / 2) ≤
          (K + 1) / (4 * K) *
              (e * floorEta u v - K / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hupperNonneg
    have hJidentity :
        (5 * K ^ 2 + 12 * K + 9 + 2 * e ^ 2 -
              2 * K * e - 6 * e) / 96 +
            (K + 1) / (4 * K) *
              (e * ((K + e) / (16 + K + e)) - K / 2) =
          floorJ K e / 96 := by
      unfold floorJ
      field_simp [hKpos.ne', hQpos.ne']
      ring
    have hRge :
        floorJ K e / 96 ≤ floorR K e u v := by
      unfold floorR
      rw [← hJidentity]
      linarith
    have hJ := floorJ_bound hK he0
    calc
      (K ^ 2 + e ^ 2) / 384 ≤ floorJ K e / 96 := by
        linarith
      _ ≤ floorR K e u v := hRge
private theorem floor_rate_bound
    {K e u v : ℝ}
    (hK : 1 ≤ K) (he0 : 0 ≤ e)
    (hEll0 : 0 ≤ floorEll u v K)
    (hEll1 : floorEll u v K ≤ 1) :
    (floorEll u v K ^ 2 + ((K + 1) / 2) ^ 2) / 2 - 1 +
        ((K + e) / 2) ^ 2 ≤
      K ^ 2 + e ^ 2 := by
  have hEllSq : floorEll u v K ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (1 - floorEll u v K)]
  have hKSq : ((K + 1) / 2) ^ 2 ≤ K ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hK)
      (by linarith : 0 ≤ 3 * K + 1)]
  have hsumSq :
      ((K + e) / 2) ^ 2 ≤ (K ^ 2 + e ^ 2) / 2 := by
    nlinarith [sq_nonneg (K - e)]
  nlinarith [sq_nonneg e]
private theorem floor_coordinate_bounds
    {K e u v : ℝ}
    (hK : 1 ≤ K) (he0 : 0 ≤ e) (hu : 0 < u)
    (hrel : v = K * (u + 1) + e)
    (hfeedback : (K + e) * u * v ≤ 4 * (v ^ 2 - u ^ 2)) :
    0 < floorEll u v K ∧ floorEll u v K ≤ 1 ∧
      0 < floorW u v K ∧ floorW u v K ≤ (K + 1) / (2 * K) ∧
      (K + e) / (16 + K + e) ≤ floorEta u v := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hv : 0 < v := by rw [hrel]; positivity
  have huv : u ≤ v := by
    rw [hrel]
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) hu.le]
  have hKminus : 0 ≤ K - 1 := sub_nonneg.mpr hK
  have hEll1 : floorEll u v K ≤ 1 := by
    unfold floorEll
    have : 0 ≤ u * (K - 1) / (2 * v) := by positivity
    linarith
  have hEll0 : 0 < floorEll u v K := by
    have hnum : u * (K - 1) < 2 * v := by
      rw [hrel]
      nlinarith [mul_pos hKpos hu]
    unfold floorEll
    apply sub_pos.mpr
    exact (div_lt_one (by positivity : 0 < 2 * v)).2 hnum
  have hW0 : 0 < floorW u v K := by
    unfold floorW
    positivity
  have hWUpper : floorW u v K ≤ (K + 1) / (2 * K) := by
    have hden : 0 < 2 * (v + 1) := by positivity
    have hdenK : 0 < 2 * K := by positivity
    unfold floorW
    apply (div_le_div_iff₀ hden hdenK).2
    rw [hrel]
    nlinarith [mul_nonneg (by linarith : 0 ≤ K + 1)
      (by linarith : 0 ≤ e + 1)]
  have hdiff : 0 ≤ v - u := sub_nonneg.mpr huv
  have hQ : 0 < K + e := by linarith
  have hQden : 0 < 16 + K + e := by linarith
  have hvu : 0 < v + u := by positivity
  have hetaDen : 0 < v + 1 + u := by positivity
  have hfactor :
      4 * (v ^ 2 - u ^ 2) ≤ 8 * (v - u) * v := by
    nlinarith [sq_nonneg (v - u)]
  have hcancel :
      (K + e) * u ≤ 8 * (v - u) := by
    have hmul :
        (K + e) * u * v ≤ 8 * (v - u) * v :=
      hfeedback.trans hfactor
    exact (mul_le_mul_iff_of_pos_right hv).mp (by
      convert hmul using 1 <;> ring)
  have hc :
      (K + e) / (16 + K + e) ≤ (v - u) / (v + u) := by
    apply (div_le_div_iff₀ hQden hvu).2
    nlinarith
  have heta :
      (v - u) / (v + u) ≤ floorEta u v := by
    unfold floorEta
    apply (div_le_div_iff₀ hvu hetaDen).2
    nlinarith
  exact ⟨hEll0, hEll1, hW0, hWUpper, hc.trans heta⟩
private theorem floorU_pos
    {s ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    0 < floorU s ρ := by
  unfold floorU
  positivity
private theorem floorV_pos
    {s ρ : ℝ} (hs : 0 < s) (hρ0 : 0 ≤ ρ) :
    0 < floorV s ρ := by
  unfold floorV
  positivity
private theorem floor_relation
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    floorV s ρ =
      floorK s r ρ * (floorU s ρ + 1) + floorE r := by
  have hu := floorU_pos hs hρ1
  unfold floorK
  field_simp [(by positivity : 0 < floorU s ρ + 1).ne']
  ring
private theorem floorCap_eq_coordinates
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    floorCap s r ρ = (floorK s r ρ + floorE r) / 2 := by
  have hu := floorU_pos hs hρ1
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold floorCap floorK floorE floorU floorV
  field_simp [hden.ne']
  ring
private theorem floor_hMinus_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    hMinus s ρ (floorCap s r ρ) =
      (floorK s r ρ + 1) / 2 := by
  have hu := floorU_pos hs hρ1
  have hrho : 1 - ρ ≠ 0 := by linarith
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold hMinus floorCap floorK floorE floorU floorV
  field_simp [hs.ne', hrho, hden.ne']
  ring
private theorem floor_hPlus_eq
    {s r ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    hPlus s ρ (floorCap s r ρ) =
      floorEll (floorU s ρ) (floorV s ρ) (floorK s r ρ) := by
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0
  have hrhop : 1 + ρ ≠ 0 := by linarith
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold hPlus floorCap floorEll floorK floorE floorU floorV
  field_simp [hs.ne', hrhop, hden.ne', hv.ne']
  ring
private theorem floor_ZMinus_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    ZMinus s r ρ = (floorK s r ρ + 1) / 2 := by
  have hu := floorU_pos hs hρ1
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold ZMinus g floorK floorE floorU floorV
  field_simp [hden.ne']
  ring
private theorem floor_ZPlus_eq
    {s r ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ZPlus s r ρ =
      floorW (floorU s ρ) (floorV s ρ) (floorK s r ρ) := by
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0
  have hdenU : 0 < s * (1 - ρ) + 1 := by positivity
  have hdenV : 0 < s * (1 + ρ) + 1 := by positivity
  unfold ZPlus g floorW floorK floorE floorU floorV
  field_simp [hdenU.ne', hdenV.ne']
  ring
private theorem floor_tPlus_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    tPlus r (floorCap s r ρ) =
      -(2 * floorE r + floorK s r ρ - 1) / 4 := by
  have hu := floorU_pos hs hρ1
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold tPlus floorCap floorK floorE floorU floorV
  field_simp [hden.ne']
  ring
private theorem floor_tMinus_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    tMinus r (floorCap s r ρ) =
      (floorK s r ρ + 1) / 4 := by
  have hu := floorU_pos hs hρ1
  have hden : 0 < s * (1 - ρ) + 1 := by positivity
  unfold tMinus floorCap floorK floorE floorU floorV
  field_simp [hden.ne']
  ring
private theorem floor_ZParent_eq
    {s r ρ : ℝ} (hs : 0 < s) (hρ1 : ρ < 1) :
    ZParent s r =
      (floorK s r ρ + 1) * (floorU s ρ + 1) /
        (floorU s ρ + floorV s ρ + 1) := by
  have hu := floorU_pos hs hρ1
  have hdenParent : 0 < s + 1 / 2 := by linarith
  have hdenTwo : 0 < 2 * s + 1 := by linarith
  have hrel := floor_relation (r := r) hs hρ1
  have hkterm :
      floorK s r ρ * (floorU s ρ + 1) =
        floorV s ρ - floorE r := by linarith
  have hsum :
      floorU s ρ + floorV s ρ = 2 * s := by
    unfold floorU floorV
    ring
  have hnum :
      (floorK s r ρ + 1) * (floorU s ρ + 1) =
        2 * (s + r) := by
    rw [show (floorK s r ρ + 1) * (floorU s ρ + 1) =
      floorK s r ρ * (floorU s ρ + 1) +
        floorU s ρ + 1 by ring, hkterm]
    unfold floorE floorU floorV
    ring
  unfold ZParent g
  rw [hnum, hsum]
  field_simp [hdenParent.ne', hdenTwo.ne']
set_option maxHeartbeats 600000 in
private theorem floor_residual_algebra
    {K e u v r : ℝ}
    (hu : 0 < u) (hv : 0 < v)
    (hrel : v = K * (u + 1) + e)
    (hr : r = (1 - e) / 2) :
    ((-(2 * e + K - 1) / 4 * floorW u v K +
          bellman (floorEll u v K) (-(2 * e + K - 1) / 4)
            (floorW u v K)) +
        ((K + 1) / 4 * ((K + 1) / 2) +
          bellman ((K + 1) / 2) ((K + 1) / 4) ((K + 1) / 2))) / 2 -
      bellman 1 r
        ((K + 1) * (u + 1) / (u + v + 1)) =
      floorR K e u v := by
  subst r
  subst v
  unfold floorR bellman floorEta floorW floorEll
  field_simp [hu.ne', hv.ne']
  ring
set_option maxHeartbeats 600000 in
private theorem floor_residual_eq
    {s r ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    residual s r ρ (floorCap s r ρ) =
      floorR (floorK s r ρ) (floorE r) (floorU s ρ) (floorV s ρ) := by
  rw [residual, floor_hPlus_eq hs hρ0 hρ1,
    floor_hMinus_eq hs hρ1, floor_tPlus_eq hs hρ1,
    floor_tMinus_eq hs hρ1, floor_ZPlus_eq hs hρ0 hρ1,
    floor_ZMinus_eq hs hρ1, floor_ZParent_eq hs hρ1]
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0
  have hrel := floor_relation (r := r) hs hρ1
  have hr : r = (1 - floorE r) / 2 := by
    unfold floorE
    ring
  exact floor_residual_algebra hu hv hrel hr
private theorem floor_rateIncrement_eq
    {s r ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    rateIncrement s ρ (floorCap s r ρ) =
      (floorEll (floorU s ρ) (floorV s ρ) (floorK s r ρ) ^ 2 +
        ((floorK s r ρ + 1) / 2) ^ 2) / 2 - 1 := by
  rw [rateIncrement, floor_hPlus_eq hs hρ0 hρ1,
    floor_hMinus_eq hs hρ1]
private theorem feedback_eq_floor_coordinates
    {s ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    feedback s ρ =
      2 * (floorV s ρ ^ 2 - floorU s ρ ^ 2) /
        (floorU s ρ * floorV s ρ) := by
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0.le
  have hA := A_pos hs hρ0.le hρ1
  have hsq : 0 < 1 - ρ ^ 2 := sub_pos.mpr (lambda_lt_one hρ0.le hρ1)
  have hrhom : 1 - ρ ≠ 0 := by linarith
  have hrhop : 1 + ρ ≠ 0 := by linarith
  unfold feedback A lambda floorU floorV
  field_simp [hs.ne', hsq.ne', hrhom, hrhop]
  ring
private theorem uniform_eq_floor_coordinates
    (s ρ : ℝ) :
    uniform s ρ = (floorV s ρ - floorU s ρ) / 2 := by
  unfold uniform floorU floorV
  ring
end Normalized
end
end FD1D.V5.LocalBellman
end

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
set_option maxHeartbeats 600000
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hactiveU : floorCap s r ρ ≤ uniform s ρ)
    (hactiveF : floorCap s r ρ ≤ feedback s ρ) :
    residual s r ρ (floorCap s r ρ) ≥
      (rateIncrement s ρ (floorCap s r ρ) + floorCap s r ρ ^ 2) /
        1000 := by
  have hu := floorU_pos hs hρ1
  have hv := floorV_pos hs hρ0.le
  have he0 : 0 ≤ floorE r := by
    unfold floorE
    linarith
  have hrel := floor_relation (r := r) hs hρ1
  have hactiveU' :
      (floorK s r ρ + floorE r) / 2 ≤
        (floorV s ρ - floorU s ρ) / 2 := by
    rw [← floorCap_eq_coordinates hs hρ1,
      ← uniform_eq_floor_coordinates]
    exact hactiveU
  have hprod :
      0 ≤ (floorK s r ρ - 1) * floorU s ρ := by
    nlinarith
  have hK : 1 ≤ floorK s r ρ := by
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hprod hu)
  have hactiveF' :
      (floorK s r ρ + floorE r) / 2 ≤
        2 * (floorV s ρ ^ 2 - floorU s ρ ^ 2) /
          (floorU s ρ * floorV s ρ) := by
    rw [← floorCap_eq_coordinates hs hρ1,
      ← feedback_eq_floor_coordinates hs hρ0 hρ1]
    exact hactiveF
  have hfeedback :
      (floorK s r ρ + floorE r) * floorU s ρ * floorV s ρ ≤
        4 * (floorV s ρ ^ 2 - floorU s ρ ^ 2) := by
    have huv : 0 < floorU s ρ * floorV s ρ := mul_pos hu hv
    have hmul := (le_div_iff₀ huv).1 hactiveF'
    nlinarith
  obtain ⟨hEll0, hEll1, hW0, hWUpper, hEta⟩ :=
    floor_coordinate_bounds hK he0 hu hrel hfeedback
  have hResidual :=
    floorR_lower hK he0 hEll0.le hEll1 hW0.le hWUpper hEta
  have hRate :=
    floor_rate_bound hK he0 hEll0.le hEll1
  have hResidual' :
      (floorK s r ρ ^ 2 + floorE r ^ 2) / 384 ≤
        residual s r ρ (floorCap s r ρ) := by
    rw [floor_residual_eq hs hρ0.le hρ1]
    exact hResidual
  have hRate' :
      rateIncrement s ρ (floorCap s r ρ) + floorCap s r ρ ^ 2 ≤
        floorK s r ρ ^ 2 + floorE r ^ 2 := by
    rw [floor_rateIncrement_eq hs hρ0.le hρ1,
      floorCap_eq_coordinates hs hρ1]
    exact hRate
  have henergy :
      0 ≤ floorK s r ρ ^ 2 + floorE r ^ 2 := by positivity
  calc
    (rateIncrement s ρ (floorCap s r ρ) + floorCap s r ρ ^ 2) /
          1000
        ≤ (floorK s r ρ ^ 2 + floorE r ^ 2) / 1000 := by
          exact div_le_div_of_nonneg_right hRate' (by norm_num)
    _ ≤ (floorK s r ρ ^ 2 + floorE r ^ 2) / 384 := by
          nlinarith
    _ ≤ residual s r ρ (floorCap s r ρ) := hResidual'
end FD1D.V5.LocalBellman.Normalized
