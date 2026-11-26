-- Prove2me | solution 1 for FD1D.V5.LocalBellman.local_bellman_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:53:59.416867+00:00
-- url     : https://prove2.me/submissions/19e84495-239d-48e8-a7da-25ce03b529be

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_g_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_floorJ_bound
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_equal_case
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_threeCap_case
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_LocalPolicy_bias_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_discrepancyLeft_eq
import Theorems.Thm_FD1D_V5_LocalPolicy_discrepancyRight_eq
import Theorems.Thm_FD1D_V5_LocalPolicy_inventory_nonneg
import Theorems.Thm_FD1D_V5_LocalPolicy_inventory_pos
import Theorems.Thm_FD1D_V5_LocalPolicy_massLeft_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_massRight_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_parentMass_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_rateLeft_swap
import Theorems.Thm_FD1D_V5_LocalPolicy_rateRight_swap
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
namespace Normalized
private theorem weighted_square_bound
    {s r lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam * s ^ 2 / 21 ≤ r ^ 2 / 8 + lam * (s + r) ^ 2 / 13 := by
  let C : ℝ := 168 * lam + 273
  have hC : 0 < C := by dsimp [C]; nlinarith
  have hrem : 0 ≤ 69888 * lam * (1 - lam) * s ^ 2 := by positivity
  have hid :
      4 * C *
          (168 * lam * r ^ 2 + 336 * lam * r * s +
            64 * lam * s ^ 2 + 273 * r ^ 2) =
        (2 * C * r + 336 * lam * s) ^ 2 +
          69888 * lam * (1 - lam) * s ^ 2 := by
    dsimp [C]
    ring
  have hpoly :
      0 ≤ 168 * lam * r ^ 2 + 336 * lam * r * s +
        64 * lam * s ^ 2 + 273 * r ^ 2 := by
    nlinarith [sq_nonneg (2 * C * r + 336 * lam * s)]
  nlinarith
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
private theorem emptyResidual_uniform_eq
    {s r : ℝ} (hs : 0 < s) :
    emptyResidual s r 1 =
      r ^ 2 / 8 - s ^ 2 / 24 +
        g s r ^ 2 * s ^ 2 /
          ((2 * s + 1) * (s + 1 / 2)) +
        g s r * (1 / 2 - r) * (s + 1) /
          (2 * (2 * s + 1) * (s + 1 / 2)) := by
  have htwo : 2 * s + 1 ≠ 0 := by linarith
  have hhalf : s + 1 / 2 ≠ 0 := by linarith
  unfold emptyResidual bellman
  dsimp only
  field_simp [htwo, hhalf]
  unfold g
  ring
private theorem empty_uniform_case
    {s r : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2) :
    emptyResidual s r 1 ≥
      (emptyRateIncrement 1 + s ^ 2) / 1000 := by
  have hg : 0 < g s r := g_pos hr0
  rw [emptyResidual_uniform_eq hs]
  have hrate : emptyRateIncrement 1 = 0 := by
    norm_num [emptyRateIncrement]
  rw [hrate, zero_add]
  by_cases hsHalf : 1 / 2 ≤ s
  · have hden :
        (2 * s + 1) * (s + 1 / 2) ≤ 13 * s ^ 2 := by
      nlinarith [sq_nonneg (s - 1 / 2)]
    have hdenpos : 0 < (2 * s + 1) * (s + 1 / 2) := by
      positivity
    have hsquare :
        g s r ^ 2 / 13 ≤
          g s r ^ 2 * s ^ 2 /
            ((2 * s + 1) * (s + 1 / 2)) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 13) hdenpos).2
      have hmul :=
        mul_le_mul_of_nonneg_left hden (sq_nonneg (g s r))
      nlinarith
    have hcauchy :=
      weighted_square_bound
        (s := s) (r := r) (lam := 1) (by norm_num) (by norm_num)
    have hlast :
        0 ≤ g s r * (1 / 2 - r) * (s + 1) /
          (2 * (2 * s + 1) * (s + 1 / 2)) := by
      positivity
    simp only [g, one_mul] at hcauchy hsquare hlast ⊢
    nlinarith
  · have hsUpper : s ≤ 1 / 2 := le_of_not_ge hsHalf
    have hdUpper : 2 * s + 1 ≤ (s + 1) ^ 2 := by
      nlinarith [sq_nonneg s]
    have hcoef :
        1 / 3 ≤
          (s + 1) / (2 * (2 * s + 1) * (s + 1 / 2)) := by
      have hdenpos :
          0 < 2 * (2 * s + 1) * (s + 1 / 2) := by
        positivity
      apply (le_div_iff₀ hdenpos).2
      have hbound :
          2 * (s + 1) ^ 2 * (s + 1 / 2) ≤ 3 * (s + 1) := by
        have hfac : 0 ≤ s + 1 := by positivity
        nlinarith [mul_nonneg hfac
          (mul_nonneg (sub_nonneg.mpr hs.le)
            (by linarith : 0 ≤ 1 - s))]
      have hmul :=
        mul_le_mul_of_nonneg_right hdUpper
          (by linarith : 0 ≤ 2 * (s + 1 / 2))
      nlinarith
    have hlast :
        g s r * (1 / 2 - r) / 3 ≤
          g s r * (1 / 2 - r) * (s + 1) /
            (2 * (2 * s + 1) * (s + 1 / 2)) := by
      have hfactor : 0 ≤ g s r * (1 / 2 - r) := by positivity
      calc
        g s r * (1 / 2 - r) / 3 =
            (g s r * (1 / 2 - r)) * (1 / 3) := by ring
        _ ≤ (g s r * (1 / 2 - r)) *
              ((s + 1) /
                (2 * (2 * s + 1) * (s + 1 / 2))) :=
          mul_le_mul_of_nonneg_left hcoef hfactor
        _ = g s r * (1 / 2 - r) * (s + 1) /
              (2 * (2 * s + 1) * (s + 1 / 2)) := by ring
    have hcore :
        s ^ 2 / 12 ≤ r ^ 2 / 8 - s ^ 2 / 24 +
          (s + r) * (1 / 2 - r) / 3 := by
      have hleft : 0 ≤ r + s := by linarith
      have hright : 0 ≤ 4 - 5 * r - 3 * s := by linarith
      nlinarith [mul_nonneg hleft hright]
    have hsquare :
        0 ≤ g s r ^ 2 * s ^ 2 /
          ((2 * s + 1) * (s + 1 / 2)) := by
      positivity
    simp only [g] at hlast hsquare ⊢
    nlinarith
private theorem empty_floor_residual_eq
    {s r : ℝ} (hs : 0 < s) :
    emptyResidual s r (g s r) =
      floorR (2 * g s r - 1) (1 - 2 * r) 0 (2 * s) := by
  have hsTwo : 2 * s ≠ 0 := by linarith
  have hsOne : 2 * s + 1 ≠ 0 := by linarith
  have hsHalf : s + 1 / 2 ≠ 0 := by linarith
  unfold emptyResidual floorR floorW floorEta floorEll bellman
  dsimp only
  field_simp [hsTwo, hsOne, hsHalf]
  unfold g
  ring
private theorem empty_floor_case
    {s r : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hg1 : 1 ≤ g s r) :
    emptyResidual s r (g s r) ≥
      (emptyRateIncrement (g s r) + s ^ 2) / 1000 := by
  let K : ℝ := 2 * g s r - 1
  let e : ℝ := 1 - 2 * r
  have hK : 1 ≤ K := by
    dsimp [K]
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have he0 : 0 ≤ e := by
    dsimp [e]
    linarith
  have hsum : K + e = 2 * s := by
    dsimp [K, e]
    unfold g
    ring
  have hEll : floorEll 0 (2 * s) K = 1 := by
    unfold floorEll
    field_simp
    ring
  have hW0 : 0 ≤ floorW 0 (2 * s) K := by
    unfold floorW
    positivity
  have hWUpper :
      floorW 0 (2 * s) K ≤ (K + 1) / (2 * K) := by
    have hdenS : 0 < 2 * (2 * s + 1) := by positivity
    have hdenK : 0 < 2 * K := by positivity
    unfold floorW
    norm_num only [zero_add]
    apply (div_le_div_iff₀ hdenS hdenK).2
    have hKUpper : K ≤ 2 * s + 1 := by
      dsimp [K]
      unfold g
      linarith
    nlinarith
  have hEta :
      (K + e) / (16 + K + e) ≤ floorEta 0 (2 * s) := by
    have hetaEq : floorEta 0 (2 * s) = 1 := by
      unfold floorEta
      field_simp
      ring
    have hdenEq : 16 + K + e = 16 + 2 * s := by
      linarith
    rw [hsum, hdenEq, hetaEq]
    have hden : 0 < 16 + 2 * s := by positivity
    exact (div_le_one hden).2 (by linarith)
  have hResidual :=
    floorR_lower hK he0 (by rw [hEll]; norm_num)
      (by rw [hEll]) hW0 hWUpper hEta
  have hResidual' :
      (K ^ 2 + e ^ 2) / 384 ≤
        emptyResidual s r (g s r) := by
    rw [empty_floor_residual_eq hs]
    simpa [K, e] using hResidual
  have hRate :=
    floor_rate_bound (u := 0) (v := 2 * s) hK he0
      (by rw [hEll]; norm_num) (by rw [hEll])
  have hG : (K + 1) / 2 = g s r := by
    dsimp [K]
    ring
  have hS : (K + e) / 2 = s := by
    rw [hsum]
    ring
  have hRate' :
      emptyRateIncrement (g s r) + s ^ 2 ≤ K ^ 2 + e ^ 2 := by
    simpa [emptyRateIncrement, hEll, hG, hS] using hRate
  have henergy : 0 ≤ K ^ 2 + e ^ 2 := by positivity
  calc
    (emptyRateIncrement (g s r) + s ^ 2) / 1000
        ≤ (K ^ 2 + e ^ 2) / 1000 := by
          exact div_le_div_of_nonneg_right hRate' (by norm_num)
    _ ≤ (K ^ 2 + e ^ 2) / 384 := by
          nlinarith
    _ ≤ emptyResidual s r (g s r) := hResidual'
end Normalized
private theorem discrepancy_swap (a p h : ℝ) (x y : ℕ) :
    discrepancy a p h y x = discrepancy a p h x y := by
  unfold discrepancy
  rw [parentMass_swap]
private theorem regularizedMass_swap (a p : ℝ) (x y : ℕ) :
    regularizedMass a p y x = regularizedMass a p x y := by
  simp [regularizedMass, inventory, add_comm]
private theorem discrepancyLeft_swap (a p h : ℝ) (x y : ℕ) :
    discrepancyLeft a p h y x = discrepancyRight a p h x y := by
  unfold discrepancyLeft discrepancyRight
  rw [massLeft_swap]
private theorem discrepancyRight_swap (a p h : ℝ) (x y : ℕ) :
    discrepancyRight a p h y x = discrepancyLeft a p h x y := by
  unfold discrepancyLeft discrepancyRight
  rw [massRight_swap]
private theorem regularizedMassLeft_swap (a p : ℝ) (x y : ℕ) :
    regularizedMassLeft a p y x = regularizedMassRight a p x y := by
  rfl
private theorem regularizedMassRight_swap (a p : ℝ) (x y : ℕ) :
    regularizedMassRight a p y x = regularizedMassLeft a p x y := by
  rfl
private theorem localResidual_swap (a p h : ℝ) (x y : ℕ) :
    localResidual a p h y x = localResidual a p h x y := by
  unfold localResidual
  rw [discrepancyLeft_swap a p h x y,
    discrepancyRight_swap a p h x y,
    regularizedMassLeft_swap a p x y,
    regularizedMassRight_swap a p x y,
    rateLeft_swap a p h x y, rateRight_swap a p h x y,
    discrepancy_swap a p h x y, regularizedMass_swap a p x y]
  ring
private theorem localEnergy_swap (a p h : ℝ) (x y : ℕ) :
    localEnergy a p h y x = localEnergy a p h x y := by
  unfold localEnergy
  rw [rateLeft_swap a p h x y, rateRight_swap a p h x y,
    bias_swap a p h x y]
  ring
private theorem bellman_scale (c u t Z : ℝ) :
    bellman (c * u) (c * t) (c * Z) = c ^ 2 * bellman u t Z := by
  unfold bellman
  ring
private theorem discrepancy_scale
    {a p h : ℝ} {x y : ℕ} (hh : 0 < h) :
    discrepancy a p h x y =
      h * (discrepancy a p h x y / h) := by
  field_simp [hh.ne']
private theorem discrepancyLeft_normalization
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    discrepancyLeft a p h x y =
      h * Normalized.tPlus
        (discrepancy a p h x y / h)
        (bias a p h x y / (a * h)) := by
  rw [LocalPolicy.discrepancyLeft_eq]
  unfold Normalized.tPlus
  field_simp [ha.ne', hh.ne'] <;> ring
private theorem discrepancyRight_normalization
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    discrepancyRight a p h x y =
      h * Normalized.tMinus
        (discrepancy a p h x y / h)
        (bias a p h x y / (a * h)) := by
  rw [LocalPolicy.discrepancyRight_eq]
  unfold Normalized.tMinus
  field_simp [ha.ne', hh.ne'] <;> ring
private theorem rateLeft_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    rateLeft a p h x y =
      h * Normalized.hPlus
        (inventory x y / a)
        (((x : ℝ) - y) / inventory x y)
        (bias a p h x y / (a * h)) := by
  have hxr : 0 < (x : ℝ) := by exact_mod_cast hx
  have hsum : x + y ≠ 0 := by omega
  have hN : 0 < inventory x y := inventory_pos hsum
  unfold rateLeft
  rw [if_neg hsum, if_neg hx.ne']
  unfold massLeft parentMass Normalized.hPlus inventory
  field_simp [ha.ne', hh.ne', hxr.ne', hN.ne']
  ring
private theorem rateRight_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    rateRight a p h x y =
      h * Normalized.hMinus
        (inventory x y / a)
        (((x : ℝ) - y) / inventory x y)
        (bias a p h x y / (a * h)) := by
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  have hsum : x + y ≠ 0 := by omega
  have hN : 0 < inventory x y := inventory_pos hsum
  unfold rateRight
  rw [if_neg hsum, if_neg hy.ne']
  unfold massRight parentMass Normalized.hMinus inventory
  field_simp [ha.ne', hh.ne', hyr.ne', hN.ne']
  ring
private theorem regularizedMassLeft_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    regularizedMassLeft a p x y =
      h * Normalized.ZPlus
        (inventory x y / a)
        (discrepancy a p h x y / h)
        (((x : ℝ) - y) / inventory x y) := by
  have hNnonneg := inventory_nonneg x y
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hNden : 0 < inventory x y + a / 2 := by linarith
  have hxden : 0 < (x : ℝ) + a / 2 := by positivity
  unfold regularizedMassLeft Normalized.ZPlus Normalized.g
    discrepancy parentMass inventory
  field_simp [ha.ne', hh.ne', hN.ne', hNden.ne', hxden.ne']
  <;> ring_nf
  <;> field_simp [ha.ne', hh.ne', hN.ne', hNden.ne', hxden.ne']
  <;> ring
private theorem regularizedMassRight_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    regularizedMassRight a p x y =
      h * Normalized.ZMinus
        (inventory x y / a)
        (discrepancy a p h x y / h)
        (((x : ℝ) - y) / inventory x y) := by
  have hNnonneg := inventory_nonneg x y
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hNden : 0 < inventory x y + a / 2 := by linarith
  have hyden : 0 < (y : ℝ) + a / 2 := by positivity
  unfold regularizedMassRight Normalized.ZMinus Normalized.g
    discrepancy parentMass inventory
  field_simp [ha.ne', hh.ne', hN.ne', hNden.ne', hyden.ne']
  <;> ring_nf
  <;> field_simp [ha.ne', hh.ne', hN.ne', hNden.ne', hyden.ne']
  <;> ring
private theorem regularizedMass_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) :
    regularizedMass a p x y =
      h * Normalized.ZParent
        (inventory x y / a)
        (discrepancy a p h x y / h) := by
  have hNnonneg := inventory_nonneg x y
  have hden : 0 < inventory x y + a / 2 := by linarith
  unfold regularizedMass Normalized.ZParent Normalized.g
    discrepancy parentMass
  field_simp [ha.ne', hh.ne', hden.ne']
  ring
private theorem parentBellman_normalization
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a) (hh : 0 < h) :
    bellman h (discrepancy a p h x y) (regularizedMass a p x y) =
      h ^ 2 * bellman 1
        (discrepancy a p h x y / h)
        (Normalized.ZParent
          (inventory x y / a)
          (discrepancy a p h x y / h)) := by
  rw [regularizedMass_normalization ha hh]
  conv_lhs =>
    congr
    · rw [show h = h * 1 by ring]
    · rw [discrepancy_scale hh]
  exact bellman_scale h 1
    (discrepancy a p h x y / h)
    (Normalized.ZParent
      (inventory x y / a)
      (discrepancy a p h x y / h))
private theorem positive_residual_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    localResidual a p h x y =
      h ^ 2 *
        Normalized.residual
          (inventory x y / a)
          (discrepancy a p h x y / h)
          (((x : ℝ) - y) / inventory x y)
          (bias a p h x y / (a * h)) := by
  unfold localResidual Normalized.residual
  rw [rateLeft_normalization ha hh hx hy,
    rateRight_normalization ha hh hx hy,
    discrepancyLeft_normalization ha hh,
    discrepancyRight_normalization ha hh,
    regularizedMassLeft_normalization ha hh hx hy,
    regularizedMassRight_normalization ha hh hx hy,
    parentBellman_normalization ha hh]
  simp only [bellman_scale]
  ring
private theorem positive_energy_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    localEnergy a p h x y =
      h ^ 2 *
        (Normalized.rateIncrement
            (inventory x y / a)
            (((x : ℝ) - y) / inventory x y)
            (bias a p h x y / (a * h)) +
          (bias a p h x y / (a * h)) ^ 2) := by
  unfold localEnergy Normalized.rateIncrement
  rw [rateLeft_normalization ha hh hx hy,
    rateRight_normalization ha hh hx hy]
  field_simp [ha.ne', hh.ne'] <;> ring
private theorem feedbackCandidate_normalization
    {a h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    feedbackCandidate a h x y / (a * h) =
      Normalized.feedback
        (inventory x y / a)
        (((x : ℝ) - y) / inventory x y) := by
  have hxr : 0 < (x : ℝ) := by exact_mod_cast hx
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  have hN : 0 < inventory x y := inventory_pos (by omega)
  unfold feedbackCandidate parentMass Normalized.feedback Normalized.A
    Normalized.lambda inventory
  field_simp [ha.ne', hh.ne', hxr.ne', hyr.ne', hN.ne']
  <;> ring_nf
  <;> field_simp [ha.ne', hh.ne', hxr.ne', hyr.ne', hN.ne']
  <;> ring
private theorem uniformCandidate_normalization
    {a h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    uniformCandidate h x y / (a * h) =
      Normalized.uniform
        (inventory x y / a)
        (((x : ℝ) - y) / inventory x y) := by
  have hN : 0 < inventory x y := inventory_pos (by omega)
  unfold uniformCandidate parentMass Normalized.uniform inventory
  field_simp [ha.ne', hh.ne', hN.ne']
  <;> ring
private theorem floorCandidate_normalization
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) (hy : 0 < y) :
    floorCandidate a p h x y / (a * h) =
      Normalized.floorCap
        (inventory x y / a)
        (discrepancy a p h x y / h)
        (((x : ℝ) - y) / inventory x y) := by
  have hyr : 0 < (y : ℝ) := by exact_mod_cast hy
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hden : 0 < 2 * (y : ℝ) + a := by positivity
  unfold floorCandidate discrepancy parentMass Normalized.floorCap inventory
  field_simp [ha.ne', hh.ne', hyr.ne', hN.ne', hden.ne']
  <;> ring_nf
  <;> field_simp [ha.ne', hh.ne', hyr.ne', hN.ne', hden.ne']
  <;> ring
private theorem ordered_positive_case
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (hxy : y ≤ x) (hx : 0 < x) (hy : 0 < y)
    (ht : discrepancy a p h x y ≤ h / 2) :
    localResidual a p h x y ≥ localEnergy a p h x y / 1000 := by
  let s : ℝ := inventory x y / a
  let r : ℝ := discrepancy a p h x y / h
  let ρ : ℝ := ((x : ℝ) - y) / inventory x y
  let z : ℝ := bias a p h x y / (a * h)
  have hN : 0 < inventory x y := inventory_pos (by omega)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hr0 : -s < r := by
    dsimp [s, r]
    unfold discrepancy parentMass
    field_simp [ha.ne', hh.ne']
    nlinarith
  have hr1 : r ≤ 1 / 2 := by
    dsimp [r]
    exact (div_le_iff₀ hh).2 (by nlinarith)
  have hρ0 : 0 ≤ ρ := by
    dsimp [ρ]
    apply div_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hxy)
    · exact hN.le
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    apply (div_lt_one hN).2
    have hyR : 0 < (y : ℝ) := by exact_mod_cast hy
    unfold inventory
    linarith
  have hResidual :
      localResidual a p h x y =
        h ^ 2 * Normalized.residual s r ρ z := by
    simpa [s, r, ρ, z] using
      positive_residual_normalization ha hh hx hy
  have hEnergy :
      localEnergy a p h x y =
        h ^ 2 * (Normalized.rateIncrement s ρ z + z ^ 2) := by
    simpa [s, ρ, z] using positive_energy_normalization ha hh hx hy
  have hnormalized :
      Normalized.residual s r ρ z ≥
        (Normalized.rateIncrement s ρ z + z ^ 2) / 1000 := by
    by_cases heq : x = y
    · subst x
      have hb : bias a p h y y = 0 := by
        simp [bias, orderedBias]
      have hρ : ρ = 0 := by
        simp [ρ, inventory]
      have hz : z = 0 := by
        simp [z, hb]
      rw [hρ, hz]
      exact Normalized.equal_case hs hr0 hr1
    · have hlt : y < x := lt_of_le_of_ne hxy (Ne.symm heq)
      have hb :
          bias a p h x y =
            min (feedbackCandidate a h x y)
              (min (uniformCandidate h x y)
                (floorCandidate a p h x y)) := by
        unfold bias
        rw [if_pos hxy]
        unfold orderedBias
        rw [if_neg heq, if_neg (by omega : x + y ≠ 0),
          if_neg hy.ne']
      have hah : 0 ≤ a * h := (mul_pos ha hh).le
      have hzChoice :
          z =
            min (Normalized.feedback s ρ)
              (min (Normalized.uniform s ρ)
                (Normalized.floorCap s r ρ)) := by
        dsimp [z]
        rw [hb, ← min_div_div_right hah,
          ← min_div_div_right hah]
        rw [feedbackCandidate_normalization ha hh hx hy,
          uniformCandidate_normalization ha hh hx hy,
          floorCandidate_normalization ha hh hx hy]
      rw [hzChoice]
      exact Normalized.threeCap_case hs hr0 hr1 hρ0 hρ1
  rw [hResidual, hEnergy]
  have hscaled :=
    mul_le_mul_of_nonneg_left hnormalized (sq_nonneg h)
  calc
    h ^ 2 * (Normalized.rateIncrement s ρ z + z ^ 2) / 1000 =
        h ^ 2 *
          ((Normalized.rateIncrement s ρ z + z ^ 2) / 1000) := by ring
    _ ≤ h ^ 2 * Normalized.residual s r ρ z := hscaled
private theorem ordered_empty_residual_normalization
    {a p h : ℝ} {x : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) :
    localResidual a p h x 0 =
      h ^ 2 *
        Normalized.emptyResidual
          ((x : ℝ) / a)
          (discrepancy a p h x 0 / h)
          (rateRight a p h x 0 / h) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hsum : x + 0 ≠ 0 := by omega
  have hxr : 0 < (x : ℝ) := by exact_mod_cast hx
  have hb : bias a p h x 0 = parentMass h x 0 := by
    simp [bias, orderedBias, hx0]
  have hRL : rateLeft a p h x 0 = h := by
    unfold rateLeft
    rw [if_neg hsum, if_neg hx0]
    unfold massLeft
    rw [hb]
    simp [parentMass, inventory, hx0]
  have hRR : rateRight a p h x 0 = max h (p / a) := by
    unfold rateRight
    rw [if_neg hsum, if_pos rfl]
  unfold localResidual Normalized.emptyResidual
  dsimp only
  rw [hRL, hRR]
  unfold discrepancyLeft discrepancyRight regularizedMassLeft
    regularizedMassRight regularizedMass discrepancy massLeft massRight
    Normalized.g bellman
  rw [hb]
  unfold parentMass inventory
  field_simp [ha.ne', hh.ne', hxr.ne']
  <;> ring_nf
  <;> field_simp [ha.ne', hh.ne', hxr.ne']
  <;> ring
private theorem ordered_empty_energy_normalization
    {a p h : ℝ} {x : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hx : 0 < x) :
    localEnergy a p h x 0 =
      h ^ 2 *
        (Normalized.emptyRateIncrement
            (rateRight a p h x 0 / h) +
          ((x : ℝ) / a) ^ 2) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hsum : x + 0 ≠ 0 := by omega
  have hb : bias a p h x 0 = parentMass h x 0 := by
    simp [bias, orderedBias, hx0]
  have hRL : rateLeft a p h x 0 = h := by
    unfold rateLeft
    rw [if_neg hsum, if_neg hx0]
    unfold massLeft
    rw [hb]
    simp [parentMass, inventory, hx0]
  unfold localEnergy Normalized.emptyRateIncrement
  rw [hRL]
  rw [hb]
  unfold parentMass inventory
  field_simp [ha.ne', hh.ne']
  ring
private theorem empty_total_normalization
    {a p h : ℝ} {x : ℕ}
    (ha : 0 < a) (hh : 0 < h) :
    Normalized.g ((x : ℝ) / a)
        (discrepancy a p h x 0 / h) =
      p / (a * h) := by
  unfold Normalized.g discrepancy parentMass inventory
  field_simp [ha.ne', hh.ne']
  ring
private theorem ordered_one_empty_case
    {a p h : ℝ} {x : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h) (hx : 0 < x)
    (ht : discrepancy a p h x 0 ≤ h / 2) :
    localResidual a p h x 0 ≥ localEnergy a p h x 0 / 1000 := by
  let s : ℝ := (x : ℝ) / a
  let r : ℝ := discrepancy a p h x 0 / h
  let emptyRate : ℝ := rateRight a p h x 0 / h
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hr0 : -s < r := by
    dsimp [s, r]
    unfold discrepancy parentMass inventory
    field_simp [ha.ne', hh.ne']
    norm_num at *
    nlinarith
  have hr1 : r ≤ 1 / 2 := by
    dsimp [r]
    exact (div_le_iff₀ hh).2 (by nlinarith)
  have hResidual :
      localResidual a p h x 0 =
        h ^ 2 * Normalized.emptyResidual s r emptyRate := by
    simpa [s, r, emptyRate] using
      ordered_empty_residual_normalization ha hh hx
  have hEnergy :
      localEnergy a p h x 0 =
        h ^ 2 *
          (Normalized.emptyRateIncrement emptyRate + s ^ 2) := by
    simpa [s, emptyRate] using
      ordered_empty_energy_normalization ha hh hx
  have hnormalized :
      Normalized.emptyResidual s r emptyRate ≥
        (Normalized.emptyRateIncrement emptyRate + s ^ 2) / 1000 := by
    by_cases hsmall : p / a ≤ h
    · have hRate : emptyRate = 1 := by
        dsimp [emptyRate]
        unfold rateRight
        rw [if_neg (by omega : x + 0 ≠ 0), if_pos rfl,
          max_eq_left hsmall]
        field_simp [hh.ne']
      rw [hRate]
      exact Normalized.empty_uniform_case hs hr0 hr1
    · have hlarge : h ≤ p / a := le_of_not_ge hsmall
      have hRate :
          emptyRate = Normalized.g s r := by
        dsimp [emptyRate]
        unfold rateRight
        rw [if_neg (by omega : x + 0 ≠ 0), if_pos rfl,
          max_eq_right hlarge]
        rw [empty_total_normalization ha hh]
        ring
      have hg1 : 1 ≤ Normalized.g s r := by
        rw [← hRate]
        dsimp [emptyRate]
        unfold rateRight
        rw [if_neg (by omega : x + 0 ≠ 0), if_pos rfl,
          max_eq_right hlarge]
        apply (le_div_iff₀ hh).2
        simpa using hlarge
      rw [hRate]
      exact Normalized.empty_floor_case hs hr0 hr1 hg1
  rw [hResidual, hEnergy]
  have hscaled :=
    mul_le_mul_of_nonneg_left hnormalized (sq_nonneg h)
  calc
    h ^ 2 * (Normalized.emptyRateIncrement emptyRate + s ^ 2) / 1000 =
        h ^ 2 *
          ((Normalized.emptyRateIncrement emptyRate + s ^ 2) / 1000) := by
            ring
    _ ≤ h ^ 2 * Normalized.emptyResidual s r emptyRate := hscaled
private theorem empty_parent_residual_eq
    {a p h : ℝ} (ha : 0 < a) :
    localResidual a p h 0 0 =
      h * (p / a) / 2 - 7 * (p / a) ^ 2 / 8 := by
  unfold localResidual discrepancyLeft discrepancyRight
    regularizedMassLeft regularizedMassRight regularizedMass
    discrepancy massLeft massRight rateLeft rateRight bias orderedBias
    parentMass inventory bellman
  simp only [Nat.cast_zero, zero_add, add_zero, le_refl, if_pos,
    max_self]
  field_simp [ha.ne']
  ring
private theorem empty_parent_energy_eq (a p h : ℝ) :
    localEnergy a p h 0 0 = 0 := by
  unfold localEnergy rateLeft rateRight bias orderedBias parentMass inventory
  norm_num
private theorem empty_parent_case
    {a p h : ℝ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h 0 0 ≤ h / 2) :
    localResidual a p h 0 0 ≥ localEnergy a p h 0 0 / 1000 := by
  have ht' : p / a ≤ h / 2 := by
    simpa [discrepancy, parentMass, inventory] using ht
  have ht0 : 0 ≤ p / a := by positivity
  have hproduct :
      0 ≤ (p / a) * (h / 2 - p / a) := by positivity
  rw [empty_parent_residual_eq ha, empty_parent_energy_eq]
  norm_num
  nlinarith [sq_nonneg (p / a)]
private theorem ordered_case
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    localResidual a p h x y ≥ localEnergy a p h x y / 1000 := by
  by_cases hy : y = 0
  · subst y
    by_cases hx : x = 0
    · subst x
      exact empty_parent_case ha hp hh ht
    · exact ordered_one_empty_case ha hp hh (Nat.pos_of_ne_zero hx) ht
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    have hxpos : 0 < x := lt_of_lt_of_le hypos hxy
    exact ordered_positive_case ha hp hh hxy hxpos hypos ht
end
end FD1D.V5.LocalBellman
end

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
namespace FD1D.V5.LocalBellman
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    localResidual a p h x y ≥ localEnergy a p h x y / 1000 := by
  by_cases hxy : y ≤ x
  · exact ordered_case ha hp hh hxy ht
  · have hyx : x ≤ y := Nat.le_of_not_ge hxy
    have htSwap : discrepancy a p h y x ≤ h / 2 := by
      rwa [discrepancy_swap]
    have hs := ordered_case ha hp hh hyx htSwap
    rwa [localResidual_swap, localEnergy_swap] at hs
end FD1D.V5.LocalBellman
