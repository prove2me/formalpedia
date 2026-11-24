-- Prove2me | solution 1 for FockSPR.phiFunc_quad_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:37.999149+00:00
-- url     : https://prove2.me/submissions/081ff4bc-ef4c-4499-9a28-cc302ea7e65d

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
section
@[expose] public section
open Real MeasureTheory Set
noncomputable section
namespace FockSPR
private lemma rStar_sq {n : ℕ} : (rStar n) ^ 2 = ↑n + 1 / 2 := by
  unfold rStar; rw [sq]; exact Real.mul_self_sqrt (by positivity)
private lemma rStar_gt_one {n : ℕ} (hn : 1 ≤ n) : rStar n > 1 := by
  unfold rStar
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt (↑n + 1 / 2) := Real.sqrt_lt_sqrt (by norm_num)
        (by have : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn; linarith only [this])
private lemma rStar_pos {n : ℕ} (hn : 1 ≤ n) : 0 < rStar n :=
  lt_trans one_pos (rStar_gt_one hn)
private lemma hasDerivAt_phiFunc (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (phiFunc n) ((2 * ↑n + 1) / r - 2 * r) r := by
  unfold phiFunc
  have h1 := (Real.hasDerivAt_log (ne_of_gt hr)).const_mul (2 * ↑n + 1 : ℝ)
  have h2 : HasDerivAt (fun r => r ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  have h3 := h1.sub h2
  rw [show (2 * (n : ℝ) + 1) / r - 2 * r = (2 * ↑n + 1) * r⁻¹ - 2 * r by
    rw [div_eq_mul_inv]]
  exact h3
private lemma hasDerivAt_hFunc (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (hFunc n) ((2 * ↑n + 1) / r - 2 * rStar n) r := by
  unfold hFunc
  have hsq : HasDerivAt (fun r => (r - rStar n) ^ 2) (2 * (r - rStar n)) r := by
    have h : HasDerivAt (fun x : ℝ => (x - rStar n) ^ 2)
        ((2 : ℕ) * (r - rStar n) ^ (2 - 1) * (1 - 0)) r :=
      ((hasDerivAt_id r).sub (hasDerivAt_const r (rStar n))).pow 2
    simp_all
  have hadd := (hasDerivAt_phiFunc n hr).add hsq
  rw [show ((2 * ↑n + 1) / r - 2 * r) + 2 * (r - rStar n)
      = (2 * (↑n : ℝ) + 1) / r - 2 * rStar n by ring] at hadd
  exact hadd
private lemma hFunc_deriv_val {n : ℕ} (_hn : 1 ≤ n) :
    (2 * ↑n + 1 : ℝ) / rStar n - 2 * rStar n = 0 := by
  have : (2 * ↑n + 1 : ℝ) = 2 * (rStar n) ^ 2 := by rw [rStar_sq]; ring
  rw [this]; field_simp; ring
private lemma hFunc_deriv_eq_zero {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (hFunc n) 0 (rStar n) := by
  rw [show (0 : ℝ) = (2 * ↑n + 1 : ℝ) / rStar n - 2 * rStar n from
    (hFunc_deriv_val hn).symm]
  exact hasDerivAt_hFunc n (rStar_pos hn)
private lemma hFunc_concaveOn {n : ℕ} (hn : 1 ≤ n) :
    ConcaveOn ℝ (Ioi 0) (hFunc n) := by
  apply (StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) _ _).concaveOn
  · unfold hFunc phiFunc
    exact ((continuousOn_const.mul
      (Real.continuousOn_log.mono (fun x hx => ne_of_gt hx))).sub
      (continuousOn_pow 2)).add ((continuousOn_id.sub continuousOn_const).pow 2)
  · rw [interior_Ioi]
    intro a ha b hb hab
    rw [(hasDerivAt_hFunc n (show (0:ℝ) < a from ha)).deriv,
        (hasDerivAt_hFunc n (show (0:ℝ) < b from hb)).deriv]
    linarith only [div_lt_div_of_pos_left
      (show (0 : ℝ) < 2 * ↑n + 1 from by positivity)
      (show (0:ℝ) < a from ha) hab]
private lemma hFunc_le {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    hFunc n r ≤ hFunc n (rStar n) := by
  rcases lt_trichotomy r (rStar n) with hlt | heq | hgt
  · exact (slope_nonneg_iff_of_le hlt.le).mp
      ((hFunc_concaveOn hn).le_slope_of_hasDerivAt
        (show r ∈ Ioi 0 from hr) (show rStar n ∈ Ioi 0 from rStar_pos hn)
        hlt (hFunc_deriv_eq_zero hn))
  · rw [heq]
  · exact (slope_nonpos_iff_of_le hgt.le).mp
      ((hFunc_concaveOn hn).slope_le_of_hasDerivAt
        (show rStar n ∈ Ioi 0 from rStar_pos hn) (show r ∈ Ioi 0 from hr)
        hgt (hFunc_deriv_eq_zero hn))
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Set
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) :
    phiFunc n r ≤ phiFunc n (rStar n) - (r - rStar n) ^ 2 := by
  have h := hFunc_le hn hr
  unfold hFunc at h
  linarith only [h, sq_nonneg (r - rStar n)]
end FockSPR
