-- Prove2me | solution 1 for ConsistentSubmodular.HardInstance.lp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:13.083282+00:00
-- url     : https://prove2.me/submissions/bd36e969-c590-4839-82a8-8a27c41c582c

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardScalar

section

noncomputable section

namespace ConsistentSubmodular.HardInstance

/-- The identity of Appendix A.2: `1 + x + y - x y - y²/x - (1 + x - y)(1 + x y) = y Φ(x)`. -/
theorem lpDenominator_sub (x : ℝ) :
    lpDenominator x - lpNumerator x * (1 + x ^ 3 * (1 + x)) = lpThird x * phi x := by
  unfold lpDenominator lpNumerator lpThird phi
  ring

end ConsistentSubmodular.HardInstance

end

end

section

open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem solution {x ε k C : ℝ} (hx0 : 0 < x) (hs : x * (1 + x) ≤ 1) (hphi : phi x = 0)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 6) (hk : 0 < k) (hεk : 1 ≤ ε * k) (hC0 : 0 ≤ C)
    (hC : C ≤ ε * k) :
    k * lpNumerator x + lpError x * C ≤
      (1 / (1 + x ^ 3 * (1 + x)) + 12 * ε) * (k * lpDenominator x - lpError x) := by
  set q := x ^ 3 * (1 + x) with hq
  set r := 1 / (1 + q) with hr
  have hq0 : 0 ≤ q := by positivity
  have hrq : r * (1 + q) = 1 := by rw [hr]; field_simp
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one (by positivity)]; linarith
  have hx1 : x ≤ 1 := by nlinarith
  have hy0 : 0 ≤ lpThird x := by unfold lpThird; positivity
  have hyx : lpThird x ≤ x := by unfold lpThird; nlinarith
  have hy1 : lpThird x ≤ 1 := by linarith
  have hμ₁0 : 0 ≤ lpMuOne x := by
    unfold lpMuOne
    have : 0 ≤ 1 - x := by linarith
    positivity
  have hμ₁1 : lpMuOne x * x ≤ 1 := by
    unfold lpMuOne
    have h1 : x * (1 + x) * (1 - x) ≤ 1 := by nlinarith
    nlinarith [mul_le_mul h1 hx1 hx0.le zero_le_one]
  have hμ₂0 : 0 ≤ lpMuTwo x := by unfold lpMuTwo; linarith
  have hμ₂1 : lpMuTwo x ≤ 1 := by unfold lpMuTwo; nlinarith
  have hη0 : 0 ≤ lpError x := by unfold lpError; positivity
  have hη3 : lpError x ≤ 3 := by
    unfold lpError
    nlinarith [mul_le_mul hμ₂1 hy1 hy0 zero_le_one]
  have hN1 : 1 ≤ lpNumerator x := by unfold lpNumerator; linarith
  -- `Den = N (1 + x y)`, since `Φ(x) = 0`.
  have hden : lpNumerator x * (1 + q) = lpDenominator x := by
    have := lpDenominator_sub x
    rw [hphi, mul_zero] at this
    linarith
  set P := lpNumerator x * (1 + q) with hP
  have hP1 : 1 ≤ P := by nlinarith
  have hrP : r * P = lpNumerator x := by rw [hP]; linear_combination lpNumerator x * hrq
  -- `k Den - η ≥ k (P - 3 ε) ≥ 0`.
  have hbase : k * (P - 3 * ε) ≤ k * lpDenominator x - lpError x := by
    have h2 : 3 ≤ 3 * (ε * k) := by linarith
    have h3 : k * (P - 3 * ε) = k * P - 3 * (ε * k) := by ring
    rw [h3, ← hden]
    linarith
  have hbase0 : 0 ≤ k * (P - 3 * ε) := mul_nonneg hk.le (by linarith)
  have hstep : (r + 12 * ε) * (k * (P - 3 * ε)) ≤
      (r + 12 * ε) * (k * lpDenominator x - lpError x) :=
    mul_le_mul_of_nonneg_left hbase (by linarith)
  have hexpand : (r + 12 * ε) * (k * (P - 3 * ε)) =
      k * (lpNumerator x - 3 * ε * r + 12 * ε * P - 36 * ε ^ 2) := by
    linear_combination k * hrP
  have hgain : k * (lpNumerator x + 3 * ε) ≤ (r + 12 * ε) * (k * (P - 3 * ε)) := by
    rw [hexpand]
    apply mul_le_mul_of_nonneg_left _ hk.le
    nlinarith
  have hlhs : k * lpNumerator x + lpError x * C ≤ k * (lpNumerator x + 3 * ε) := by
    have h1 : lpError x * C ≤ 3 * (ε * k) := mul_le_mul hη3 hC hC0 (by norm_num)
    have h2 : k * (lpNumerator x + 3 * ε) = k * lpNumerator x + 3 * (ε * k) := by ring
    rw [h2]
    linarith
  linarith

end
