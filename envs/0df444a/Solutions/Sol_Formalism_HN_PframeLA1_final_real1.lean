-- Prove2me | solution 1 for Formalism.HN.PframeLA1.final_real1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:17.597855+00:00
-- url     : https://prove2.me/submissions/7d871d1a-b582-4dd5-9209-fc0851ede494

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PframeLA1
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open scoped InnerProductSpace
namespace Formalism.HN.PframeLA1
theorem _root_.solution (D R w e ε η t X tW : ℝ) (hD : 0 < D) (hR : 0 < R) (he0 : 0 ≤ e) (he : e ≤ 1/4)
    (hε : 0 ≤ ε) (hw0 : 0 ≤ w) (hwD : w ≤ D) (ht : R * (1 - √e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D) (hlow : t / D * w - √w * √X ≤ tW)
    (hup : tW ≤ ε * R + R * √(ε * e)) : w ≤ (η + 4 * ε + 4 * √e) * D := by
  have hsw : √w ^ 2 = w := Real.sq_sqrt hw0
  have hsX : √X ^ 2 = X := Real.sq_sqrt hX0
  have hse0 : 0 ≤ √e := Real.sqrt_nonneg e
  have hse : √e ≤ 1 / 2 := by
    rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hRt : R ≤ 2 * t := by nlinarith [mul_le_mul_of_nonneg_left hse hR.le]
  have htpos : 0 < t := by linarith
  have hη : 0 ≤ η := by
    have h1 : 0 ≤ η * t ^ 2 / D := le_trans hX0 hX
    have h2 : 0 ≤ η * t ^ 2 := by
      have := mul_nonneg h1 hD.le
      rwa [div_mul_cancel₀ _ hD.ne'] at this
    by_contra hneg
    push_neg at hneg
    have : η * t ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  by_cases hε4 : 1 / 4 ≤ ε
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ η + 4 * ε + 4 * √e - 1) hD.le]
  push_neg at hε4
  set q := √(ε * e) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqe : q ≤ √e := Real.sqrt_le_sqrt (by nlinarith)
  set y := D / t * √X with hy
  have hy2 : y ^ 2 ≤ η * D := by
    have h1 : y ^ 2 = D ^ 2 * X / t ^ 2 := by rw [hy, mul_pow, div_pow, hsX]; ring
    rw [h1, div_le_iff₀ (by positivity)]
    have h2 : X * D ≤ η * t ^ 2 := (le_div_iff₀ hD).mp hX
    nlinarith [mul_le_mul_of_nonneg_left h2 hD.le]
  have hyt : y * t = D * √X := by rw [hy]; field_simp
  have hDt : D * (t / D) = t := by field_simp
  have hkey : t * (w - √w * y) ≤ t * (2 * D * (ε + q)) := by
    have h1 : t / D * w - √w * √X ≤ R * (ε + q) := by linarith
    have h2 : t * w - D * (√w * √X) ≤ D * (R * (ε + q)) := by
      have := mul_le_mul_of_nonneg_left h1 hD.le
      have e1 : D * (t / D * w - √w * √X) = t * w - D * (√w * √X) := by
        linear_combination w * hDt
      linarith
    have h3 : D * (R * (ε + q)) ≤ D * (2 * t * (ε + q)) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      nlinarith
    have e2 : t * (√w * y) = D * (√w * √X) := by linear_combination √w * hyt
    nlinarith
  have hmain : w - √w * y ≤ 2 * D * (ε + q) := le_of_mul_le_mul_left hkey htpos
  have hamgm : √w * y ≤ (w + y ^ 2) / 2 := by nlinarith [sq_nonneg (√w - y)]
  nlinarith [mul_le_mul_of_nonneg_left hqe hD.le]
end Formalism.HN.PframeLA1
