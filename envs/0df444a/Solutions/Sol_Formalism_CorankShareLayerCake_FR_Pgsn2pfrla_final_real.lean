-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.final_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:12.770559+00:00
-- url     : https://prove2.me/submissions/8fbef6d8-b5e9-45af-b6f3-33acd39fc526

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open Finset Module LinearMap
open scoped InnerProductSpace
namespace Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
theorem _root_.solution (D R w e ε η t X tW : ℝ) (hD : 0 < D) (hR : 0 < R) (he0 : 0 ≤ e) (he : e ≤ 1/4)
    (hε : 0 ≤ ε) (hw0 : 0 ≤ w) (hwD : w ≤ D) (ht : R * (1 - √e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D) (hlow : t / D * w - √w * √X ≤ tW)
    (hup : tW ≤ ε * R + R * √(ε * e)) : w ≤ (2 * η + 4 * ε + 4 * √e) * D := by
  have hs0 : 0 ≤ √e := Real.sqrt_nonneg e
  have hs : √e ≤ 1 / 2 := by
    have h4 : √(1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h4]
    exact Real.sqrt_le_sqrt he
  have ht0 : R / 2 ≤ t := by nlinarith
  have htpos : 0 < t := by linarith
  have hXD : X * D ≤ η * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hX hD.le
    rwa [div_mul_cancel₀ _ hD.ne'] at h1
  have hη : 0 ≤ η := by
    have h2 : 0 ≤ η * t ^ 2 := le_trans (mul_nonneg hX0 hD.le) hXD
    by_contra hc
    push_neg at hc
    have : η * t ^ 2 < 0 := mul_neg_of_neg_of_pos hc (by positivity)
    linarith
  by_cases hK : 1 ≤ 2 * η + 4 * ε + 4 * √e
  · calc w ≤ D := hwD
      _ = 1 * D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK hD.le
  push_neg at hK
  have hε1 : ε ≤ 1 := by linarith
  have hsε : √ε ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hε1
  have hse : √(ε * e) = √ε * √e := Real.sqrt_mul hε e
  have hab : √w * √X * D ≤ t * (w + η * D) / 2 := by
    have hP : 0 ≤ √w * √X * D := by positivity
    have hQ : 0 ≤ t * (w + η * D) / 2 := by positivity
    have hsq : (√w * √X * D) ^ 2 ≤ (t * (w + η * D) / 2) ^ 2 := by
      have e1 : (√w * √X * D) ^ 2 = w * (X * D) * D := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hw0, Real.sq_sqrt hX0]; ring
      rw [e1]
      nlinarith [mul_le_mul_of_nonneg_left hXD (mul_nonneg hw0 hD.le),
        mul_nonneg (sq_nonneg t) (sq_nonneg (w - η * D))]
    calc √w * √X * D = √((√w * √X * D) ^ 2) := (Real.sqrt_sq hP).symm
      _ ≤ √((t * (w + η * D) / 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = t * (w + η * D) / 2 := Real.sqrt_sq hQ
  have hc := hlow.trans hup
  rw [hse] at hc
  have key : t * w - √w * √X * D ≤ D * (ε * R + R * (√ε * √e)) := by
    have h1 := mul_le_mul_of_nonneg_right hc hD.le
    have e1 : t / D * w * D = t * w := by field_simp
    nlinarith
  by_cases hwη : w ≤ η * D
  · nlinarith [mul_nonneg (by positivity : 0 ≤ η + 4 * ε + 4 * √e) hD.le]
  push_neg at hwη
  have h3 : R / 2 * (w - η * D) ≤ t * (w - η * D) := mul_le_mul_of_nonneg_right ht0 (by linarith)
  have h4 : R * ((w - η * D) - 4 * D * (ε + √ε * √e)) ≤ 0 := by nlinarith
  have h5 : (w - η * D) - 4 * D * (ε + √ε * √e) ≤ 0 := by
    by_contra hc2
    push_neg at hc2
    have := mul_pos hR hc2
    linarith
  have h6 : √ε * √e ≤ √e := mul_le_of_le_one_left hs0 hsε
  nlinarith [mul_le_mul_of_nonneg_left h6 hD.le, mul_nonneg hη hD.le]
end Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
