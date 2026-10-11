-- Prove2me | solution 1 for BlackScholesModel.call_theta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T14:28:18.693992+00:00
-- url     : https://prove2.me/submissions/0b832ecd-2c3d-4b9c-b5c2-ad218f0b9bd5

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_stdNormalCDF_hasDerivAt
import Theorems.Thm_BlackScholesModel_pdf_dPlus_dMinus_balance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun t' => callPrice K r σ T S t')
      (-(S * stdNormalPDF (dPlus S K r σ (T - t)) * σ) /
        (2 * Real.sqrt (T - t)) -
        r * K * Real.exp (-r * (T - t)) *
          stdNormalCDF (dMinus S K r σ (T - t))) t := by
  let τ := T - t
  have hτ : 0 < τ := sub_pos.mpr ht
  have hroot0 : Real.sqrt τ ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hτ)
  have hden0 : σ * Real.sqrt τ ≠ 0 :=
    mul_ne_zero (ne_of_gt hσ) hroot0
  have hτderiv : HasDerivAt (fun u : ℝ => T - u) (-1) t := by
    convert (hasDerivAt_const t T).sub (hasDerivAt_id t) using 1 <;>
      first
      | rfl
      | (funext u; dsimp [id]; ring)
      | ring
  have hroot : HasDerivAt (fun u : ℝ => Real.sqrt (T - u))
      (-1 / (2 * Real.sqrt τ)) t := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hτ)).comp t hτderiv using 1 <;>
      first
      | rfl
      | (funext u; dsimp [Function.comp_def]; ring)
      | ring
  have hnum : HasDerivAt
      (fun u : ℝ => Real.log (S / K) +
        (r + σ ^ 2 / 2) * (T - u))
      (-(r + σ ^ 2 / 2)) t := by
    convert (hτderiv.mul_const (r + σ ^ 2 / 2)).const_add
      (Real.log (S / K)) using 1 <;>
      first
      | rfl
      | (funext u; dsimp [id]; ring)
      | ring
  have hden : HasDerivAt
      (fun u : ℝ => σ * Real.sqrt (T - u))
      (σ * (-1 / (2 * Real.sqrt τ))) t :=
    hroot.const_mul σ
  let A : ℝ :=
    (-(r + σ ^ 2 / 2) * (σ * Real.sqrt τ) -
      (Real.log (S / K) + (r + σ ^ 2 / 2) * τ) *
        (σ * (-1 / (2 * Real.sqrt τ)))) /
        (σ * Real.sqrt τ) ^ 2
  have hdPlus : HasDerivAt (fun u : ℝ => dPlus S K r σ (T - u)) A t := by
    convert hnum.div hden hden0 using 1 <;>
      first
      | rfl
      | (funext u; dsimp [dPlus]; ring)
      | (dsimp [dPlus, A, τ]; ring)
  have hdMinus : HasDerivAt (fun u : ℝ => dMinus S K r σ (T - u))
      (A - σ * (-1 / (2 * Real.sqrt τ))) t := by
    convert hdPlus.sub hden using 1 <;>
      first
      | rfl
      | (funext u; dsimp [dMinus]; ring)
      | (dsimp [dMinus, A, τ]; ring)
  have houterPlus : HasDerivAt (fun z : ℝ => stdNormalCDF z)
      (stdNormalPDF (dPlus S K r σ τ)) (dPlus S K r σ τ) :=
    stdNormalCDF_hasDerivAt (dPlus S K r σ τ)
  have houterMinus : HasDerivAt (fun z : ℝ => stdNormalCDF z)
      (stdNormalPDF (dMinus S K r σ τ)) (dMinus S K r σ τ) :=
    stdNormalCDF_hasDerivAt (dMinus S K r σ τ)
  have hNplus : HasDerivAt
      (fun u : ℝ => stdNormalCDF (dPlus S K r σ (T - u)))
      (stdNormalPDF (dPlus S K r σ τ) * A) t := by
    simpa only [Function.comp_def] using houterPlus.comp t hdPlus
  have hNminus : HasDerivAt
      (fun u : ℝ => stdNormalCDF (dMinus S K r σ (T - u)))
      (stdNormalPDF (dMinus S K r σ τ) *
        (A - σ * (-1 / (2 * Real.sqrt τ)))) t := by
    simpa only [Function.comp_def] using houterMinus.comp t hdMinus
  have hdiscarg : HasDerivAt (fun u : ℝ => -r * (T - u)) r t := by
    convert hτderiv.const_mul (-r) using 1 <;>
      first
      | rfl
      | (funext u; ring)
      | ring
  have hdisc : HasDerivAt (fun u : ℝ => Real.exp (-r * (T - u)))
      (Real.exp (-r * τ) * r) t :=
    (Real.hasDerivAt_exp _).comp t hdiscarg
  have hprice : HasDerivAt
      (fun u : ℝ =>
        stdNormalCDF (dPlus S K r σ (T - u)) * S -
        stdNormalCDF (dMinus S K r σ (T - u)) * K *
          Real.exp (-r * (T - u)))
      ((stdNormalPDF (dPlus S K r σ τ) * A) * S -
       ((stdNormalPDF (dMinus S K r σ τ) *
          (A - σ * (-1 / (2 * Real.sqrt τ)))) * K) * Real.exp (-r * τ) -
       (stdNormalCDF (dMinus S K r σ τ) * K) *
          (Real.exp (-r * τ) * r)) t := by
    convert (hNplus.mul_const S).sub
      ((hNminus.mul_const K).mul hdisc) using 1 <;>
        first
        | rfl
        | (funext u; ring)
        | ring
  have hbalance := pdf_dPlus_dMinus_balance S K r σ τ hS hK hσ hτ
  have hcoeff :
      ((stdNormalPDF (dPlus S K r σ τ) * A) * S -
       ((stdNormalPDF (dMinus S K r σ τ) *
          (A - σ * (-1 / (2 * Real.sqrt τ)))) * K) * Real.exp (-r * τ) -
       (stdNormalCDF (dMinus S K r σ τ) * K) *
          (Real.exp (-r * τ) * r)) =
      -(S * stdNormalPDF (dPlus S K r σ τ) * σ) /
        (2 * Real.sqrt τ) -
        r * K * Real.exp (-r * τ) *
          stdNormalCDF (dMinus S K r σ τ) := by
    calc
      _ = (S * stdNormalPDF (dPlus S K r σ τ) -
           K * Real.exp (-r * τ) * stdNormalPDF (dMinus S K r σ τ)) * A -
          (K * Real.exp (-r * τ) * stdNormalPDF (dMinus S K r σ τ)) *
            (σ / (2 * Real.sqrt τ)) -
          r * K * Real.exp (-r * τ) *
            stdNormalCDF (dMinus S K r σ τ) := by ring
      _ = -(S * stdNormalPDF (dPlus S K r σ τ) * σ) /
            (2 * Real.sqrt τ) -
          r * K * Real.exp (-r * τ) *
            stdNormalCDF (dMinus S K r σ τ) := by
              rw [← hbalance]
              ring
  rw [hcoeff] at hprice
  simpa only [callPrice, τ] using hprice