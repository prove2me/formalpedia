-- Prove2me | solution 1 for BlackScholesModel.call_vega
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T17:23:32.770243+00:00
-- url     : https://prove2.me/submissions/683e5766-addf-429c-b545-05e8d07f4a73

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
    HasDerivAt (fun σ' => callPrice K r σ' T S t)
      (S * stdNormalPDF (dPlus S K r σ (T - t)) * Real.sqrt (T - t)) σ := by
  let τ := T - t
  have hτ : 0 < τ := sub_pos.mpr ht
  have hden0 : σ * Real.sqrt τ ≠ 0 :=
    mul_ne_zero (ne_of_gt hσ) (ne_of_gt (Real.sqrt_pos.2 hτ))
  have hNumRaw := (((hasDerivAt_id σ).pow 2).div_const (2 : ℝ)).mul_const τ
  have hNumRaw' : HasDerivAt
      (fun v : ℝ => (v ^ 2 / 2) * τ) (σ * τ) σ := by
    simpa [pow_one, mul_assoc, mul_comm, mul_left_comm] using hNumRaw
  have hNumEq :
      (fun v : ℝ => Real.log (S / K) + (r + v ^ 2 / 2) * τ) =
      (fun v : ℝ => (Real.log (S / K) + r * τ) + (v ^ 2 / 2) * τ) := by
    funext v
    ring
  have hNumPlus : HasDerivAt
      (fun v : ℝ => Real.log (S / K) + (r + v ^ 2 / 2) * τ)
      (σ * τ) σ := by
    rw [hNumEq]
    exact hNumRaw'.const_add (Real.log (S / K) + r * τ)
  have hDen : HasDerivAt
      (fun v : ℝ => v * Real.sqrt τ) (Real.sqrt τ) σ := by
    simpa only [id, one_mul] using
      (hasDerivAt_id σ).mul_const (Real.sqrt τ)
  let A : ℝ :=
    ((σ * τ) * (σ * Real.sqrt τ) -
      (Real.log (S / K) + (r + σ ^ 2 / 2) * τ) * Real.sqrt τ) /
        (σ * Real.sqrt τ) ^ 2
  have hdPlus : HasDerivAt
      (fun v : ℝ => dPlus S K r v τ) A σ := by
    convert hNumPlus.div hDen hden0 using 1 <;>
      first
      | rfl
      | (funext v; (try { dsimp [dPlus] }); ring)
      | ((try { dsimp [dPlus, A] }); ring)
  have hdMinus : HasDerivAt
      (fun v : ℝ => dMinus S K r v τ) (A - Real.sqrt τ) σ := by
    convert hdPlus.sub hDen using 1 <;>
      first
      | rfl
      | (funext v; (try { dsimp [dMinus] }); ring)
      | ((try { dsimp [dMinus, A] }); ring)
  have houterPlus : HasDerivAt (fun z : ℝ => stdNormalCDF z)
      (stdNormalPDF (dPlus S K r σ τ)) (dPlus S K r σ τ) :=
    stdNormalCDF_hasDerivAt (dPlus S K r σ τ)
  have houterMinus : HasDerivAt (fun z : ℝ => stdNormalCDF z)
      (stdNormalPDF (dMinus S K r σ τ)) (dMinus S K r σ τ) :=
    stdNormalCDF_hasDerivAt (dMinus S K r σ τ)
  have hNplus : HasDerivAt
      (fun v : ℝ => stdNormalCDF (dPlus S K r v τ))
      (stdNormalPDF (dPlus S K r σ τ) * A) σ := by
    simpa only [Function.comp_def] using houterPlus.comp σ hdPlus
  have hNminus : HasDerivAt
      (fun v : ℝ => stdNormalCDF (dMinus S K r v τ))
      (stdNormalPDF (dMinus S K r σ τ) * (A - Real.sqrt τ)) σ := by
    simpa only [Function.comp_def] using houterMinus.comp σ hdMinus
  have hprice : HasDerivAt
      (fun v : ℝ =>
        stdNormalCDF (dPlus S K r v τ) * S -
        stdNormalCDF (dMinus S K r v τ) * K * Real.exp (-r * τ))
      ((stdNormalPDF (dPlus S K r σ τ) * A) * S -
       ((stdNormalPDF (dMinus S K r σ τ) *
          (A - Real.sqrt τ)) * K) * Real.exp (-r * τ)) σ := by
    convert (hNplus.mul_const S).sub
      ((hNminus.mul_const K).mul_const (Real.exp (-r * τ))) using 1 <;>
        first
        | rfl
        | (funext v; ring)
        | ring
  have hbalance := pdf_dPlus_dMinus_balance
    S K r σ τ hS hK hσ hτ
  have hcoeff :
      ((stdNormalPDF (dPlus S K r σ τ) * A) * S -
       ((stdNormalPDF (dMinus S K r σ τ) *
          (A - Real.sqrt τ)) * K) * Real.exp (-r * τ)) =
       S * stdNormalPDF (dPlus S K r σ τ) * Real.sqrt τ := by
    calc
      _ = (S * stdNormalPDF (dPlus S K r σ τ) -
           K * Real.exp (-r * τ) * stdNormalPDF (dMinus S K r σ τ)) * A +
          (K * Real.exp (-r * τ) * stdNormalPDF (dMinus S K r σ τ)) *
             Real.sqrt τ := by ring
      _ = S * stdNormalPDF (dPlus S K r σ τ) * Real.sqrt τ := by
        rw [hbalance]
        ring
  rw [hcoeff] at hprice
  simpa only [callPrice, τ] using hprice