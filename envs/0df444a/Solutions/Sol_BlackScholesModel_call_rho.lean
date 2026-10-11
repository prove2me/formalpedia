-- Prove2me | solution 1 for BlackScholesModel.call_rho
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T17:00:53.239119+00:00
-- url     : https://prove2.me/submissions/8dee16ee-5b3a-4dcb-8437-cf8316805b73

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
    HasDerivAt (fun r' => callPrice K r' σ T S t)
      (K * (T - t) * Real.exp (-r * (T - t)) *
        stdNormalCDF (dMinus S K r σ (T - t))) r := by
  let τ := T - t
  have hτ : 0 < τ := sub_pos.mpr ht
  have hlin : HasDerivAt
      (fun u : ℝ => (u + σ ^ 2 / 2) * τ) τ r := by
    convert ((hasDerivAt_id r).add_const (σ ^ 2 / 2)).mul_const τ using 1 <;>
      first
      | rfl
      | (funext x; dsimp [id]; ring)
      | ring
  have hnum : HasDerivAt
      (fun u : ℝ => Real.log (S / K) + (u + σ ^ 2 / 2) * τ)
      τ r := hlin.const_add _
  have hdplus : HasDerivAt
      (fun u : ℝ => dPlus S K u σ τ)
      (τ / (σ * Real.sqrt τ)) r := by
    simpa only [dPlus] using hnum.div_const (σ * Real.sqrt τ)
  have hdminus : HasDerivAt
      (fun u : ℝ => dMinus S K u σ τ)
      (τ / (σ * Real.sqrt τ)) r := by
    simpa only [dMinus, sub_eq_add_neg] using
      hdplus.add_const (-(σ * Real.sqrt τ))
  have houterPlus : HasDerivAt (fun z : ℝ => stdNormalCDF z)
      (stdNormalPDF (dPlus S K r σ τ)) (dPlus S K r σ τ) :=
    stdNormalCDF_hasDerivAt (dPlus S K r σ τ)
  have houterMinus : HasDerivAt (fun z : ℝ => stdNormalCDF z)
      (stdNormalPDF (dMinus S K r σ τ)) (dMinus S K r σ τ) :=
    stdNormalCDF_hasDerivAt (dMinus S K r σ τ)
  have hNplus : HasDerivAt
      (fun u => stdNormalCDF (dPlus S K u σ τ))
      (stdNormalPDF (dPlus S K r σ τ) *
        (τ / (σ * Real.sqrt τ))) r := by
    simpa only [Function.comp_def] using houterPlus.comp r hdplus
  have hNminus : HasDerivAt
      (fun u => stdNormalCDF (dMinus S K u σ τ))
      (stdNormalPDF (dMinus S K r σ τ) *
        (τ / (σ * Real.sqrt τ))) r := by
    simpa only [Function.comp_def] using houterMinus.comp r hdminus
  have hnegr : HasDerivAt (fun u : ℝ => -u * τ) (-τ) r := by
    convert (hasDerivAt_id r).neg.mul_const τ using 1 <;>
      first
      | rfl
      | (funext u; dsimp [id]; ring)
      | ring
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u * τ))
      (Real.exp (-r * τ) * (-τ)) r :=
    (Real.hasDerivAt_exp _).comp r hnegr
  have hprice : HasDerivAt (fun u : ℝ =>
      stdNormalCDF (dPlus S K u σ τ) * S -
      stdNormalCDF (dMinus S K u σ τ) * K * Real.exp (-u * τ))
      ((stdNormalPDF (dPlus S K r σ τ) *
          (τ / (σ * Real.sqrt τ))) * S -
       ((stdNormalPDF (dMinus S K r σ τ) *
          (τ / (σ * Real.sqrt τ))) * K) * Real.exp (-r * τ) -
       (stdNormalCDF (dMinus S K r σ τ) * K) *
          (Real.exp (-r * τ) * (-τ))) r := by
    convert (hNplus.mul_const S).sub ((hNminus.mul_const K).mul hexp) using 1 <;>
      first
      | rfl
      | ring
  have hbalance := pdf_dPlus_dMinus_balance
    S K r σ τ hS hK hσ hτ
  have hcoeff :
      ((stdNormalPDF (dPlus S K r σ τ) *
          (τ / (σ * Real.sqrt τ))) * S -
       ((stdNormalPDF (dMinus S K r σ τ) *
          (τ / (σ * Real.sqrt τ))) * K) * Real.exp (-r * τ) -
       (stdNormalCDF (dMinus S K r σ τ) * K) *
          (Real.exp (-r * τ) * (-τ))) =
      K * τ * Real.exp (-r * τ) *
        stdNormalCDF (dMinus S K r σ τ) := by
    calc
      _ = (S * stdNormalPDF (dPlus S K r σ τ) -
          K * Real.exp (-r * τ) * stdNormalPDF (dMinus S K r σ τ)) *
            (τ / (σ * Real.sqrt τ)) +
          K * τ * Real.exp (-r * τ) *
            stdNormalCDF (dMinus S K r σ τ) := by ring
      _ = K * τ * Real.exp (-r * τ) *
          stdNormalCDF (dMinus S K r σ τ) := by
            rw [hbalance]
            ring
  rw [hcoeff] at hprice
  simpa only [callPrice, τ] using hprice