-- Prove2me | solution 1 for BlackScholesModel.call_delta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T14:16:06.235097+00:00
-- url     : https://prove2.me/submissions/d8ad2774-5dbf-4e0c-8f4a-248c4491dc98

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_stdNormalCDF_hasDerivAt
import Theorems.Thm_BlackScholesModel_pdf_dPlus_dMinus_balance
import Theorems.Thm_BlackScholesModel_dPlus_hasDerivAt_spot

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (K r σ T S t : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hS : 0 < S) (ht : t < T) :
    HasDerivAt (fun S' => callPrice K r σ T S' t)
      (stdNormalCDF (dPlus S K r σ (T - t))) S := by
  let τ := T - t
  have hτ : 0 < τ := sub_pos.mpr ht
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hroot : Real.sqrt τ ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hτ)
  have hden : σ * Real.sqrt τ ≠ 0 :=
    mul_ne_zero (ne_of_gt hσ) hroot
  have hDplus : HasDerivAt (fun s => dPlus s K r σ τ)
      (1 / (S * σ * Real.sqrt τ)) S :=
    dPlus_hasDerivAt_spot S K r σ τ hS hK hσ hτ
  have hDminus : HasDerivAt (fun s => dMinus s K r σ τ)
      (1 / (S * σ * Real.sqrt τ)) S := by
    simpa only [dMinus, sub_eq_add_neg] using
      hDplus.add_const (-(σ * Real.sqrt τ))
  have houterPlus : HasDerivAt (fun z : ℝ => stdNormalCDF z)
      (stdNormalPDF (dPlus S K r σ τ)) (dPlus S K r σ τ) :=
    stdNormalCDF_hasDerivAt (dPlus S K r σ τ)
  have houterMinus : HasDerivAt (fun z : ℝ => stdNormalCDF z)
      (stdNormalPDF (dMinus S K r σ τ)) (dMinus S K r σ τ) :=
    stdNormalCDF_hasDerivAt (dMinus S K r σ τ)
  have hNplus : HasDerivAt
      (fun s => stdNormalCDF (dPlus s K r σ τ))
      (stdNormalPDF (dPlus S K r σ τ) *
        (1 / (S * σ * Real.sqrt τ))) S := by
    simpa only [Function.comp_def] using houterPlus.comp S hDplus
  have hNminus : HasDerivAt
      (fun s => stdNormalCDF (dMinus s K r σ τ))
      (stdNormalPDF (dMinus S K r σ τ) *
        (1 / (S * σ * Real.sqrt τ))) S := by
    simpa only [Function.comp_def] using houterMinus.comp S hDminus
  have hvalue : HasDerivAt
      (fun s : ℝ =>
        stdNormalCDF (dPlus s K r σ τ) * s -
        stdNormalCDF (dMinus s K r σ τ) * K *
          Real.exp (-r * τ))
      ((stdNormalPDF (dPlus S K r σ τ) *
          (1 / (S * σ * Real.sqrt τ))) * S +
        stdNormalCDF (dPlus S K r σ τ) * 1 -
        ((stdNormalPDF (dMinus S K r σ τ) *
          (1 / (S * σ * Real.sqrt τ))) * K) *
          Real.exp (-r * τ)) S :=
    (hNplus.mul (hasDerivAt_id S)).sub
      ((hNminus.mul_const K).mul_const (Real.exp (-r * τ)))
  have hbalance := pdf_dPlus_dMinus_balance
    S K r σ τ hS hK hσ hτ
  have hderivval :
      ((stdNormalPDF (dPlus S K r σ τ) *
          (1 / (S * σ * Real.sqrt τ))) * S +
        stdNormalCDF (dPlus S K r σ τ) * 1 -
        ((stdNormalPDF (dMinus S K r σ τ) *
          (1 / (S * σ * Real.sqrt τ))) * K) *
          Real.exp (-r * τ)) =
      stdNormalCDF (dPlus S K r σ τ) := by
    calc
      _ = (S * stdNormalPDF (dPlus S K r σ τ) -
            K * Real.exp (-r * τ) *
              stdNormalPDF (dMinus S K r σ τ)) *
          (1 / (S * σ * Real.sqrt τ)) +
        stdNormalCDF (dPlus S K r σ τ) := by ring
      _ = stdNormalCDF (dPlus S K r σ τ) := by
        rw [hbalance]
        ring
  rw [hderivval] at hvalue
  simpa only [callPrice, τ] using hvalue