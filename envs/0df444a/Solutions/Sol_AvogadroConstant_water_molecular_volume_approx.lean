-- Prove2me | solution 1 for AvogadroConstant.water_molecular_volume_approx
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:18:28.953357+00:00
-- url     : https://prove2.me/submissions/09c0f4d5-b60a-4a77-a303-c5d68288422a

import Mathlib
import Definitions.Def_AvogadroConstant_model

open AvogadroConstant

theorem W4a_AvogadroConstant_crystal_amountOfSubstance
    (U : MassAmountUnits) (V vCell : ℝ) (k : ℕ) (hvCell : 0 < vCell) :
    amountOfSubstance (avogadroConstant U) (crystalEntityCount V vCell k)
      = (k : ℝ) * V / (vCell * avogadroNumber) * U.mole := by
  have hN := avogadroNumber_pos.ne'
  have hm := U.mole_pos.ne'
  have hv := hvCell.ne'
  unfold amountOfSubstance avogadroConstant crystalEntityCount
  field_simp

theorem solution
    (U : MassAmountUnits) (mL nm3 v : ℝ) (hnm3 : 0 < nm3) (hmL : mL = 10 ^ 21 * nm3)
    (hv : molarVolume (avogadroConstant U) v * U.mole = 18 * mL) :
    0.0298 * nm3 < v ∧ v < 0.0300 * nm3 := by
  have hm := U.mole_pos.ne'
  have hv' : molarVolume (avogadroConstant U) v * U.mole = v * 602214076e15 := by
    unfold molarVolume avogadroConstant avogadroNumber
    rw [mul_assoc, div_mul_cancel₀ _ hm]
    norm_num
  have hv2 : v * 602214076e15 = 18 * 10 ^ 21 * nm3 := by
    rw [hmL] at hv
    linarith
  constructor <;> nlinarith

theorem W4a_AvogadroConstant_molarMass_carbon12_pre2019
    (U : MassAmountUnits) (NA : ℝ) (hNA : NA = U.gram / U.dalton / U.mole) :
    molarMass NA (12 * U.dalton) = 12 * U.gram / U.mole := by
  have hm := U.mole_pos.ne'
  have hd := U.dalton_pos.ne'
  subst hNA
  unfold molarMass
  field_simp

theorem W4a_AvogadroConstant_mole_eq (U : MassAmountUnits) :
    U.mole = avogadroNumber * elementaryAmount (avogadroConstant U) := by
  have hN := avogadroNumber_pos.ne'
  have hm := U.mole_pos.ne'
  unfold elementaryAmount avogadroConstant
  field_simp

theorem W4a_AvogadroConstant_molarMass_mul_mole (U : MassAmountUnits) (m : ℝ) :
    molarMass (avogadroConstant U) m * U.mole = avogadroNumber * m := by
  have hm := U.mole_pos.ne'
  unfold molarMass avogadroConstant
  field_simp

theorem W4a_AvogadroConstant_amount_mul (U : MassAmountUnits) (N : ℝ) :
    amountOfSubstance (avogadroConstant U) N * avogadroConstant U = N := by
  have h := (avogadroConstant_pos U).ne'
  unfold amountOfSubstance
  field_simp

theorem W4a_AvogadroConstant_avogadroNumber_eq_gram_div_dalton
    (U : MassAmountUnits) (mC12 : ℝ) (hmC12 : 0 < mC12) (N : ℝ)
    (hmole : N * mC12 = 12 * U.gram) (hdalton : U.dalton = mC12 / 12) :
    N = U.gram / U.dalton := by
  rw [hdalton, eq_div_iff (by positivity)]
  linarith
