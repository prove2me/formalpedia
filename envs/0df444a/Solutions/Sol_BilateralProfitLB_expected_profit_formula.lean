-- Prove2me | solution 1 for BilateralProfitLB.expected_profit_formula
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T13:14:40.139444+00:00
-- url     : https://prove2.me/submissions/806ca7dd-cff5-43d4-aab7-a9adf8d06369

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction
import Definitions.Def_BilateralProfitLB_Stochastic
import Theorems.Thm_BilateralProfitLB_claim_7_3


section BundlePart000


namespace BilateralProfitLB

open MeasureTheory BilateralProfit

local notation "U01" => Set.Icc (0 : ℝ) 1
private noncomputable abbrev buyer (K j : ℕ) : Measure ℝ :=
  (volume.restrict U01).withDensity (fun b => ENNReal.ofReal (fB K j b))

private theorem trades_eq_rectangle (p q : ℝ) : {v | Trades v (p, q)} = Set.Iic p ×ˢ Set.Ici q := by
  rfl

private theorem integral_profit_eq_muP (D : Measure (ℝ × ℝ)) (p q : ℝ) :
    (∫ v, profit v (p, q) ∂D) = muP D (p, q) := by
  have hprofit : (fun v => profit v (p, q)) =
      (Set.Iic p ×ˢ Set.Ici q).indicator (fun _ => q - p) := by
    funext v
    by_cases hv : v ∈ Set.Iic p ×ˢ Set.Ici q
    · have ht : Trades v (p, q) := hv
      simp [profit, tradeBit, hv, ht]
    · have ht : ¬Trades v (p, q) := hv
      simp [profit, tradeBit, hv, ht]
  rw [hprofit, integral_indicator_const _ (measurableSet_Iic.prod measurableSet_Ici)]
  rw [muP, Ptrade, trades_eq_rectangle, measureReal_def, smul_eq_mul]
  exact mul_comm _ _

private theorem uniform_Iic {p : ℝ} (hp : p ∈ U01) :
    (volume.restrict U01) (Set.Iic p) = ENNReal.ofReal p := by
  rw [Measure.restrict_apply measurableSet_Iic]
  have hc : Set.Iic p ∩ U01 = Set.Icc 0 p := by
    ext x
    exact ⟨fun hx => ⟨hx.2.1, hx.1⟩, fun hx => ⟨hx.2, hx.1, hx.2.trans hp.2⟩⟩
  rw [hc, Real.volume_Icc, sub_zero]

private theorem muP_of_survival {K j : ℕ} [IsFiniteMeasure (buyer K j)]
    {p q : ℝ} (hp : p ∈ U01) (hs : (buyer K j) (Set.Ici q) = ENNReal.ofReal (S K j q))
    (hS : 0 ≤ S K j q) :
    muP (law K j) (p, q) = (q - p) * p * S K j q := by
  unfold muP Ptrade law
  rw [trades_eq_rectangle, Measure.prod_prod, uniform_Iic hp, hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.1, ENNReal.toReal_ofReal hS]
  ring

private theorem half_mem {q : ℝ} (hq : q ∈ U01) : q / 2 ∈ U01 :=
  ⟨by linarith [hq.1], by linarith [hq.2]⟩

private theorem profit_formula_of_survival {K j : ℕ} [IsFiniteMeasure (buyer K j)]
    {p q : ℝ} (hp : p ∈ U01) (hq : q ∈ U01)
    (hs : (buyer K j) (Set.Ici q) = ENNReal.ofReal (S K j q)) (hS : 0 ≤ S K j q) :
    (∫ v, profit v (p, q) ∂(law K j)) = (q - p) * p * S K j q ∧
      muP (law K j) (p, q) = (q - p) * p * S K j q ∧
      h K j q = q ^ 2 / 4 * S K j q ∧
      (∫ v, profit v (p, q) ∂(law K j)) ≤ h K j q := by
  have hmu := muP_of_survival hp hs hS
  have hh : h K j q = q ^ 2 / 4 * S K j q := by
    unfold h
    rw [muP_of_survival (half_mem hq) hs hS]
    ring
  refine ⟨(integral_profit_eq_muP _ _ _).trans hmu, hmu, hh, ?_⟩
  rw [integral_profit_eq_muP, hmu, hh]
  have hpq : (q - p) * p ≤ q ^ 2 / 4 := by nlinarith [sq_nonneg (p - q / 2)]
  exact mul_le_mul_of_nonneg_right hpq hS

end BilateralProfitLB
end BundlePart000


section BundlePart001



open Set Filter MeasureTheory
open scoped ENNReal

namespace BilateralProfitLB

open MechanismDesign.BilateralTrade

private abbrev HardLawClaim : Prop :=
  ∀ K : ℕ, 1 ≤ K → ∀ j : ℕ, j ≤ K →
    ∃ E : Environment, UnitSupport E ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, E.fS x = 1) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, E.fB b = fB K j b) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, 1 - E.cdfB b = S K j b) ∧
      E.prior = law K j ∧ E.Regular

private theorem densityEnvironment_integrable {E : Environment} (hE : UnitSupport E) :
    IntegrableOn E.fB (Icc (0 : ℝ) 1) := by
  have hi : IntervalIntegrable E.fB volume 0 1 :=
    hE.2.2.1 ▸ hE.2.2.2 ▸ E.fB_intervalIntegrable
  exact (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).2 hi.1

private theorem densityEnvironment_integral {E : Environment} (hE : UnitSupport E) :
    ∫ x in (0 : ℝ)..1, E.fB x = 1 :=
  hE.2.2.1 ▸ hE.2.2.2 ▸ E.fB_integral

private theorem densityEnvironment_linIcc {E : Environment} {K j : ℕ}
    (hE : UnitSupport E) (hB : ∀ b ∈ Icc (0 : ℝ) 1, E.fB b = fB K j b)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ∫⁻ x in Icc q 1, ENNReal.ofReal (fB K j x) =
      ENNReal.ofReal (∫ x in q..1, E.fB x) := by
  have hsub : Icc q 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_left hq.1
  have hi : IntegrableOn E.fB (Icc q 1) :=
    (densityEnvironment_integrable hE).mono_set hsub
  have hnon : 0 ≤ᵐ[volume.restrict (Icc q 1)] E.fB := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    apply le_of_lt
    apply E.fB_pos
    rw [hE.2.2.1, hE.2.2.2]
    exact hsub hx
  rw [intervalIntegral.integral_of_le hq.2, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hi hnon]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [hB x (hsub hx)]

private theorem densityEnvironment_tail {E : Environment} {K j : ℕ} (hE : UnitSupport E)
    (hS : ∀ b ∈ Icc (0 : ℝ) 1, 1 - E.cdfB b = S K j b) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ∫ x in q..1, E.fB x = S K j q := by
  have hi := densityEnvironment_integrable hE
  have hin₁ : IntervalIntegrable E.fB volume 0 q := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hq.1]
    exact hi.mono_set (Icc_subset_Icc_right hq.2)
  have hin₂ : IntervalIntegrable E.fB volume q 1 := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hq.2]
    exact hi.mono_set (Icc_subset_Icc_left hq.1)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hin₁ hin₂
  rw [densityEnvironment_integral hE] at hsum
  have hs := hS q hq
  rw [Environment.cdfB, hE.2.2.1] at hs
  linarith

private theorem S_nonneg_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ} (hK : 1 ≤ K)
    (hj : j ≤ K) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ S K j q := by
  obtain ⟨E, hE, _, _, hS, _, _⟩ := hClaim K hK j hj
  rw [← densityEnvironment_tail hE hS hq]
  apply intervalIntegral.integral_nonneg hq.2
  intro b hb
  have hb' : b ∈ Icc E.loB E.hiB := by
    rw [hE.2.2.1, hE.2.2.2]
    exact ⟨hq.1.trans hb.1, hb.2⟩
  exact (E.fB_pos b hb').le

private theorem buyerMeasure_Ici_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ}
    (hK : 1 ≤ K) (hj : j ≤ K) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b))
      (Ici q) = ENNReal.ofReal (S K j q) := by
  obtain ⟨E, hE, _, hB, hS, _, _⟩ := hClaim K hK j hj
  have hh : Ici q ∩ Icc (0 : ℝ) 1 = Icc q 1 := by
    ext b
    exact ⟨fun ⟨h, _, h₁⟩ => ⟨h, h₁⟩, fun ⟨h, h₁⟩ => ⟨h, hq.1.trans h, h₁⟩⟩
  rw [withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    hh, densityEnvironment_linIcc hE hB hq, densityEnvironment_tail hE hS hq]

private theorem buyerMeasure_inUnit_of_claim_7_3 (hClaim : HardLawClaim) {K j : ℕ}
    (hK : 1 ≤ K) (hj : j ≤ K) :
    ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (fB K j x) = 1 := by
  obtain ⟨E, hE, _, hB, _, _, _⟩ := hClaim K hK j hj
  rw [densityEnvironment_linIcc hE hB (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩),
    densityEnvironment_integral hE, ENNReal.ofReal_one]

private theorem buyerMeasure_isProbabilityMeasure_of_claim_7_3 (hClaim : HardLawClaim)
    {K j : ℕ} (hK : 1 ≤ K) (hj : j ≤ K) :
    IsProbabilityMeasure
      ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    buyerMeasure_inUnit_of_claim_7_3 hClaim hK hj]

end BilateralProfitLB
end BundlePart001


section BundlePart002




namespace BilateralProfitLB

open MeasureTheory BilateralProfit

private theorem expected_profit_formula_from_claim_7_3 (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj : j ≤ K)
    (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (∫ v, profit v (p, q) ∂(law K j)) = (q - p) * p * S K j q ∧
      muP (law K j) (p, q) = (q - p) * p * S K j q ∧
      h K j q = q ^ 2 / 4 * S K j q ∧
      (∫ v, profit v (p, q) ∂(law K j)) ≤ h K j q := by
  let := buyerMeasure_isProbabilityMeasure_of_claim_7_3 claim_7_3 hK hj
  exact profit_formula_of_survival hp hq (buyerMeasure_Ici_of_claim_7_3 claim_7_3 hK hj hq)
    (S_nonneg_of_claim_7_3 claim_7_3 hK hj hq)

end BilateralProfitLB
end BundlePart002

open BilateralProfitLB
open MeasureTheory BilateralProfit

theorem solution (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj : j ≤ K) (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (∫ v, profit v (p, q) ∂(law K j)) = (q - p) * p * S K j q ∧
      muP (law K j) (p, q) = (q - p) * p * S K j q ∧
      h K j q = q ^ 2 / 4 * S K j q ∧
      (∫ v, profit v (p, q) ∂(law K j)) ≤ h K j q := by
  exact BilateralProfitLB.expected_profit_formula_from_claim_7_3 K hK j hj p q hp hq
