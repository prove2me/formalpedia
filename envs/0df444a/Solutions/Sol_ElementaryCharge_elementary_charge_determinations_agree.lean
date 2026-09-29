-- Prove2me | solution 1 for ElementaryCharge.elementary_charge_determinations_agree
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:21:25.361992+00:00
-- url     : https://prove2.me/submissions/8cfef6fe-7e61-4122-8b3d-7fcc846abe6f

import Mathlib
import Definitions.Def_elementary_charge_si_constants

open ElementaryCharge

theorem W4a_ElementaryCharge_charge_from_josephson_von_klitzing (q hPlanck : ℝ) (hq : q ≠ 0)
    (hh : hPlanck ≠ 0) :
    2 / (josephsonConstant q hPlanck * vonKlitzingConstant q hPlanck) = q := by
  unfold josephsonConstant vonKlitzingConstant
  field_simp

theorem W4a_ElementaryCharge_charge_from_faraday_avogadro (NA q : ℝ) (hNA : NA ≠ 0) :
    faradayConstant NA q / NA = q := by
  unfold faradayConstant
  field_simp

theorem W4a_ElementaryCharge_charge_from_codata_relation (q hPlanck mu0 cLight alpha : ℝ)
    (hq : 0 < q) (hh : 0 < hPlanck) (hmu : 0 < mu0) (hc : 0 < cLight)
    (halpha : alpha = fineStructureConstant q hPlanck mu0 cLight) :
    Real.sqrt (2 * hPlanck * alpha / (mu0 * cLight)) = q := by
  have : 2 * hPlanck * alpha / (mu0 * cLight) = q ^ 2 := by
    rw [halpha]; unfold fineStructureConstant; field_simp
  rw [this, Real.sqrt_sq hq.le]

theorem solution (mu0 alpha : ℝ)
    (hmu : 0 < mu0)
    (halpha : alpha = fineStructureConstant eSI planckSI mu0 lightSpeedSI) :
    faradayConstant avogadroSI eSI = 964853321233100184 / 10 ^ 13 ∧
    faradayConstant avogadroSI eSI / avogadroSI = eSI ∧
    2 / (josephsonConstant eSI planckSI * vonKlitzingConstant eSI planckSI)
      = eSI ∧
    Real.sqrt (2 * planckSI * alpha / (mu0 * lightSpeedSI)) = eSI := by
  have he : (0 : ℝ) < eSI := by unfold eSI; norm_num
  have hh : (0 : ℝ) < planckSI := by unfold planckSI; norm_num
  have hN : (0 : ℝ) < avogadroSI := by unfold avogadroSI; norm_num
  have hc : (0 : ℝ) < lightSpeedSI := by unfold lightSpeedSI; norm_num
  refine ⟨?_, W4a_ElementaryCharge_charge_from_faraday_avogadro _ _ hN.ne',
    W4a_ElementaryCharge_charge_from_josephson_von_klitzing _ _ he.ne' hh.ne',
    W4a_ElementaryCharge_charge_from_codata_relation _ _ _ _ _ he hh hmu hc halpha⟩
  unfold faradayConstant avogadroSI eSI
  norm_num

theorem W4a_ElementaryCharge_charge_quantization_closure (S : Set ℝ) (q0 : ℝ)
    (hS : ∀ s ∈ S, ∃ n : ℤ, s = n * q0) :
    (AddSubgroup.closure S : Set ℝ) ⊆ (AddSubgroup.zmultiples q0 : Set ℝ) := by
  have hsub : S ⊆ (AddSubgroup.zmultiples q0 : Set ℝ) := by
    intro s hs
    obtain ⟨n, rfl⟩ := hS s hs
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by rw [zsmul_eq_mul]⟩
  intro x hx
  exact (AddSubgroup.closure_le _).mpr hsub hx

theorem W4a_ElementaryCharge_dirac_monopole_forces_quantization (Q : Set ℝ) (g hbar : ℝ)
    (hg : g ≠ 0)
    (hdirac : ∀ q ∈ Q, ∃ n : ℤ, q * g = n * (hbar / 2)) :
    ∀ q ∈ Q, ∃ n : ℤ, q = n * (hbar / (2 * g)) := by
  intro q hq
  obtain ⟨n, hn⟩ := hdirac q hq
  refine ⟨n, ?_⟩
  field_simp
  linear_combination 2 * hn

theorem W4a_ElementaryCharge_charge_eq_natural_unit_mul_sqrt_alpha
    (q eps0 hbar cLight alpha : ℝ)
    (hq : 0 < q) (hpos : 0 < 4 * Real.pi * eps0 * hbar * cLight)
    (halpha : alpha = q ^ 2 / (4 * Real.pi * eps0 * hbar * cLight)) :
    naturalUnitCharge eps0 hbar cLight * Real.sqrt alpha = q := by
  unfold naturalUnitCharge
  rw [← Real.sqrt_mul hpos.le, halpha]
  have : 4 * Real.pi * eps0 * hbar * cLight * (q ^ 2 / (4 * Real.pi * eps0 * hbar * cLight))
      = q ^ 2 := by
    generalize 4 * Real.pi * eps0 * hbar * cLight = X at hpos ⊢
    have hX := hpos.ne'
    field_simp
  rw [this, Real.sqrt_sq hq.le]
