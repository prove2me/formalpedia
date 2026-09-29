-- Prove2me | solution 1 for CuspForm.dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d75cfb43-a6eb-565a-9596-f447a0b070d5

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_CuspForm_IntegralLattice
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_CuspForm_dvd_mul_qCoeff_discriminant_prime_of_qCoeff_congr_sigmaPrimeTo
import Theorems.Thm_CuspForm_dvd_mul_qCoeff_discriminant_prime_sq_sub_pow_of_qCoeff_congr_sigmaPrimeTo
import Theorems.Thm_ModularCurve_qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven
import Theorems.Thm_CuspForm_not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo
import Theorems.Thm_ModularCurve_dvd_sq_sub_one_div_of_isCoprime_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo
p2m_attr_erase "simp" "ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve

theorem solution (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hIB : CuspForm.HasIntegralBasis p) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (hf : f ∈ CuspForm.qIntegralSet p) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (h1 : IsCoprime (af 1) (m : ℤ)) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) :
    m ∣ (p ^ 2 - 1) / 24 := by
  have _ := hIB
  have _ := hf
  have ht : ∀ n : ℕ, ((PowerSeries.coeff n (PowerSeries.X * ModularCurve.dedekindEtaUnit) : ℤ) : ℂ)
      = ModularFormClass.qCoeff ModularForm.discriminant n := by
    intro n
    show _ = (UpperHalfPlane.qExpansion 1 ModularForm.discriminant).coeff n
    rw [ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, PowerSeries.coeff_map]
    rfl
  have hC1 := CuspForm.dvd_mul_qCoeff_discriminant_prime_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf hcongr _ ht
  have hC2 := CuspForm.dvd_mul_qCoeff_discriminant_prime_sq_sub_pow_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf hcongr _ ht
  have hH := ModularCurve.qCoeff_discriminant_prime_sq_eq_sq_sub_pow_eleven p _ ht
  have hpm := CuspForm.not_prime_dvd_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf h1 hcongr
  have hC2' : (24 * m : ℤ) ∣ af 1 * ((p : ℤ) - 1)
      * ((PowerSeries.coeff p (PowerSeries.X * ModularCurve.dedekindEtaUnit)) ^ 2 - (p : ℤ) ^ 11 * ((p : ℤ) + 1)) := by
    have hrw : (PowerSeries.coeff (p ^ 2) (PowerSeries.X * ModularCurve.dedekindEtaUnit) : ℤ) - (p : ℤ) ^ 12
        = (PowerSeries.coeff p (PowerSeries.X * ModularCurve.dedekindEtaUnit)) ^ 2 - (p : ℤ) ^ 11 * ((p : ℤ) + 1) := by
      rw [hH]; ring
    rw [← hrw]; exact hC2
  exact ModularCurve.dvd_sq_sub_one_div_of_isCoprime_of_not_dvd p m Fact.out (af 1) _ h1 hpm hC1 hC2'

end S_CuspForm_dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo
end P2MW
export P2MW.S_CuspForm_dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo (solution)
