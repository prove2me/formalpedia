-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_radial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:34.535067+00:00
-- url     : https://prove2.me/submissions/955857b3-8aac-4fc0-b987-a55d53b37a02

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_finrank_real
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_unit_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (d r : ℕ) (hr : r ≤ d) (R : ℝ) (hR : 0 < R) :
    ∫⁻ x : EuclideanSpace ℂ (Fin (d + 1)),
      ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * (d - r)))⁻¹ else 0) =
    ENNReal.ofReal (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) := by
  let φ : ℝ → ℝ := fun ρ => if ρ ≤ R then (ρ ^ (2 * (d - r)))⁻¹ else 0
  let ψ : ℝ → ℝ := (Ioc 0 R).indicator (fun ρ => ρ ^ (2 * r + 1))
  have hD := s5b7_finrank_real (d + 1)
  have heq : EqOn (fun ρ : ℝ => ρ ^ (finrank ℝ (EuclideanSpace ℂ (Fin (d + 1))) - 1) • φ ρ) ψ
      (Ioi 0) := by
    intro ρ hρ
    have hρ0 : (0 : ℝ) < ρ := hρ
    simp only [φ, ψ, hD, smul_eq_mul]
    by_cases h : ρ ≤ R
    · have hm : ρ ∈ Ioc 0 R := ⟨hρ0, h⟩
      rw [if_pos h, indicator_of_mem hm]
      have e : 2 * (d + 1) - 1 = 2 * (d - r) + (2 * r + 1) := by omega
      rw [e, pow_add]
      field_simp
    · have hm : ρ ∉ Ioc 0 R := fun hh => h hh.2
      rw [if_neg h, indicator_of_notMem hm, mul_zero]
  have hψ : Integrable ψ := by
    refine (IntegrableOn.integrable_indicator ?_ measurableSet_Ioc)
    exact (continuous_pow _).integrableOn_Ioc
  have hint : Integrable (fun x : EuclideanSpace ℂ (Fin (d + 1)) => φ ‖x‖) := by
    rw [integrable_fun_norm_addHaar volume]
    exact (hψ.integrableOn).congr_fun heq.symm measurableSet_Ioi
  have hval : ∫ x : EuclideanSpace ℂ (Fin (d + 1)), φ ‖x‖ =
      Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1) := by
    rw [integral_fun_norm_addHaar volume φ, setIntegral_congr_fun measurableSet_Ioi heq,
      s5b7_unit_ball, hD]
    have h3 : ∫ ρ in Ioi (0 : ℝ), ψ ρ = R ^ (2 * r + 2) / (2 * (r : ℝ) + 2) := by
      simp only [ψ]
      rw [setIntegral_indicator measurableSet_Ioc]
      have : Ioi (0 : ℝ) ∩ Ioc 0 R = Ioc 0 R := by
        ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; tauto
      rw [this, ← intervalIntegral.integral_of_le hR.le, integral_pow]
      simp
      ring
    rw [h3, Nat.factorial_succ]
    simp only [nsmul_eq_mul, smul_eq_mul]
    push_cast
    field_simp
  rw [← hval]
  refine (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => ?_)).symm
  simp only [φ, Pi.zero_apply]
  split_ifs
  · positivity
  · exact le_rfl
end Formalism.HermitianLatticeCounting.P
