-- Prove2me | solution 1 for GenFrameSpan.stepSat_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:24.847906+00:00
-- url     : https://prove2.me/submissions/8781118a-03a1-405d-bf2e-d0069bbdb2d6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatFin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW
namespace GenFrameSpan
theorem _root_.solution (hP : ProjZ) : StepSat := by
  intro hadm Lt _ _ l _ N0 nu P B hPmem hPc
  obtain ⟨T, hTmem, hTfix⟩ := hP hadm Lt N0 nu
  have ha : ∀ m, ∃ a : ColChoice N0 nu →₀ ℤ,
      (a.sum fun J k => k • nablaX N0 nu J) = T (MvPolynomial.monomial m 1) :=
    fun m => Finsupp.mem_span_range_iff_exists_finsupp.mp (hTmem _)
  choose a ha using ha
  let S : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
    (MvPolynomial.basisMonomials _ ℂ_[l]).constr ℂ_[l]
      fun m => MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1))
  have hS1 : ∀ m, S (MvPolynomial.monomial m 1) =
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
    intro m
    have h := (MvPolynomial.basisMonomials _ ℂ_[l]).constr_basis ℂ_[l]
      (fun m => MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1))) m
    simpa [MvPolynomial.coe_basisMonomials] using h
  have hSφ : ∀ Q : MvPolynomial (Lt × ℕ × Fin N0) ℤ,
      S (MvPolynomial.map (Int.castRingHom ℂ_[l]) Q) =
        MvPolynomial.map (Int.castRingHom ℂ_[l]) (T Q) := by
    intro Q
    induction Q using MvPolynomial.induction_on' with
    | monomial m k =>
      have hk : MvPolynomial.monomial m k = k • MvPolynomial.monomial m (1 : ℤ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hk]
      simp only [map_zsmul]
      rw [MvPolynomial.map_monomial, map_one, hS1]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  have hle : Submodule.span ℂ_[l] (Set.range fun J : ColChoice N0 nu =>
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)) ≤ LinearMap.eqLocus S LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨J, rfl⟩
    exact (LinearMap.mem_eqLocus).mpr (by rw [hSφ, hTfix]; rfl)
  have hSP : S P = P := (LinearMap.mem_eqLocus).mp (hle hPmem)
  have hSexp : S P = ∑ m ∈ P.support, MvPolynomial.coeff m P •
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
    conv_lhs => rw [MvPolynomial.as_sum P]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← hS1, ← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  let c : ColChoice N0 nu →₀ ℂ_[l] := ∑ m ∈ P.support,
    MvPolynomial.coeff m P • Finsupp.mapRange (Int.cast : ℤ → ℂ_[l]) Int.cast_zero (a m)
  have hc : ∀ J, c J = ∑ m ∈ P.support, MvPolynomial.coeff m P * (a m J : ℂ_[l]) := by
    intro J
    simp [c, Finsupp.finsetSum_apply]
  refine ⟨c, fun J => ?_, ?_⟩
  · rw [hc]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg l) _) fun m _ => ?_
    rw [norm_mul]
    calc ‖MvPolynomial.coeff m P‖ * ‖(a m J : ℂ_[l])‖ ≤ ‖MvPolynomial.coeff m P‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one _ _) (norm_nonneg _)
      _ ≤ (l : ℝ) ^ (-B) := by rw [mul_one]; exact hPc m
  · rw [← Finsupp.linearCombination_apply]
    have hΦ : ∀ m, Finsupp.linearCombination ℂ_[l]
        (fun J => MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J))
        (Finsupp.mapRange (Int.cast : ℤ → ℂ_[l]) Int.cast_zero (a m)) =
        MvPolynomial.map (Int.castRingHom ℂ_[l]) (T (MvPolynomial.monomial m 1)) := by
      intro m
      rw [← ha, Finsupp.linearCombination_apply, map_finsuppSum]
      rw [Finsupp.sum_mapRange_index (by intro; exact zero_smul _ _)]
      refine Finsupp.sum_congr fun J _ => ?_
      rw [map_zsmul, Int.cast_smul_eq_zsmul]
    simp only [c, map_sum, map_smul, hΦ]
    rw [← hSexp, hSP]
end GenFrameSpan
