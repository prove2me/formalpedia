-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.divided_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:26:42.452811+00:00
-- url     : https://prove2.me/submissions/0c2bb6e4-f984-48da-8d92-c290b8ded1d6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_IntegralPderivLgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_bd_pow_incr
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_natCast
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_sm_mul


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_mul bd_C bd_sum int_mul int_pow sm_mul bd_natCast frob_congr
  PhiH PhiH_apply)
open DividedPowerNorms
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : DivDeriv := by
  intro K ι κ _ _ _ _ _ p hp hnp x Φ φ Y hΦ hφ0 hφ hY0 hY n
  classical
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  set φ' := Function.update φ x (φ x + MvPowerSeries.C (p : K) * Y) with hφ'
  have hs : MvPowerSeries.HasSubst φ := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have hs' : MvPowerSeries.HasSubst φ' := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => ?_
    by_cases h : i = x
    · subst h
      simp [hφ', hφ0, hY0]
    · simp [hφ', Function.update_of_ne h, hφ0]
  rw [map_sub, MvPowerSeries.coeff_subst hs', MvPowerSeries.coeff_subst hs,
    ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite hs' Φ n)
      (MvPowerSeries.coeff_subst_finite hs Φ n)]
  refine Formalism.DworkPowerSeriesWeights.norm_finsum_le_of hpos fun d => ?_
  have e1 : ∀ ψ : ι → MvPowerSeries κ K, (d.prod fun s e => ψ s ^ e) =
      ψ x ^ d x * (d.erase x).prod fun s e => ψ s ^ e := fun ψ =>
    (Finsupp.mul_prod_erase' d x (fun s e => ψ s ^ e) fun _ => pow_zero _).symm
  have e2 : ((d.erase x).prod fun s e => φ' s ^ e) = (d.erase x).prod fun s e => φ s ^ e := by
    refine Finsupp.prod_congr fun s hs => ?_
    have : s ≠ x := by
      rintro rfl
      simp at hs
    rw [hφ', Function.update_of_ne this]
  have hR : Bd 1 ((d.erase x).prod fun s e => φ s ^ e) := by
    unfold Finsupp.prod
    refine Finset.prod_induction _ (Bd 1) (fun a b ha hb => int_mul ha hb) DworkIntegrality.bd_one
      fun s _ => int_pow (hφ s) _
  have hc : ‖(d x : K) * MvPowerSeries.coeff d Φ‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos (d x) with h0 | h0
    · simp [h0]
    · have h1 := hΦ (d - Finsupp.single x 1)
      rw [MvPowerSeries.coeff_pderiv] at h1
      have h2 : d - Finsupp.single x 1 + Finsupp.single x 1 = d := by
        ext s
        by_cases h : s = x
        · subst h
          simp
          omega
        · simp [Ne.symm h]
      have h3 : (((d - Finsupp.single x 1 : ι →₀ ℕ) x : ℕ) : K) + 1 = (d x : K) := by
        have : (d - Finsupp.single x 1 : ι →₀ ℕ) x + 1 = d x := by
          simp
          omega
        exact_mod_cast this
      rw [h2, h3, mul_comm] at h1
      exact h1
  have e3 : MvPowerSeries.coeff d Φ • MvPowerSeries.coeff n (d.prod fun s e => φ' s ^ e) -
      MvPowerSeries.coeff d Φ • MvPowerSeries.coeff n (d.prod fun s e => φ s ^ e) =
      MvPowerSeries.coeff n (MvPowerSeries.C (MvPowerSeries.coeff d Φ) *
        ((φ x + MvPowerSeries.C (p : K) * Y) ^ d x - φ x ^ d x) *
          (d.erase x).prod fun s e => φ s ^ e) := by
    rw [e1 φ', e1 φ, e2, mul_assoc, MvPowerSeries.coeff_C_mul, sub_mul, map_sub, smul_eq_mul,
      smul_eq_mul, mul_sub]
    simp [hφ']
  rw [e3]
  exact sm_mul hpos (bd_pow_incr hp hnp (hφ x) hY _ _ hc) hR n
end Formalism.InvariantFactorPaths.G7
