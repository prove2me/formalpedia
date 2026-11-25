-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.base_case_false_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:56.864899+00:00
-- url     : https://prove2.me/submissions/d81227fa-2768-4eb2-8d09-e04e7d1b9937

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_coeff_frob_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
namespace Formalism.BaseCaseIdentities
theorem _root_.solution : BaseCaseFalse := by
  intro l i hl hl3 hi hi3
  refine ⟨exData l i hl hl3 hi, rfl, rfl, ?_⟩
  have : Fact l.Prime := ⟨hl⟩
  intro hW
  have hK : (1 : ℕ) < Kn i := by
    unfold Kn
    omega
  have h1 := hW.1 (1 : Fin 2) hK
  have hq : 1 ≤ l ^ 2 := Nat.one_le_pow _ _ (by omega)

  have hz1 : (exData l i hl hl3 hi).zvec 1 = 0 := by
    simp [Data.zvec, exData]
  have hz0 : (exData l i hl hl3 hi).zvec 0 = X () := by
    simp [Data.zvec, exData]
  have hm : (exData l i hl hl3 hi).m 1 1 = MvPowerSeries.C (-(l : ℚ)⁻¹) * frob (l ^ 2) (X ()) := by
    show MvPowerSeries.C (-(l : ℚ)⁻¹) * ∑ c : Fin 2, frob (l ^ 2) ((exData l i hl hl3 hi).zvec c) *
      MvPowerSeries.C ((exData l i hl hl3 hi).g c 1) = _
    rw [Fin.sum_univ_two, hz0, hz1]
    simp [exData]
  have h2 := h1 ((l ^ 2) • Finsupp.single () 1)
  have hlev : (exData l i hl hl3 hi).lev 1 = 1 := rfl
  rw [hlev, hz1, hm, zero_sub, ← neg_mul, ← map_neg, neg_neg, coeff_C_mul,
    coeff_frob_smul _ hq] at h2
  have hX : coeff (Finsupp.single () 1) (X () : MvPowerSeries Unit ℚ) = 1 := by
    simp [coeff_X]
  rw [hX, one_pow, mul_one] at h2
  have hv : (exData l i hl hl3 hi).v (l : ℚ)⁻¹ = ((-1 : ℝ) : WithTop ℝ) := ratVal_l_inv l
  rw [hv, ← WithTop.coe_add, WithTop.coe_le_coe] at h2
  have hdeg : (((l ^ 2) • Finsupp.single () 1 : Unit →₀ ℕ).degree : ℕ) = l ^ 2 := by
    simp
  rw [hdeg] at h2
  simp only [Data.top, Data.rad] at h2
  have hl' : (exData l i hl hl3 hi).l = l := rfl
  have hi' : (exData l i hl hl3 hi).i = i := rfl
  rw [hl', hi'] at h2

  have hlR : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl3
  have hq1 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hrho : ((l ^ 2 : ℕ) : ℝ) * rho l = 1 + rho l := by
    unfold rho
    push_cast
    field_simp
    ring
  have hpow : (l : ℝ) ^ 3 ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi3
  have hLpos : (0 : ℝ) < (l : ℝ) ^ i := by positivity
  have hsg : ((l ^ 2 : ℕ) : ℝ) * sg l i < 1 := by
    unfold sg
    push_cast
    rw [mul_div_assoc', div_lt_one (by positivity)]
    nlinarith [sq_nonneg (l : ℝ)]
  nlinarith
end Formalism.BaseCaseIdentities
