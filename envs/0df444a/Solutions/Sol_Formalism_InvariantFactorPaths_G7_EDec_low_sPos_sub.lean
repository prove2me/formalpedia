-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EDec.low_sPos_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:45:00.854871+00:00
-- url     : https://prove2.me/submissions/4f0d7f64-ff9a-410e-977c-6f12e3fa8920

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_of_zero
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_of_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_symm
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_coeff_sPos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_nonneg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_powq


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
open Formalism.DworkPowerSeriesWeights (Integral low_subst_of_low)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_mul low_pow low_one_iff low_mul_sub
  low_of_zero)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one)
open TwoS (Cg cg_refl cg_of_eq cg_symm cg_trans cg_add cg_sum cg_mul cg_pow cg_frob_add cg_frob_sum
  integral_add integral_neg integral_sum integral_C integral_X integral_zero coeff_sPos pinv_nonneg)
open Formalism.InvariantFactorPaths.G7.EDec
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.EDec
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (E : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    Low ((p ^ 2) ^ E) (sPos (K := K) p s ab - sT p E s ab) := by
  classical
  intro n hn
  have key : ∀ l : ℕ, n = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l) →
      l < n.degree + 1 ∧ l < E := by
    intro l e
    have hd : n.degree = (p ^ 2) ^ l := by rw [e, Finsupp.degree_single]
    refine ⟨by rw [hd]; exact lt_powq hp l, ?_⟩
    rw [hd] at hn
    exact (Nat.pow_lt_pow_iff_right (show 1 < p ^ 2 by nlinarith)).1 hn
  rw [map_sub, coeff_sPos, sT, map_sum, sub_eq_zero]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow]
  calc _ = ∑ l ∈ range (E + n.degree + 1),
        (if n = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l) then (-1 : K) ^ l
          else 0) :=
        Finset.sum_subset (Finset.range_mono (by omega))
          fun l _ hl => if_neg fun e => hl (mem_range.2 (key l e).1)
    _ = ∑ l ∈ range E,
        (if n = Finsupp.single (s - 2 * (l : ZMod (2 * ν)), ab) ((p ^ 2) ^ l) then (-1 : K) ^ l
          else 0) :=
        (Finset.sum_subset (Finset.range_mono (by omega))
          fun l _ hl => if_neg fun e => hl (mem_range.2 (key l e).2)).symm
    _ = _ := Finset.sum_congr rfl fun l _ => by split_ifs <;> simp
end Formalism.InvariantFactorPaths.G7.EDec
