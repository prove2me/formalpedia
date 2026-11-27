-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ChG.exp_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:23:45.288065+00:00
-- url     : https://prove2.me/submissions/64de0670-4a97-408f-aeb8-fd9a60d165e6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffPderivUncurry
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_step
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mvExp_linF_step
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_zero_mvExp
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.L2.FormalSeriesBounds.ChG
variable {K : Type} [Field K] [CharZero K] {τ : Type} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds.ChG
theorem _root_.solution (y : τ → K) (Ψ : MvPowerSeries τ K) (h0 : MvPowerSeries.constantCoeff Ψ = 1)
    (hd : ∀ w, MvPowerSeries.pderiv K w Ψ = Ψ * MvPowerSeries.C (y w)) : Ψ = mvExp (linF y) := by
  have step : ∀ (w : τ) (m : τ →₀ ℕ), MvPowerSeries.coeff (m + Finsupp.single w 1) Ψ * ((m w : K) + 1) =
      y w * MvPowerSeries.coeff m Ψ := by
    intro w m
    have h := congrArg (MvPowerSeries.coeff m) (hd w)
    rw [MvPowerSeries.coeff_pderiv, mul_comm Ψ, MvPowerSeries.coeff_C_mul] at h
    exact h
  have key : ∀ (n : ℕ) (m : τ →₀ ℕ), m.degree = n →
      MvPowerSeries.coeff m Ψ = MvPowerSeries.coeff m (mvExp (linF y)) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
      subst hm0
      rw [coeff_zero_mvExp, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    | succ n ih =>
      intro m hm
      obtain ⟨w, hw⟩ : ∃ w, m w ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        have : m = 0 := Finsupp.ext hcon
        rw [this] at hm
        simp at hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        ext x
        by_cases hx : x = w
        · subst hx
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
          omega
        · simp [Ne.symm hx]
      have hdeg : m'.degree = n := by
        rw [map_add, Finsupp.degree_single] at hm
        omega
      have hne : ((m' w : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' w)
      have e1 := step w m'
      have e2 := coeff_mvExp_linF_step y w m'
      rw [ih m' hdeg, ← e2] at e1
      exact mul_right_cancel₀ hne e1
  ext m
  exact key _ m rfl
end Formalism.L2.FormalSeriesBounds.ChG
