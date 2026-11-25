-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_subst_linS_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:10.234688+00:00
-- url     : https://prove2.me/submissions/564391b4-1bc6-4cf5-96f1-60ff406fa47c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_linS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_prod_eq_zero_of_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_pow_eq_zero_of_base

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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ τ : Type} [Fintype σ] [Fintype τ] (M : τ → σ → C) (R : σ → Prop)
    (Q : τ → Prop) (hRQ : ∀ w, R w → ∀ c, ¬ Q c → M c w = 0) (H : MvPowerSeries σ C)
    (hH : ∀ μ : σ →₀ ℕ, (∀ w ∈ μ.support, ¬ R w) → coeff μ H = 0)
    (A : τ →₀ ℕ) (hA : ∀ b, Q b → A b = 0) : coeff A (subst (linS M) H) = 0 := by
  rw [coeff_subst (hasSubst_linS M)]
  refine finsum_eq_zero_of_forall_eq_zero fun μ => ?_
  by_cases hμ : ∀ w ∈ μ.support, ¬ R w
  · rw [hH μ hμ, zero_smul]
  · simp only [not_forall, not_not] at hμ
    obtain ⟨w, hw, hRw⟩ := hμ
    have hlin : ∀ B : τ →₀ ℕ, (∀ b, Q b → B b = 0) → coeff B (linS M w) = 0 := by
      intro B hB
      unfold linS
      rw [map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [map_smul]
      by_cases hc : Q c
      · rw [coeff_X, if_neg, smul_zero]
        intro h
        have := hB c hc
        rw [h, Finsupp.single_eq_same] at this
        exact one_ne_zero this
      · rw [hRQ w hRw c hc, zero_smul]
    have : coeff A (μ.prod fun s n => linS M s ^ n) = 0 :=
      coeff_prod_eq_zero_of_mem Q μ.support (fun s => linS M s ^ μ s) hw
        (fun B hB => coeff_pow_eq_zero_of_base Q hlin (Finsupp.mem_support_iff.1 hw) B hB) A hA
    rw [this, smul_zero]
end Formalism.L2.FormalSeriesBounds
