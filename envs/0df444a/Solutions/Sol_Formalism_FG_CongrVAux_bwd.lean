-- Prove2me | solution 1 for Formalism.FG.CongrVAux.bwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:04:04.847254+00:00
-- url     : https://prove2.me/submissions/7163da4b-1475-4681-bba7-5f2e8129c7db

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Theorems.Thm_Formalism_FG_CongrVAux_coeff_subst_local
import Theorems.Thm_Formalism_FG_CongrVAux_coeff_subst_perturb
import Theorems.Thm_P2M_Formalism_FG_CongrVAux_norm_sub_le_max__2892e70044d6
import Theorems.Thm_Formalism_FG_CongrVAux_fwd
import Theorems.Thm_Formalism_FG_CongrVAux_degree_lt_of_le_of_ne
import Theorems.Thm_Formalism_FG_CongrVAux_coeff_ofFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution [CharZero K] {p q : ℕ} {hq : q ≠ 0} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ)
    {ι : Type v} [Fintype ι] [DecidableEq ι] {M : ι → ι → K} (hM : IntegralMat M)
    {f : ι → MvPowerSeries ι K} (hf : IsIdMod2 f) (hfe : IsFunEqTypeV p q hq σ M f)
    {α β : ι → MvPowerSeries τ K} (hα0 : ∀ i, constantCoeff (α i) = 0)
    (hβ0 : ∀ i, constantCoeff (β i) = 0) (hα : ∀ i, IntegralMv (α i)) (hβ : ∀ i, IntegralMv (β i))
    {r : ℕ} (hr : 1 ≤ r) (hd : ∀ j, DivByMv ((p : K) ^ r) (subst α (f j) - subst β (f j))) :
    ∀ i, DivByMv ((p : K) ^ r) (α i - β i) := by
  classical
  have key : ∀ N : ℕ, ∀ d : τ →₀ ℕ, d.degree = N → ∀ i,
      ‖coeff d (α i - β i)‖ ≤ ‖(p : K) ^ r‖ := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro d hdN
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have : d = 0 := (Finsupp.degree_eq_zero_iff d).1 hdN
      subst this
      intro i
      rw [coeff_zero_eq_constantCoeff_apply, map_sub, hα0, hβ0, sub_zero, norm_zero]
      exact norm_nonneg _
    have hd0 : d ≠ 0 := by rintro rfl; simp at hdN; omega
    set c : ι → K := fun i => coeff d (α i - β i) with hc
    have hc1 : ∀ i, ‖c i‖ ≤ 1 := fun i => by
      simp only [hc, map_sub]; exact (norm_sub_le_max' _ _).trans (max_le (hα i d) (hβ i d))
    set β₁ : ι → MvPowerSeries τ K := fun i => β i + monomial d (c i) with hβ₁
    have hcβ₁ : ∀ i e, coeff e (β₁ i) = coeff e (β i) + if e = d then c i else 0 := by
      intro i e
      simp only [hβ₁, map_add, coeff_monomial]
    have hβ₁0 : ∀ i, constantCoeff (β₁ i) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, hcβ₁, if_neg (Ne.symm hd0), add_zero,
        coeff_zero_eq_constantCoeff_apply, hβ0]
    have hβ₁i : ∀ i, IntegralMv (β₁ i) := fun i e => by
      rw [hcβ₁]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hβ i e) ?_)
      split_ifs
      · exact hc1 i
      · simp
    set α' : ι → MvPowerSeries τ K :=
      fun i => ofFun fun e => if e ≤ d then coeff e (α i) else coeff e (β₁ i) with hα'
    have hcα' : ∀ i e, coeff e (α' i) = if e ≤ d then coeff e (α i) else coeff e (β₁ i) :=
      fun i e => coeff_ofFun _ e
    have hα'0 : ∀ i, constantCoeff (α' i) = 0 := fun i => by
      rw [← coeff_zero_eq_constantCoeff_apply, hcα', if_pos zero_le,
        coeff_zero_eq_constantCoeff_apply, hα0]
    have hα'i : ∀ i, IntegralMv (α' i) := fun i e => by
      rw [hcα']
      split_ifs
      · exact hα i e
      · exact hβ₁i i e
    have hdiv : ∀ i, DivByMv ((p : K) ^ r) (α' i - β₁ i) := fun i e => by
      rw [map_sub, hcα']
      split_ifs with hle
      · rw [hcβ₁]
        by_cases hed : e = d
        · subst hed
          rw [if_pos rfl, hc]
          simp
        · rw [if_neg hed, add_zero, ← map_sub]
          exact ih e.degree (hdN ▸ degree_lt_of_le_of_ne hle hed) e rfl i
      · simp
    intro j
    have hf' := fwd hS hM hf.1 hfe hα'0 hβ₁0 hα'i hβ₁i hr hdiv j d
    rw [map_sub, coeff_subst_local hα'0 hα0 (fun i e he => by rw [hcα', if_pos he]) (f j)] at hf'
    have hpert := coeff_subst_perturb hd0 hβ0 c (f j)
    simp only [hf.2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at hpert
    rw [← hβ₁] at hpert
    rw [hpert] at hf'
    have hA := hd j d
    rw [map_sub] at hA
    have : coeff d (α j - β j) = (coeff d (subst α (f j)) - coeff d (subst β (f j))) -
        (coeff d (subst α (f j)) - (coeff d (subst β (f j)) + c j)) := by
      rw [hc]; ring
    rw [this]
    exact (norm_sub_le_max' _ _).trans (max_le hA hf')
  intro i d
  exact key _ d rfl i
end Formalism.FG.CongrVAux
