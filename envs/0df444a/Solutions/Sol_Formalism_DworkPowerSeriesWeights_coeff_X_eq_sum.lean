-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.coeff_X_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:11.071872+00:00
-- url     : https://prove2.me/submissions/3886cde9-d41e-49f0-8a5f-b02e22f9b9db

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_lt_sq_pow
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_coeff_genLog
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
universe u v w
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff low_P)
section Shift
variable {K : Type u} [Field K] {τ : Type v} [DecidableEq τ]
private theorem coeff_pow_eq_zero_of_degree_lt' {h : MvPowerSeries τ K} (h0 : constantCoeff h = 0) :
    ∀ (m : ℕ) (n : τ →₀ ℕ), n.degree < m → coeff n (h ^ m) = 0 := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    replace hab : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    by_cases ha : ab.1 = 0
    · rw [ha, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0, zero_mul]
    · have hdeg : ab.1.degree + ab.2.degree = n.degree := by rw [← hab, map_add]
      have hpos : 0 < ab.1.degree := by
        rcases Nat.eq_zero_or_pos ab.1.degree with h' | h'
        · exact absurd ((Finsupp.degree_eq_zero_iff _).1 h') ha
        · exact h'
      rw [ih ab.2 (by omega), mul_zero]
end Shift
end Formalism.DworkPowerSeriesWeights
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff low_P)
variable {K : Type u} [Field K] {τ : Type v} [DecidableEq τ]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution [Finite τ] {l : ℕ} (hl : 2 ≤ l) (p : τ → τ) {g : τ → MvPowerSeries τ K}
    (hg0 : ∀ x, constantCoeff (g x) = 0) (x : τ)
    (hx : subst g (genLog (K := K) l p x) = X x) (n : τ →₀ ℕ) :
    coeff n (X x : MvPowerSeries τ K) = ∑ e ∈ Finset.range (n.degree + 1),
      ((l : K) ^ e)⁻¹ * coeff n (g (p^[e] x) ^ ((l ^ 2) ^ e)) := by
  have hs : HasSubst g := by
    first
      | exact hasSubst_of_constantCoeff_zero hg0
      | exact HasSubst.of_constantCoeff_nilpotent (fun s => by rw [hg0 s]; exact IsNilpotent.zero)
  have hcoef := congrArg (coeff n) hx
  rw [coeff_subst hs] at hcoef
  rw [← hcoef]

  set D : ℕ → τ →₀ ℕ := fun e => Finsupp.single (p^[e] x) ((l ^ 2) ^ e) with hDdef
  have hDdeg : ∀ e, (D e).degree = (l ^ 2) ^ e := fun e => by simp [hDdef, Finsupp.degree_single]
  have hD_inj : ∀ e e', D e = D e' → e = e' := by
    intro e e' h
    have h' := congrArg Finsupp.degree h
    rw [hDdeg, hDdeg] at h'
    exact Nat.pow_right_injective (by nlinarith) h'
  have hcD : ∀ e, coeff (D e) (genLog (K := K) l p x) = ((l : K) ^ e)⁻¹ := by
    intro e
    rw [coeff_genLog hl p x (D e) (M := (l ^ 2) ^ e + 1) (by rw [hDdeg]; omega)]
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl]
    · intro e' _ hne
      rw [if_neg]
      intro h
      exact hne (hD_inj e e' h).symm
    · intro he
      exfalso
      apply he
      rw [Finset.mem_range]
      have := lt_sq_pow hl e
      omega
  rw [finsum_eq_sum_of_support_subset _ (s := (Finset.range (n.degree + 1)).image D) ?_]
  · rw [Finset.sum_image (fun e _ e' _ h => hD_inj e e' h)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hcD, smul_eq_mul, hDdef]
    simp only
    rw [Finsupp.prod_single_index (h := fun s e => g s ^ e) (pow_zero _)]
  · intro d hd
    rw [Function.mem_support, smul_eq_mul] at hd
    have h1 : coeff d (genLog (K := K) l p x) ≠ 0 := left_ne_zero_of_mul hd
    have h2 := right_ne_zero_of_mul hd
    have h1' : (∑ e ∈ Finset.range (d.degree + 1),
        if d = Finsupp.single (p^[e] x) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) ≠ 0 := h1
    obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1'
    have hde : d = D e := by
      by_contra hc
      exact he (if_neg hc)
    rw [hde, hDdef] at h2
    simp only at h2
    rw [Finsupp.prod_single_index (h := fun s e => g s ^ e) (pow_zero _)] at h2
    have hle : ¬ n.degree < (l ^ 2) ^ e := fun hlt => h2 (coeff_pow_eq_zero_of_degree_lt' (hg0 _) _ n hlt)
    have := lt_sq_pow hl e
    rw [Finset.coe_image]
    exact ⟨e, by simp only [Finset.coe_range, Set.mem_Iio]; omega, hde.symm⟩
end Formalism.DworkPowerSeriesWeights
