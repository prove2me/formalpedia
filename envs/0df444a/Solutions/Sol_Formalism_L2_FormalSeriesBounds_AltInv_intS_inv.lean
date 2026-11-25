-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intS_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:46.782146+00:00
-- url     : https://prove2.me/submissions/b726134f-818c-499a-9a10-01845fcaffc5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_finsum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_low_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_deg_one_single
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_det
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
open Classical
open MvPowerSeries
namespace Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
private theorem hasSubst_lemma [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    HasSubst a :=
  ⟨fun s => by rw [ha s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
end Formalism.L2.FormalSeriesBounds.AltInv
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution [Fintype σ] (Φ t : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (heq : ∀ x, subst t (Φ x) = X x) : ∀ y, IntS v (t y) := by
  obtain ⟨L, hLdef⟩ : ∃ L : Matrix σ σ C, L = Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x) :=
    ⟨_, rfl⟩
  rw [← hLdef] at hL
  have hts : HasSubst t := hasSubst_lemma ht0
  have hLent : ∀ k l, IntC v (L k l) := by
    intro k l
    rw [hLdef, Matrix.of_apply]
    exact hΦ k _
  have hdeg0 : ∀ d : σ →₀ ℕ, d.degree = 0 → d = 0 := by
    intro d hd
    have h0 : ∑ i ∈ d.support, d i = 0 := hd
    rw [Finset.sum_eq_zero_iff] at h0
    ext i
    by_contra hi
    exact hi (h0 i (Finsupp.mem_support_iff.2 hi))
  have hord : ∀ y, OrdV 1 (t y) := by
    intro y μ hμ
    rw [hdeg0 μ (by omega), coeff_zero_eq_constantCoeff_apply, ht0]
  have hdet0 : L.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hL
    simp at hL
  have hinv : IntC v (L.det)⁻¹ := by
    have h1 : v (L.det * (L.det)⁻¹) = 0 := by rw [mul_inv_cancel₀ hdet0, AddValuation.map_one]
    rw [AddValuation.map_mul, hL, zero_add] at h1
    exact le_of_eq h1.symm
  have hadj : ∀ a b, IntC v (L.adjugate a b) := by
    intro a b
    rw [Matrix.adjugate_apply]
    refine intC_det _ fun k l => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact intC_one
      · exact intC_zero
    · exact hLent k l
  have hNint : ∀ x, IntS v (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) := by
    intro x d
    rw [map_sub, map_sum]
    refine intC_sub (hΦ x d) (intC_sum _ fun y _ => ?_)
    rw [coeff_smul, coeff_X]
    split_ifs
    · rw [mul_one]
      exact hLent x y
    · rw [mul_zero]
      exact intC_zero
  have hNlow : ∀ x, OrdV 2 (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) := by
    intro x d hd
    by_cases h1 : d.degree = 1
    · obtain ⟨z, rfl⟩ := deg_one_single d h1
      rw [map_sub, map_sum]
      have hs : ∀ y, coeff (Finsupp.single z 1) (L x y • (X y : MvPowerSeries σ C)) =
          if y = z then L x y else 0 := by
        intro y
        rw [coeff_smul, coeff_X]
        by_cases hyz : y = z
        · subst hyz
          simp
        · rw [if_neg hyz, if_neg, mul_zero]
          intro h
          exact hyz ((Finsupp.single_left_inj one_ne_zero).1 h).symm
      rw [Finset.sum_congr rfl fun y _ => hs y, Finset.sum_ite_eq' Finset.univ z, if_pos (Finset.mem_univ z),
        hLdef, Matrix.of_apply, sub_self]
    · have hd0 := hdeg0 d (by omega)
      subst hd0
      rw [map_sub, map_sum]
      simp only [coeff_smul, coeff_zero_X, mul_zero, Finset.sum_const_zero, sub_zero]
      rw [coeff_zero_eq_constantCoeff_apply, hΦ0]
  have hsplit : ∀ x, (X x : MvPowerSeries σ C) =
      (∑ y, L x y • t y) + subst t (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) := by
    intro x
    have e1 : subst t (Φ x) = subst t (∑ y, L x y • (X y : MvPowerSeries σ C)) +
        subst t (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) := by
      conv_lhs => rw [show Φ x = (∑ y, L x y • (X y : MvPowerSeries σ C)) +
        (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C)) by ring]
      rw [← coe_substAlgHom hts, map_add]
    have e2 : subst t (∑ y, L x y • (X y : MvPowerSeries σ C)) = ∑ y, L x y • t y := by
      rw [← coe_substAlgHom hts, map_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [map_smul, coe_substAlgHom, subst_X hts]
    rw [← heq x, e1, e2]
  have hlow : ∀ K, ∀ y, LowLt (v := v) K (t y) := by
    intro K
    induction K with
    | zero =>
      intro y μ hμ
      exact absurd hμ (Nat.not_lt_zero _)
    | succ K ih =>
      intro y μ hμ
      by_cases hlt : μ.degree < K
      · exact ih y μ hlt
      have hμK : μ.degree = K := by omega
      by_cases hK0 : K = 0
      · rw [hord y μ (by omega)]
        exact intC_zero
      have ih' : ∀ s, LowLt (v := v) (K - 1 + 1) (t s) := by
        intro s
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hK0)]
        exact ih s
      have hLw : ∀ x, IntC v ((Matrix.mulVec L fun y => coeff μ (t y)) x) := by
        intro x
        have hc := congrArg (coeff μ) (hsplit x)
        rw [map_add, map_sum] at hc
        simp only [coeff_smul] at hc
        have hmv : (Matrix.mulVec L fun y => coeff μ (t y)) x = ∑ y, L x y * coeff μ (t y) := rfl
        have hval : (Matrix.mulVec L fun y => coeff μ (t y)) x = coeff μ (X x : MvPowerSeries σ C) -
            coeff μ (subst t (Φ x - ∑ y, L x y • (X y : MvPowerSeries σ C))) := by
          rw [hmv, hc]
          ring
        rw [hval]
        refine intC_sub ?_ ?_
        · rw [coeff_X]
          split_ifs
          · exact intC_one
          · exact intC_zero
        · rw [coeff_subst hts]
          refine intC_finsum fun d => ?_
          rw [smul_eq_mul]
          by_cases hd : d.degree < 2
          · rw [hNlow x d hd, zero_mul]
            exact intC_zero
          · have hdd : d.degree = ∑ s ∈ d.support, d s := rfl
            have hP := (low_prod hord ih' d.support d).2 μ (by omega)
            exact intC_mul (hNint x d) hP
      have hdw : (Matrix.mulVec L.adjugate (Matrix.mulVec L fun y => coeff μ (t y))) y = L.det * coeff μ (t y) := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
        first
        | (rw [Matrix.smul_mulVec, Matrix.one_mulVec]; rfl)
        | simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
        | simp [Matrix.mulVec, Matrix.dotProduct, Matrix.one_apply]
      have hw : coeff μ (t y) = (L.det)⁻¹ * (Matrix.mulVec L.adjugate (Matrix.mulVec L fun y => coeff μ (t y))) y := by
        rw [hdw, inv_mul_cancel_left₀ hdet0]
      rw [hw]
      exact intC_mul hinv (intC_sum _ fun z _ => intC_mul (hadj _ _) (hLw z))
  intro y μ
  exact hlow (μ.degree + 1) y μ (Nat.lt_succ_self _)
end Formalism.L2.FormalSeriesBounds.AltInv
