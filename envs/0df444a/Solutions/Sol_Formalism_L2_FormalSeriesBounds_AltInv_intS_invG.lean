-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intS_invG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:47.960808+00:00
-- url     : https://prove2.me/submissions/651b2b4c-95f7-4c7d-8e7c-3eee6a0cd3dd

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_deg_one_single
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_det
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_finsum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_low_prod


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] {v : AddValuation C (WithTop ℝ)}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution {σ : Type*} [Fintype σ] (Φ t G : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (hG : ∀ x, IntS v (G x)) (heq : ∀ x, subst t (Φ x) = G x) :
    ∀ y, IntS v (t y) := by
  set L : Matrix σ σ C := Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x) with hLdef
  have hdet0 : L.det ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hL; exact WithTop.top_ne_coe hL
  have hord : ∀ s, OrdV 1 (t s) := fun s μ hμ => by
    have : μ = 0 := (Finsupp.degree_eq_zero_iff μ).1 (by omega)
    subst this; simpa using ht0 s
  have hs : HasSubst t := hasSubst_of_constantCoeff_zero ht0
  suffices key : ∀ E : ℕ, ∀ y, LowLt (v := v) E (t y) by
    intro y μ; exact key (μ.degree + 1) y μ (Nat.lt_succ_self _)
  intro E
  induction E with
  | zero => intro y μ h; exact absurd h (Nat.not_lt_zero _)
  | succ E ih =>
    intro y μ hμ
    rcases Nat.lt_succ_iff_lt_or_eq.mp hμ with hlt | heqd
    · exact ih y μ hlt

    cases E with
    | zero =>
      have : μ = 0 := (Finsupp.degree_eq_zero_iff μ).1 heqd
      subst this; simp [ht0 y, intC_zero]
    | succ E' =>

      have hlow : ∀ s, LowLt (v := v) (E' + 1) (t s) := ih
      have hbig : ∀ d : σ →₀ ℕ, 2 ≤ d.degree → IntC v (coeff μ (d.prod fun s n => t s ^ n)) := by
        intro d hd
        have hp := low_prod (v := v) hord hlow d.support d
        have : (d.prod fun s n => t s ^ n) = ∏ s ∈ d.support, t s ^ d s := rfl
        rw [this]
        have hdeg : d.degree = ∑ s ∈ d.support, d s := rfl
        exact hp.2 μ (by omega)

      have heqx : ∀ x, ∑ y', L x y' * coeff μ (t y') = coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)) := by
        intro x
        have h1 := congrArg (coeff μ) (heq x)
        rw [coeff_subst hs] at h1
        have hfin := coeff_subst_finite hs (Φ x) μ
        set T : (σ →₀ ℕ) → C := fun d => coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n) with hT
        have hsplit : ∀ d, T d = (if d.degree = 1 then T d else 0) + (if d.degree = 1 then 0 else T d) := by
          intro d; split_ifs <;> simp
        have hfg : (Function.support fun d => if d.degree = 1 then T d else 0).Finite :=
          hfin.subset (fun d hd => by
            simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact hd; exact absurd rfl hd)
        have hfh : (Function.support fun d => if d.degree = 1 then 0 else T d).Finite :=
          hfin.subset (fun d hd => by
            simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact absurd rfl hd; exact hd)
        have h2 : ∑ᶠ d, T d = (∑ᶠ d, if d.degree = 1 then T d else 0) +
            ∑ᶠ d, (if d.degree = 1 then 0 else T d) := by
          rw [← finsum_add_distrib hfg hfh]; exact finsum_congr hsplit
        have h3 : (∑ᶠ d, if d.degree = 1 then T d else 0) = ∑ y', L x y' * coeff μ (t y') := by
          rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun y' => Finsupp.single y' 1)
            (fun d hd => by
              simp only [Function.mem_support] at hd
              split_ifs at hd with hd1
              · obtain ⟨y', rfl⟩ := deg_one_single d hd1
                simp
              · exact absurd rfl hd)]
          rw [Finset.sum_image (fun a _ b _ hab => (Finsupp.single_left_inj one_ne_zero).mp hab)]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [if_pos (by simp), hT]
          simp only [smul_eq_mul]
          rw [Finsupp.prod_single_index (by simp), pow_one]
          rfl
        rw [h2, h3] at h1
        exact eq_sub_of_add_eq h1

      have hc : ∀ x, IntC v (coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n))) := by
        intro x
        refine intC_sub ?_ (intC_finsum fun d => ?_)
        · exact hG x μ
        · split_ifs with hd1
          · exact intC_zero
          · by_cases hd0 : d = 0
            · subst hd0; rw [coeff_zero_eq_constantCoeff_apply, hΦ0, zero_smul]; exact intC_zero
            · have : 2 ≤ d.degree := by
                have : d.degree ≠ 0 := fun h0 => hd0 ((Finsupp.degree_eq_zero_iff d).1 h0)
                omega
              rw [smul_eq_mul]; exact intC_mul (hΦ x d) (hbig d this)

      set w : σ → C := fun y' => coeff μ (t y') with hw
      set c : σ → C := fun x => coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)) with hcdef
      have hLw : L.mulVec w = c := by
        funext x; simp only [Matrix.mulVec, dotProduct]; exact heqx x
      have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet0
      have hwsol : w = L⁻¹.mulVec c := by
        rw [← hLw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hunit, Matrix.one_mulVec]
      have hinv : ∀ i j, IntC v (L⁻¹ i j) := by
        intro i j
        rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
        refine intC_mul ?_ ?_
        · unfold IntC; rw [AddValuation.map_inv, hL]; simp
        · rw [Matrix.adjugate_apply]
          refine intC_det _ fun a b => ?_
          rw [Matrix.updateRow_apply]
          split_ifs
          · rw [Pi.single_apply]; split_ifs; exact intC_one; exact intC_zero
          · exact hΦ a _
      have : w y = (L⁻¹.mulVec c) y := by rw [← hwsol]
      show IntC v (w y)
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      exact intC_sum _ fun x _ => intC_mul (hinv y x) (hc x)
end Formalism.L2.FormalSeriesBounds.AltInv
