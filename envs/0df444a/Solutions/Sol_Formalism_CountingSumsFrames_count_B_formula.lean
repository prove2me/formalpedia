-- Prove2me | solution 1 for Formalism.CountingSumsFrames.count_B_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:19.688365+00:00
-- url     : https://prove2.me/submissions/1ab7f15c-1faa-4b21-a2cc-9a7340697500

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : CountB := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ π hπ M Rl CC n E c hEc hCC hGR
  choose hle u v huv using hGR

  have htor : ∀ z : V, π • z = 0 → z = 0 := by
    intro z hz
    have hπK : algebraMap O K π ≠ 0 := by
      intro h0
      exact hπ.ne_zero ((IsFractionRing.injective O K) (by simpa using h0))
    rw [← algebraMap_smul K π z] at hz
    exact (smul_eq_zero.mp hz).resolve_left hπK
  have key : ∀ a : Fin M → Fin n → O, ∑ e, ((u e (a e) : CC e) : V) = 0 → ∀ e i, π ∣ a e i := by
    intro a ha e i
    have hsplit : ((u e (a e) : CC e) : V) = - ∑ e' ∈ univ.erase e, ((u e' (a e') : CC e') : V) := by
      rw [← Finset.add_sum_erase _ _ (mem_univ e)] at ha
      exact eq_neg_of_add_eq_zero_left ha
    let S : Submodule O V := (Rl e).map ((π ^ c) • LinearMap.id : V →ₗ[O] V)
    have hmem : ∀ e' ∈ univ.erase e, ((u e' (a e') : CC e') : V) ∈ S := by
      intro e' he'
      obtain ⟨y, hy, hxy⟩ := hCC e' e (Finset.ne_of_mem_erase he') _ (u e' (a e')).2
      exact ⟨y, hy, by simp [hxy]⟩
    have hS : ((u e (a e) : CC e) : V) ∈ S := by
      rw [hsplit]; exact S.neg_mem (S.sum_mem hmem)
    obtain ⟨y, hy, hxy⟩ := hS
    have h2 : Submodule.inclusion (hle e) (u e (a e)) = π ^ c • (⟨y, hy⟩ : Rl e) := by
      apply Subtype.ext
      simp only [Submodule.coe_inclusion, SetLike.val_smul]
      rw [← hxy]; simp
    have h3 := congrArg (fun f => f (a e)) (huv e)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h3
    rw [h2, map_smul] at h3
    have h4 := congrFun h3 i
    simp only [Pi.smul_apply, smul_eq_mul] at h4
    have h5 : a e i * π ^ E = (π ^ (c - E) * v e ⟨y, hy⟩ i) * π ^ E := by
      rw [mul_comm (a e i), ← h4, ← pow_sub_mul_pow π hEc.le]; ring
    have h6 := mul_right_cancel₀ (pow_ne_zero E hπ.ne_zero) h5
    rw [h6]
    exact dvd_mul_of_dvd_left (dvd_pow_self π (Nat.sub_ne_zero_of_lt hEc)) _
  have iter : ∀ k : ℕ, ∀ a : Fin M → Fin n → O, ∑ e, ((u e (a e) : CC e) : V) = 0 →
      ∀ e i, π ^ k ∣ a e i := by
    intro k
    induction k with
    | zero => intro a _ e i; simp
    | succ k ih =>
      intro a ha e i
      have hd := key a ha
      choose a' ha' using hd
      have hfun : ∀ e, a e = π • a' e := fun e => funext fun i => by simp [ha' e i]
      have hsum : ∑ e, ((u e (a' e) : CC e) : V) = 0 := by
        apply htor
        rw [Finset.smul_sum]
        rw [← ha]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hfun e, map_smul]; simp
      have := ih a' hsum e i
      rw [ha' e i, pow_succ, mul_comm (π ^ k)]
      exact mul_dvd_mul_left π this
  have zero : ∀ a : Fin M → Fin n → O, ∑ e, ((u e (a e) : CC e) : V) = 0 → ∀ e i, a e i = 0 := by
    intro a ha e i
    by_contra h
    obtain ⟨k, w, hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h hπ
    have hdiv := iter (k + 1) a ha e i
    rw [hk, pow_succ, mul_comm (w : O)] at hdiv
    have : π ∣ (w : O) := (mul_dvd_mul_iff_left (pow_ne_zero k hπ.ne_zero)).mp hdiv
    exact hπ.not_isUnit (isUnit_of_dvd_unit this w.isUnit)
  let w : Fin M × Fin n → V := fun p => ((u p.1 (Pi.single p.2 1) : CC p.1) : V)
  have hli : LinearIndependent O w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have hconv : ∑ p, g p • w p = ∑ e, ((u e (fun i => g (e, i)) : CC e) : V) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun e _ => ?_
      have : (fun i => g (e, i)) = ∑ i, g (e, i) • (Pi.single i 1 : Fin n → O) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      rw [this, map_sum]
      simp [w, map_smul]
    rw [hconv] at hg
    exact zero (fun e i => g (e, i)) hg p.1 p.2
  have hliK : LinearIndependent K w := (LinearIndependent.iff_fractionRing O K).mp hli
  have := hliK.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fin] using this
end Formalism.CountingSumsFrames
