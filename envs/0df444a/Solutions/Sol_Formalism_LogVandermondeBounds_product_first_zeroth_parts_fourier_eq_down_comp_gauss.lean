-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.fourier_eq_down_comp_gauss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:48.606962+00:00
-- url     : https://prove2.me/submissions/2b3a0bf0-ab3e-44ad-9e2b-a97351543403

import Definitions.Def_Formalism_LogVandermondeBounds_GaussOperatorProductFormula
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_FourierIsometryOnNormKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
section Helpers
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}
private lemma pair_smul_left (a : k) (f x : Fin r → k) : pair (a • f) x = a * pair f x := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
private lemma pair_zero_left (x : Fin r → k) : pair (0 : Fin r → k) x = 0 := by
  simp [pair]
private lemma smulEquiv_apply (c : kˣ) (f : Fin r → k) : smulEquiv c f = (c : k) • f := rfl
private lemma sum_units (F : k → ℂ) : ∑ c : kˣ, F (c : k) = ∑ t, F t - F 0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : k)), add_sub_cancel_right]
  refine Finset.sum_bij' (fun c _ => (c : k)) (fun t ht => if h : t = 0 then 1 else Units.mk0 t h)
    ?_ ?_ ?_ ?_ ?_
  · intro c _; simp [Units.ne_zero]
  · intro t _; simp
  · intro c _; simp [Units.ne_zero]
  · intro t ht
    have : t ≠ 0 := Finset.ne_of_mem_erase ht
    simp [this]
  · intro c _; rfl
private lemma sum_orbit_eq_zero (φ : (Fin r → k) → ℂ) (hφ : ∀ f, f ≠ 0 → nmP φ f = 0)
    (P : (Fin r → k) → Prop) [DecidablePred P] (hP : ∀ (c : kˣ) g, P ((c : k) • g) ↔ P g)
    (hP0 : ∀ g, P g → g ≠ 0) :
    ∑ g ∈ univ.filter P, φ g = 0 := by
  have hc : ((Fintype.card kˣ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have key : ∑ _c : kˣ, ∑ g ∈ univ.filter P, φ g = 0 := by
    have step : ∀ c : kˣ, ∑ g ∈ univ.filter P, φ g = ∑ g ∈ univ.filter P, φ ((c : k) • g) := by
      intro c
      rw [Finset.sum_filter, Finset.sum_filter]
      refine (Fintype.sum_equiv (smulEquiv c) _ _ (fun g => ?_)).symm
      simp only [smulEquiv_apply, hP]
    rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
    refine Finset.sum_eq_zero (fun g hg => ?_)
    have := hφ g (hP0 g (Finset.mem_filter.1 hg).2)
    simpa [nmP, diaP] using this
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at key
  exact (mul_eq_zero.1 key).resolve_left hc
end Helpers
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
end

set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution : FourierEqDownGauss := by
  intro k _ _ _ r ψ φ hφ x
  have hA : opD (opGs ψ φ) x =
      ∑ g, (if pair g x ≠ 0 then ψ (pair g x) * φ g else 0) := by
    simp only [opD, opGs]
    rw [Finset.sum_comm]
    have step : ∀ c : kˣ, ∑ f ∈ univ.filter (fun f => pair f x = 1), ψ (c : k) * φ ((c : k) • f) =
        ∑ g, (if pair g x = (c : k) then ψ (pair g x) * φ g else 0) := by
      intro c
      rw [Finset.sum_filter]
      refine Fintype.sum_equiv (smulEquiv c) _ _ (fun f => ?_)
      simp only [smulEquiv_apply, pair_smul_left]
      by_cases h : pair f x = 1
      · simp [h]
      · have h' : ¬ (c : k) * pair f x = c := fun h' =>
          h (mul_left_cancel₀ c.ne_zero (h'.trans (mul_one _).symm))
        simp [h, h']
    rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [sum_units (fun t => if pair g x = t then ψ (pair g x) * φ g else 0)]
    by_cases h : pair g x = 0
    · simp [h]
    · simp [h]
  have hB : opFF ψ φ x = ∑ g, (if pair g x ≠ 0 then ψ (pair g x) * φ g else 0)
      + ∑ g ∈ univ.filter (fun g => g ≠ 0 ∧ pair g x = 0), φ g := by
    simp only [opFF, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    by_cases h1 : g = 0
    · simp [h1, pair_zero_left]
    · by_cases h2 : pair g x = 0
      · simp [h1, h2]
      · simp [h1, h2]
  have hC : ∑ g ∈ univ.filter (fun g => g ≠ 0 ∧ pair g x = 0), φ g = 0 :=
    sum_orbit_eq_zero φ hφ (fun g => g ≠ 0 ∧ pair g x = 0)
      (fun c g => by simp [pair_smul_left, Units.ne_zero]) (fun g h => h.1)
  rw [hB, hC, add_zero, hA]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
