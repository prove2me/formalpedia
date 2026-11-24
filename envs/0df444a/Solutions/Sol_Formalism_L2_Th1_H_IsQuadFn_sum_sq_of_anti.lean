-- Prove2me | solution 1 for Formalism.L2.Th1.H.IsQuadFn.sum_sq_of_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:15.810413+00:00
-- url     : https://prove2.me/submissions/9b5899d8-1ebf-4650-bf9a-341f25c14987

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_right
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_phi_zero
import Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_zero_left

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.IsQuadFn
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}
namespace Formalism.L2.Th1.H.IsQuadFn
theorem _root_.solution {P : Type*} [AddCommGroup P] [Fintype P] {Φ : P → ℂ} {B : P → P → ℂ}
    (h : IsQuadFn Φ B) (T : P →+ P) (hT : ∀ v, Φ v * Φ (T v) = 1) :
    (∑ v, Φ v) ^ 2 = (Fintype.card P : ℂ) := by
  classical
  have hB : ∀ v w, B (T v) (T w) * B v w = 1 := by
    intro v w
    have h1 := hT (v + w)
    rw [map_add, h.add, h.add] at h1
    have h2 := hT v
    have h3 := hT w
    have h4 : (Φ v * Φ (T v)) * (Φ w * Φ (T w)) * (B (T v) (T w) * B v w) = 1 := by
      linear_combination h1
    rwa [h2, h3, one_mul, one_mul] at h4
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).mpr (fun v hv => h.nondeg v (fun w => ?_))
    have h5 := hB v w
    rwa [hv, h.b_zero_left, one_mul] at h5
  have hsurj : Function.Surjective T := Finite.injective_iff_surjective.mp hinj
  have hchar : ∀ w, w ≠ 0 → ∑ v, B w (T v) = 0 := by
    intro w hw
    obtain ⟨u, hu⟩ : ∃ u, B w (T u) ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hw (h.nondeg w (fun y => by obtain ⟨u, rfl⟩ := hsurj y; exact hcon u))
    have hs : B w (T u) * ∑ v, B w (T v) = ∑ v, B w (T v) := by
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv (Equiv.addLeft u) _ _ (fun v => by simp [h.right])
    have h6 : (B w (T u) - 1) * ∑ v, B w (T v) = 0 := by
      rw [sub_mul, hs, one_mul, sub_self]
    exact (mul_eq_zero.mp h6).resolve_left (sub_ne_zero.mpr hu)
  have hrow : ∀ v, Φ v * ∑ w, Φ w = ∑ w, Φ w * B w (T v) := by
    intro v
    have e : ∑ w, Φ (w + T v) = ∑ w, Φ w :=
      Fintype.sum_equiv (Equiv.addRight (T v)) _ _ (fun w => by simp)
    rw [← e, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [h.add]
    linear_combination (Φ w * B w (T v)) * hT v
  have hcol : ∀ w, ∑ v, B w (T v) = if w = 0 then (Fintype.card P : ℂ) else 0 := by
    intro w
    split_ifs with hw
    · subst hw
      simp [h.b_zero_left]
    · exact hchar w hw
  calc (∑ v, Φ v) ^ 2 = ∑ v, Φ v * ∑ w, Φ w := by rw [pow_two, Finset.sum_mul]
    _ = ∑ v, ∑ w, Φ w * B w (T v) := Finset.sum_congr rfl (fun v _ => hrow v)
    _ = ∑ w, Φ w * ∑ v, B w (T v) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ w, Φ w * (if w = 0 then (Fintype.card P : ℂ) else 0) :=
        Finset.sum_congr rfl (fun w _ => by rw [hcol w])
    _ = (Fintype.card P : ℂ) := by
        simp [h.phi_zero]
end Formalism.L2.Th1.H.IsQuadFn
