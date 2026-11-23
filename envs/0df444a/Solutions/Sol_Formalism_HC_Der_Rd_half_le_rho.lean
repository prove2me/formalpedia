-- Prove2me | solution 1 for Formalism.HC.Der.Rd.half_le_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:14.734795+00:00
-- url     : https://prove2.me/submissions/72bcf3a3-26b6-4a08-b027-2c3ede93696b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Theorems.Thm_Formalism_HC_Der_Rd_card_KK
import Theorems.Thm_Formalism_HC_Der_Rd_mul_mem_KK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
private theorem totient_ne_zero_of_ne_zero {n : ℕ} (hn : n ≠ 0) : n.totient ≠ 0 := by
  first
  | exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  | exact (Nat.totient_pos (Nat.pos_of_ne_zero hn)).ne'
  | simpa using hn
variable {N : ℕ} [NeZero N]
private theorem ne_zero_of_dvd_of_neZero {f : ℕ} (hf : f ∣ N) : f ≠ 0 := by
  rintro rfl
  exact NeZero.ne N (zero_dvd_iff.mp hf)
private theorem card_KK_ne_zero_of_dvd {f : ℕ} (hf : f ∣ N) : (KK N f).card ≠ 0 := by
  intro h
  have h' := card_KK hf
  rw [h, zero_mul] at h'
  exact totient_ne_zero_of_ne_zero (NeZero.ne N) h'.symm
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Der.Rd
theorem _root_.solution (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) (h : ∃ u ∈ KK N f, u ∉ U) : 1 / 2 ≤ rho U f := by
  open Classical in
  have card_outside_add_card_inside_lemma_12 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) (f : ℕ) :
      ((KK N f).filter fun u => u ∉ U).card +
        ((KK N f).filter fun u => u ∈ U).card = (KK N f).card := by
    rw [add_comm]
    first
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | convert Finset.filter_card_add_filter_neg_card_eq_card (s := KK N f) (fun u => u ∈ U)
    | convert Finset.card_filter_add_card_filter_not (s := KK N f) (fun u => u ∈ U)
  open Classical in
  have kernelOutsideFraction_eq_div_lemma_13 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
      rho U f =
        (((KK N f).filter fun u => u ∉ U).card : ℝ) / (KK N f).card := by
    have hc : ((KK N f).card : ℝ) * f.totient = N.totient := by
      exact_mod_cast card_KK hf
    have ht : (f.totient : ℝ) ≠ 0 := by
      exact_mod_cast totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)
    unfold rho
    rw [← hc, mul_div_mul_right _ _ ht]
  open Classical in
  have card_inside_le_outside_lemma_15 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) {u0 : (ZMod N)ˣ}
      (hu0 : u0 ∈ KK N f) (hu0' : u0 ∉ U) :
      ((KK N f).filter fun u => u ∈ U).card ≤
        ((KK N f).filter fun u => u ∉ U).card := by
    apply Finset.card_le_card_of_injOn (fun v => u0 * v)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq] at hv ⊢
      refine ⟨mul_mem_KK hf hu0 hv.1, fun h => hu0' ?_⟩
      have h' := mul_mem h (inv_mem hv.2)
      rwa [mul_inv_cancel_right] at h'
    · intro a _ b _ hab
      exact mul_left_cancel hab
  obtain ⟨u0, hu0, hu0'⟩ := h
  have h1 := (Nat.cast_le (α := ℝ)).mpr (card_inside_le_outside_lemma_15 U hf hu0 hu0')
  have h2 := congrArg (Nat.cast : ℕ → ℝ) (card_outside_add_card_inside_lemma_12 U f)
  push_cast at h2
  have hK : (0 : ℝ) < (KK N f).card :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (card_KK_ne_zero_of_dvd hf))
  rw [kernelOutsideFraction_eq_div_lemma_13 U hf]
  first
  | exact (le_div_iff₀ hK).mpr (by linarith)
  | exact (le_div_iff hK).mpr (by linarith)
end Formalism.HC.Der.Rd
