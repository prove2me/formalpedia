-- Prove2me | solution 1 for Formalism.HC.Der.Rd.rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:16.957841+00:00
-- url     : https://prove2.me/submissions/ca48537c-1811-45b8-bd96-95531d0370ca

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Theorems.Thm_Formalism_HC_Der_Rd_card_KK
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
open Classical
namespace Formalism.HC.Der.Rd
theorem _root_.solution (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
    rho U f = 1 - (((KK N f).filter fun u => u ∈ U).card : ℝ) * f.totient / N.totient := by
  have card_outside_add_card_inside_lemma_12 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) (f : ℕ) :
      ((KK N f).filter fun u => u ∉ U).card +
        ((KK N f).filter fun u => u ∈ U).card = (KK N f).card := by
    rw [add_comm]
    first
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | convert Finset.filter_card_add_filter_neg_card_eq_card (s := KK N f) (fun u => u ∈ U)
    | convert Finset.card_filter_add_card_filter_not (s := KK N f) (fun u => u ∈ U)
  have kernelOutsideFraction_eq_div_lemma_13 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N) :
      rho U f =
        (((KK N f).filter fun u => u ∉ U).card : ℝ) / (KK N f).card := by
    have hc : ((KK N f).card : ℝ) * f.totient = N.totient := by
      exact_mod_cast card_KK hf
    have ht : (f.totient : ℝ) ≠ 0 := by
      exact_mod_cast totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)
    unfold rho
    rw [← hc, mul_div_mul_right _ _ ht]
  have hc : ((KK N f).card : ℝ) * f.totient = N.totient := by
    exact_mod_cast card_KK hf
  have ht : (f.totient : ℝ) ≠ 0 := by
    exact_mod_cast totient_ne_zero_of_ne_zero (ne_zero_of_dvd_of_neZero hf)
  have hK : ((KK N f).card : ℝ) ≠ 0 := by exact_mod_cast card_KK_ne_zero_of_dvd hf
  have hs : (((KK N f).filter fun u => u ∉ U).card : ℝ) +
      (((KK N f).filter fun u => u ∈ U).card : ℝ) = (KK N f).card := by
    exact_mod_cast card_outside_add_card_inside_lemma_12 U f
  rw [kernelOutsideFraction_eq_div_lemma_13 U hf, ← hc, mul_div_mul_right _ _ ht, eq_sub_iff_add_eq, ← add_div, hs,
    div_self hK]
end Formalism.HC.Der.Rd
