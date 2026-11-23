-- Prove2me | solution 1 for Formalism.HC.Der.Rd.rho_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:17.212586+00:00
-- url     : https://prove2.me/submissions/3f109bbf-b3ae-43ea-8ec3-db4d301dc8db

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
theorem _root_.solution (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N)
    (h : ∀ u ∈ KK N f, ∀ v ∈ KK N f, u ∉ U → v ∉ U → u * v ∈ U) : rho U f ≤ 1 / 2 := by
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
  have card_outside_le_inside_lemma_16 {N : ℕ} [NeZero N] (U : Subgroup (ZMod N)ˣ) {f : ℕ} (hf : f ∣ N)
      (h : ∀ u ∈ KK N f, ∀ v ∈ KK N f, u ∉ U → v ∉ U → u * v ∈ U) :
      ((KK N f).filter fun u => u ∉ U).card ≤
        ((KK N f).filter fun u => u ∈ U).card := by
    rcases Finset.eq_empty_or_nonempty ((KK N f).filter fun u => u ∉ U) with he | ⟨u0, hu0⟩
    · rw [he, Finset.card_empty]
      exact Nat.zero_le _
    · rw [Finset.mem_filter] at hu0
      apply Finset.card_le_card_of_injOn (fun v => u0 * v)
      · intro v hv
        simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq] at hv ⊢
        exact ⟨mul_mem_KK hf hu0.1 hv.1, h u0 hu0.1 v hv.1 hu0.2 hv.2⟩
      · intro a _ b _ hab
        exact mul_left_cancel hab
  have h1 := (Nat.cast_le (α := ℝ)).mpr (card_outside_le_inside_lemma_16 U hf h)
  have h2 := congrArg (Nat.cast : ℕ → ℝ) (card_outside_add_card_inside_lemma_12 U f)
  push_cast at h2
  have hK : (0 : ℝ) < (KK N f).card :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (card_KK_ne_zero_of_dvd hf))
  rw [kernelOutsideFraction_eq_div_lemma_13 U hf]
  first
  | exact (div_le_iff₀ hK).mpr (by linarith)
  | exact (div_le_iff hK).mpr (by linarith)
end Formalism.HC.Der.Rd
