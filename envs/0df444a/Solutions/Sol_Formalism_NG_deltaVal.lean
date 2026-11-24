-- Prove2me | solution 1 for Formalism.NG.deltaVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:38.718383+00:00
-- url     : https://prove2.me/submissions/b6af45fa-501e-4618-bde0-f31ec65d780b

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ProdEraseZero
import Theorems.Thm_Formalism_NG_powSubPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.NG
private lemma prod_erase_zero {M : Type*} [CommMonoid M] (t : ℕ) (f : Fin (t + 1) → M) :
    ∏ i ∈ univ.erase (0 : Fin (t + 1)), f i = ∏ i : Fin t, f i.succ := by
  rw [Fin.univ_succ, Finset.erase_cons, Finset.prod_map]
  rfl
end Formalism.NG
end

set_option autoImplicit false
open Finset
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatDeltaVal := by
  intro l hl hl2 u hu w t
  have hp : l.Prime := hl.out
  have h2 : (2 : ℤ) ≤ l := by exact_mod_cast hp.two_le
  have hnot : ¬ (l : ℤ) ^ 2 ∣ (1 + (l : ℤ)) - 1 := by
    rw [show (1 + (l : ℤ)) - 1 = (l : ℤ) by ring]
    intro h
    have := Int.le_of_dvd (by omega) h
    nlinarith
  have hF : ∀ i : ℕ, (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1))) ≠ 0 ∧
      padicValInt l (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1))) =
        1 + padicValNat l (i + 1) := by
    intro i
    have hrw : u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1)) =
        (-u) * ((1 + (l : ℤ)) ^ (w + (i + 1)) - (1 + (l : ℤ)) ^ w) := by ring
    have hps := powSubPow l hl2 (1 + (l : ℤ)) (by simp) hnot w (w + (i + 1)) (by omega)
    rw [Nat.add_sub_cancel_left] at hps
    have hne : (1 + (l : ℤ)) ^ (w + (i + 1)) - (1 + (l : ℤ)) ^ w ≠ 0 := by
      intro h; rw [h, padicValInt.zero] at hps; omega
    have hu0 : -u ≠ 0 := by
      intro h; exact hu (by rw [neg_eq_zero.mp h]; exact dvd_zero _)
    rw [hrw]
    refine ⟨mul_ne_zero hu0 hne, ?_⟩
    rw [padicValInt.mul hu0 hne, hps, padicValInt.eq_zero_of_not_dvd (by rwa [dvd_neg])]
    ring
  have hclaim : ∀ s : ℕ,
      (∏ i ∈ range s, (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1)))) ≠ 0 ∧
      padicValInt l (∏ i ∈ range s, (u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1)))) =
        s + padicValNat l s.factorial := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [prod_range_succ]
      refine ⟨mul_ne_zero ih.1 (hF s).1, ?_⟩
      rw [padicValInt.mul ih.1 (hF s).1, ih.2, (hF s).2, Nat.factorial_succ,
        padicValNat.mul (Nat.succ_ne_zero s) (Nat.factorial_ne_zero s)]
      ring
  unfold delta
  rw [prod_erase_zero]
  simp only [Fin.val_succ, Fin.val_zero, add_zero]
  rw [Fin.prod_univ_eq_prod_range
    (fun i => u * (1 + (l : ℤ)) ^ w - u * (1 + (l : ℤ)) ^ (w + (i + 1))) t]
  exact (hclaim t).2
end Formalism.NG
