-- Prove2me | solution 1 for Formalism.IncomingBounds.primeDvdChooseIff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:15.680374+00:00
-- url     : https://prove2.me/submissions/8f2cbcb3-45fb-4754-a22c-95cdb1da7fc2

import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
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
namespace Formalism.IncomingBounds
private lemma binomGcd_lucas_lemma (l : ℕ) [Fact l.Prime] (m v : ℕ) :
    (l ^ v * m).choose (l ^ v) ≡ m [MOD l] := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  induction v with
  | zero => simp <;> exact Nat.ModEq.refl _
  | succ v ih =>
    rw [show l ^ (v + 1) * m = l * (l ^ v * m) by ring, show l ^ (v + 1) = l * l ^ v by ring]
    refine Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
    simp only [Nat.mul_mod_right, Nat.mul_div_cancel_left _ hl, Nat.choose_self, one_mul]
    exact ih
private lemma binomGcd_lucas_lemma_2 (l : ℕ) [Fact l.Prime] (a : ℕ) :
    (l ^ (a + 1) - 1).choose (l ^ a - 1) ≡ 1 [MOD l] := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl0 : 0 < l := by omega
  have hlt : l - 1 < l := by omega
  induction a with
  | zero => simp <;> exact Nat.ModEq.refl _
  | succ a ih =>
    have e1 : 1 ≤ l ^ a := Nat.one_le_pow _ _ hl0
    have e2 : 1 ≤ l ^ (a + 1) := Nat.one_le_pow _ _ hl0
    have e3 : 1 ≤ l ^ (a + 1 + 1) := Nat.one_le_pow _ _ hl0
    have hn : l ^ (a + 1 + 1) - 1 = (l - 1) + l * (l ^ (a + 1) - 1) := by
      zify [e2, e3, (by omega : 1 ≤ l)]
      ring
    have hk : l ^ (a + 1) - 1 = (l - 1) + l * (l ^ a - 1) := by
      zify [e1, e2, (by omega : 1 ≤ l)]
      ring
    have hnk : (l ^ (a + 1 + 1) - 1).choose (l ^ (a + 1) - 1) =
        ((l - 1) + l * (l ^ (a + 1) - 1)).choose ((l - 1) + l * (l ^ a - 1)) := by
      rw [← hk, ← hn]
    rw [hnk]
    refine Choose.choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ hl0,
      Nat.div_eq_of_lt hlt, zero_add, Nat.choose_self, one_mul]
    exact ih
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : BinomGcd := by
  intro l hl n hn
  haveI := Fact.mk hl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨k, hk0, hkn, hndvd⟩ ⟨e, rfl⟩
    exact hndvd (hl.dvd_choose_pow (by omega) (by omega))
  · intro hnp
    have hd1 : l ^ padicValNat l n ∣ n := pow_padicValNat_dvd
    have hd2 : ¬ l ^ (padicValNat l n + 1) ∣ n := pow_succ_padicValNat_not_dvd (by omega)
    generalize padicValNat l n = v at hd1 hd2
    obtain ⟨m, rfl⟩ := hd1
    have hlm : ¬ l ∣ m := by
      rintro ⟨c, rfl⟩
      exact hd2 ⟨c, by ring⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hn
      omega
    have hm1 : m ≠ 1 := fun h => hnp ⟨v, by rw [h, mul_one]⟩
    have hp : 0 < l ^ v := pow_pos hl.pos v
    refine ⟨l ^ v, hp, lt_mul_of_one_lt_right hp (by omega), ?_⟩
    intro hd
    apply hlm
    exact Nat.modEq_zero_iff_dvd.1
      ((binomGcd_lucas_lemma l m v).symm.trans (Nat.modEq_zero_iff_dvd.2 hd))
  · intro e he hne
    subst hne
    obtain ⟨a, rfl⟩ : ∃ a, e = a + 1 := ⟨e - 1, by omega⟩
    refine ⟨l ^ a, pow_pos hl.pos a, Nat.pow_lt_pow_right hl.one_lt (by omega), ?_⟩
    have h1 : 1 ≤ l ^ a := Nat.one_le_pow _ _ hl.pos
    have h2 : 1 ≤ l ^ (a + 1) := Nat.one_le_pow _ _ hl.pos
    have key := Nat.add_one_mul_choose_eq (l ^ (a + 1) - 1) (l ^ a - 1)
    simp only [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2] at key
    have hc : (l ^ (a + 1)).choose (l ^ a) = l * (l ^ (a + 1) - 1).choose (l ^ a - 1) := by
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hl.pos a)
      rw [← key, pow_succ]
      ring
    intro hdvd
    rw [hc, pow_two, Nat.mul_dvd_mul_iff_left hl.pos] at hdvd
    have h3 : l ∣ 1 := Nat.modEq_zero_iff_dvd.1
      ((binomGcd_lucas_lemma_2 l a).symm.trans (Nat.modEq_zero_iff_dvd.2 hdvd))
    exact hl.one_lt.ne' (Nat.dvd_one.1 h3)
end Formalism.IncomingBounds
