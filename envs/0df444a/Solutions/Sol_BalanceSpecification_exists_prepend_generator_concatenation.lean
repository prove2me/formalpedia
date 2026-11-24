-- Prove2me | solution 1 for BalanceSpecification.exists_prepend_generator_concatenation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:14.697535+00:00
-- url     : https://prove2.me/submissions/e01de0b2-2d21-4fc0-9d80-efbd667c889d

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_block_append
public import Theorems.Thm_BalanceSpecification_block_periodicConfiguration
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution {C : Set (Word A)} {v : Word A}
    (hvC : v ∈ C) (hv : 0 < v.length) {y : Configuration A} {p : ℤ → ℤ}
    (hp : StrictMono p) (hp0 : p 0 = 0)
    (hwords : ∀ i : ℤ, block y (p i) ((p (i + 1) - p i).toNat) ∈ C) :
    ∃ (z : Configuration A) (q : ℤ → ℤ), StrictMono q ∧ q 0 = 0 ∧
      (∀ i : ℤ, block z (q i) ((q (i + 1) - q i).toNat) ∈ C) ∧
      ∀ n : ℕ, block z 0 (v.length + n) = v ++ block y 0 n := by
  let z : Configuration A := fun k =>
    if k < (v.length : ℤ) then periodicConfiguration v hv k else y (k - v.length)
  let q : ℤ → ℤ := fun i =>
    if i ≤ 0 then i * v.length else (v.length : ℤ) + p (i - 1)
  have hvZ : (0 : ℤ) < v.length := Nat.cast_pos.mpr hv
  have hleft (i : ℤ) (hi : i ≤ 0) :
      q i = i * v.length ∧ q (i + 1) = (i + 1) * v.length := by
    refine ⟨if_pos hi, ?_⟩
    by_cases his : i + 1 ≤ 0
    · exact if_pos his
    · have hi0 : i = 0 := by omega
      subst i
      simp only [q, zero_add, sub_self, hp0, add_zero, one_mul, ite_self]
  have hright (i : ℤ) (hi : 1 ≤ i) :
      q i = (v.length : ℤ) + p (i - 1) ∧ q (i + 1) = (v.length : ℤ) + p i := by
    simp only [q, show ¬i ≤ 0 by omega, show ¬i + 1 ≤ 0 by omega, ite_false,
      add_sub_cancel_right, and_self]
  have hq : StrictMono q := by
    intro a b hab
    by_cases ha : a ≤ 0
    · by_cases hb : b ≤ 0
      · simp only [q, if_pos ha, if_pos hb]
        exact mul_lt_mul_of_pos_right hab hvZ
      · have hpB : 0 ≤ p (b - 1) := by
          simpa only [hp0] using hp.monotone (show (0 : ℤ) ≤ b - 1 by omega)
        have hA : a * (v.length : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha hvZ.le
        simp only [q, if_pos ha, if_neg hb]
        omega
    · have hb : ¬b ≤ 0 := by omega
      simp only [q, if_neg ha, if_neg hb]
      simpa only [add_comm] using add_lt_add_left (hp (sub_lt_sub_right hab 1)) (v.length : ℤ)
  have hq0 : q 0 = 0 := by simp only [q, le_refl, ite_true, zero_mul]
  have hperiodic (i : ℤ) (hi : i ≤ 0) :
      block z (i * v.length) v.length = v := by
    have heq : block z (i * v.length) v.length =
        block (periodicConfiguration v hv) (i * v.length) v.length := by
      apply List.ext_getElem
      · simp only [length_block]
      · intro j hj hj'
        have hjlen : j < v.length := by simpa only [length_block] using hj
        have hstart : i * (v.length : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hi hvZ.le
        simp only [block, List.getElem_ofFn, z,
          if_pos (show i * (v.length : ℤ) + j < v.length by omega)]
    exact heq.trans (block_periodicConfiguration v hv i)
  have htail (k : ℤ) (hk : (v.length : ℤ) ≤ k) (n : ℕ) :
      block z k n = block y (k - v.length) n := by
    apply List.ext_getElem
    · simp only [length_block]
    · intro j hj hj'
      have hjZ : (0 : ℤ) ≤ j := Nat.cast_nonneg j
      simp only [block, List.getElem_ofFn, z,
        if_neg (show ¬k + (j : ℤ) < v.length by omega)]
      congr 1
      omega
  refine ⟨z, q, hq, hq0, ?_, ?_⟩
  · intro i
    by_cases hi : i ≤ 0
    · obtain ⟨hi0, hi1⟩ := hleft i hi
      rw [hi0, hi1]
      have hdiff : (i + 1) * (v.length : ℤ) - i * v.length = v.length := by ring
      rw [hdiff, Int.toNat_natCast, hperiodic i hi]
      exact hvC
    · obtain ⟨hi0, hi1⟩ := hright i (by omega)
      rw [hi0, hi1]
      have hdiff : (v.length : ℤ) + p i - ((v.length : ℤ) + p (i - 1)) =
          p i - p (i - 1) := by ring
      have hpI : 0 ≤ p (i - 1) := by
        simpa only [hp0] using hp.monotone (show (0 : ℤ) ≤ i - 1 by omega)
      rw [hdiff, htail _ (by omega)]
      have hstart : (v.length : ℤ) + p (i - 1) - v.length = p (i - 1) := by ring
      rw [hstart]
      simpa only [sub_add_cancel] using hwords (i - 1)
  · intro n
    rw [block_append, show (0 : ℤ) + v.length = v.length by omega,
      htail _ le_rfl, sub_self]
    have hfirst : block z 0 v.length = v := by
      simpa only [zero_mul] using hperiodic 0 le_rfl
    rw [hfirst]
end BalanceSpecification
