-- Prove2me | solution 1 for BalanceSpecification.hasVariableSpecification_of_single_periodic_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:39.205342+00:00
-- url     : https://prove2.me/submissions/0a6b456e-aaa8-4301-bed8-d59351eefb85

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_shiftMap_iterate_val
public import Theorems.Thm_BalanceSpecification_block_append
public import Theorems.Thm_BalanceSpecification_block_mem_language
public import Theorems.Thm_BalanceSpecification_block_shift
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_language_iff_exists_block_zero
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*}
variable [Fintype A] [TopologicalSpace A] {X : ShiftSpace A}
omit [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {x : Configuration A}
    (hx : x ∈ X.carrier) {p : ℕ} (hp : 0 < p)
    (hperiod : SymbolicDynamics.FullShift.shift (p : ℤ) x = x)
    (horbit : X.carrier = {y | ∃ n : ℕ,
      SymbolicDynamics.FullShift.shift (n : ℤ) x = y}) : HasVariableSpecification X := by
  have hpmap : Function.IsPeriodicPt (shiftMap X) p (⟨x, hx⟩ : X.carrier) := by
    apply Subtype.ext
    simpa only [shiftMap_iterate_val] using hperiod
  have hshiftres (t : ℕ) : SymbolicDynamics.FullShift.shift ((t % p : ℕ) : ℤ) x =
      SymbolicDynamics.FullShift.shift (t : ℤ) x := by
    have he := congrArg Subtype.val (hpmap.iterate_mod_apply t)
    simpa only [shiftMap_iterate_val] using he
  refine ⟨p, ?_⟩
  intro u hu v hv
  obtain ⟨zu, hzu, hu0⟩ := mem_language_iff_exists_block_zero.mp hu
  obtain ⟨zv, hzv, hv0⟩ := mem_language_iff_exists_block_zero.mp hv
  obtain ⟨a, ha⟩ := (show ∃ n : ℕ,
    SymbolicDynamics.FullShift.shift (n : ℤ) x = zu from
      by simpa only [horbit, Set.mem_ofPred_eq] using hzu)
  obtain ⟨b, hb⟩ := (show ∃ n : ℕ,
    SymbolicDynamics.FullShift.shift (n : ℤ) x = zv from
      by simpa only [horbit, Set.mem_ofPred_eq] using hzv)
  have hua : block x (a : ℤ) u.length = u := by
    simpa only [← ha, block_shift, add_zero] using hu0
  have hvb : block x (b : ℤ) v.length = v := by
    simpa only [← hb, block_shift, add_zero] using hv0
  let r := (a + u.length) % p
  let s := b % p
  let d := if r ≤ s then s - r else s + p - r
  have hrp : r < p := Nat.mod_lt _ hp
  have hsp : s < p := Nat.mod_lt _ hp
  have hdp : d < p := by
    dsimp only [d]
    split <;> omega
  have hres : (a + u.length + d) % p = b % p := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hdp]
    change (r + d) % p = s
    by_cases hrs : r ≤ s
    · have hd : r + d = s := by
        dsimp only [d]
        rw [if_pos hrs]
        omega
      rw [hd, Nat.mod_eq_of_lt hsp]
    · have hd : r + d = s + p := by
        dsimp only [d]
        rw [if_neg hrs]
        omega
      rw [hd, Nat.add_mod_right, Nat.mod_eq_of_lt hsp]
  have hfar : block x ((a + u.length + d : ℕ) : ℤ) v.length = v := by
    have heq : SymbolicDynamics.FullShift.shift ((a + u.length + d : ℕ) : ℤ) x =
        SymbolicDynamics.FullShift.shift (b : ℤ) x := by
      rw [← hshiftres (a + u.length + d), ← hshiftres b, hres]
    have he := congrArg (fun z => block z 0 v.length) heq
    simp only [block_shift, add_zero] at he
    exact he.trans hvb
  let w := block x ((a + u.length : ℕ) : ℤ) d
  refine ⟨w, block_mem_language hx _ _, ?_, ?_⟩
  · simpa only [w, length_block] using hdp.le
  · have hfull : block x (a : ℤ) (u.length + d + v.length) = u ++ w ++ v := by
      rw [block_append, block_append, hua]
      have hstart : (a : ℤ) + (u.length + d : ℕ) = ((a + u.length + d : ℕ) : ℤ) := by
        simp only [Nat.cast_add, add_assoc]
      rw [hstart, hfar]
      rfl
    refine ⟨x, hx, (a : ℤ), ?_⟩
    simpa only [List.length_append, w, length_block] using hfull
end BalanceSpecification
