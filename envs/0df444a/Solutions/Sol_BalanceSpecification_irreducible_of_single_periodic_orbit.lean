-- Prove2me | solution 1 for BalanceSpecification.irreducible_of_single_periodic_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:28.368694+00:00
-- url     : https://prove2.me/submissions/8adaafd8-f5f0-412b-9088-dd76c98199cd

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
      SymbolicDynamics.FullShift.shift (n : ℤ) x = y}) : Irreducible X := by
  have hpmap : Function.IsPeriodicPt (shiftMap X) p (⟨x, hx⟩ : X.carrier) := by
    apply Subtype.ext
    simpa only [shiftMap_iterate_val] using hperiod
  intro u hu v hv
  obtain ⟨zu, hzu, hu0⟩ := mem_language_iff_exists_block_zero.mp hu
  obtain ⟨zv, hzv, hv0⟩ := mem_language_iff_exists_block_zero.mp hv
  obtain ⟨a, ha⟩ := (show ∃ n : ℕ,
    SymbolicDynamics.FullShift.shift (n : ℤ) x = zu from by simpa only [horbit, Set.mem_ofPred_eq] using hzu)
  obtain ⟨b, hb⟩ := (show ∃ n : ℕ,
    SymbolicDynamics.FullShift.shift (n : ℤ) x = zv from by simpa only [horbit, Set.mem_ofPred_eq] using hzv)
  have hua : block x (a : ℤ) u.length = u := by
    simpa only [← ha, block_shift, add_zero] using hu0
  have hvb : block x (b : ℤ) v.length = v := by
    simpa only [← hb, block_shift, add_zero] using hv0
  let k := a + u.length + 1
  have hmultiple : SymbolicDynamics.FullShift.shift ((p * k : ℕ) : ℤ) x = x := by
    have he := congrArg Subtype.val (hpmap.mul_const k).eq
    simpa only [shiftMap_iterate_val] using he
  have hvfar : block x ((b + p * k : ℕ) : ℤ) v.length = v := by
    have hstart : ((b + p * k : ℕ) : ℤ) = ((p * k : ℕ) : ℤ) + (b : ℤ) := by
      simp only [Nat.cast_add]
      omega
    rw [hstart, ← block_shift, hmultiple]
    exact hvb
  have hgap : a + u.length ≤ b + p * k := by
    have hmul : k ≤ p * k := by
      simpa only [one_mul] using Nat.mul_le_mul_right k (Nat.one_le_of_lt hp)
    dsimp only [k] at hmul ⊢
    omega
  let d := b + p * k - (a + u.length)
  let w := block x ((a + u.length : ℕ) : ℤ) d
  refine ⟨w, block_mem_language hx _ _, ?_⟩
  have hfull : block x (a : ℤ) (u.length + d + v.length) = u ++ w ++ v := by
    rw [block_append, block_append, hua]
    have hstart : (a : ℤ) + (u.length + d : ℕ) = ((b + p * k : ℕ) : ℤ) := by
      dsimp only [d]
      omega
    rw [hstart, hvfar]
    rfl
  refine ⟨x, hx, (a : ℤ), ?_⟩
  simpa only [List.length_append, w, length_block] using hfull
end BalanceSpecification
