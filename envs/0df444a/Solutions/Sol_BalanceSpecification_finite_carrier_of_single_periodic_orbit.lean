-- Prove2me | solution 1 for BalanceSpecification.finite_carrier_of_single_periodic_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:18:27.874276+00:00
-- url     : https://prove2.me/submissions/2c04c9ba-c806-4e92-9fe7-54e602c7cd01

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Definitions.Def_BalanceSpecificaton_Specification
public import Mathlib.Data.Set.Card
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Theorems.Thm_BalanceSpecification_shiftMap_iterate_val
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
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
      SymbolicDynamics.FullShift.shift (n : ℤ) x = y}) : X.carrier.Finite := by
  have hpmap : Function.IsPeriodicPt (shiftMap X) p (⟨x, hx⟩ : X.carrier) := by
    apply Subtype.ext
    simpa only [shiftMap_iterate_val] using hperiod
  apply (Set.finite_range (fun i : Fin p => SymbolicDynamics.FullShift.shift (i.val : ℤ) x)).subset
  intro y hy
  obtain ⟨n, rfl⟩ := (show ∃ n : ℕ,
    SymbolicDynamics.FullShift.shift (n : ℤ) x = y from by simpa only [horbit, Set.mem_ofPred_eq] using hy)
  refine ⟨⟨n % p, Nat.mod_lt n hp⟩, ?_⟩
  have he := congrArg Subtype.val (hpmap.iterate_mod_apply n)
  simpa only [shiftMap_iterate_val] using he
end BalanceSpecification
