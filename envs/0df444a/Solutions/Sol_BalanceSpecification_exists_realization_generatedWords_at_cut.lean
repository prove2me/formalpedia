-- Prove2me | solution 1 for BalanceSpecification.exists_realization_generatedWords_at_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:13.634347+00:00
-- url     : https://prove2.me/submissions/324a37ea-9efb-4b86-9dfc-c3d5ead12519

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Theorems.Thm_BalanceSpecification_exists_prepend_generator_concatenation
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
theorem _root_.solution {C : Set (Word A)}
    (hC : ∃ q ∈ C, 0 < q.length) {v : Word A} (hv : v ∈ generatedWords C) :
    ∃ (x : Configuration A) (p : ℤ → ℤ), StrictMono p ∧ p 0 = 0 ∧
      (∀ i : ℤ, block x (p i) ((p (i + 1) - p i).toNat) ∈ C) ∧
      block x 0 v.length = v := by
  obtain ⟨q, hqC, hq⟩ := hC
  obtain ⟨ws, hws, rfl⟩ := hv
  have hreal : ∀ ws : List (Word A), (∀ w ∈ ws, w ∈ C) →
      ∃ (x : Configuration A) (p : ℤ → ℤ), StrictMono p ∧ p 0 = 0 ∧
        (∀ i : ℤ, block x (p i) ((p (i + 1) - p i).toNat) ∈ C) ∧
        block x 0 ws.flatten.length = ws.flatten := by
    intro ws
    induction ws with
    | nil =>
      intro _
      refine ⟨periodicConfiguration q hq, fun i => i * q.length, ?_, ?_, ?_, rfl⟩
      · intro a b hab
        exact mul_lt_mul_of_pos_right hab (Nat.cast_pos.mpr hq)
      · exact zero_mul _
      · intro i
        have hdiff : (i + 1) * (q.length : ℤ) - i * q.length = q.length := by ring
        rw [hdiff, Int.toNat_natCast, block_periodicConfiguration]
        exact hqC
    | cons w ws ih =>
      intro hws
      obtain ⟨y, p, hp, hp0, hpwords, hy⟩ :=
        ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
      by_cases hwlen : w.length = 0
      · have hwnil := List.length_eq_zero_iff.mp hwlen
        subst w
        exact ⟨y, p, hp, hp0, hpwords, by
          simpa only [List.flatten_cons, List.nil_append] using hy⟩
      · have hwpos : 0 < w.length := Nat.pos_of_ne_zero hwlen
        obtain ⟨z, r, hr, hr0, hrwords, hprefix⟩ :=
          exists_prepend_generator_concatenation (hws w (List.mem_cons_self)) hwpos hp hp0 hpwords
        refine ⟨z, r, hr, hr0, hrwords, ?_⟩
        simp only [List.flatten_cons, List.length_append]
        rw [hprefix, hy]
  exact hreal ws hws
end BalanceSpecification
