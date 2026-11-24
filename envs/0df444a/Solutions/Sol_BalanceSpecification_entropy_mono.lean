-- Prove2me | solution 1 for BalanceSpecification.entropy_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:51.857913+00:00
-- url     : https://prove2.me/submissions/9eee2da4-ff9d-4163-87af-bd9da5f275bf

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Theorems.Thm_BalanceSpecification_wordCount_one_le
public import Theorems.Thm_BalanceSpecification_wordCount_submultiplicative
public import Theorems.Thm_BalanceSpecification_Growth_rate_mono
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution {X Y : ShiftSpace A} (hX : X.carrier.Nonempty)
    (hY : Y.carrier.Nonempty) (hXY : X.carrier ⊆ Y.carrier) :
    entropy X hX ≤ entropy Y hY := by
  apply Growth.rate_mono (wordCount_one_le hX) (wordCount_one_le hY)
    (wordCount_submultiplicative X) (wordCount_submultiplicative Y)
  intro n
  exact_mod_cast (show wordCount (language X) n ≤ wordCount (language Y) n from
    Finset.card_le_card (by
      intro w hw
      obtain ⟨⟨x, hx, k, hk⟩, hlen⟩ := mem_wordFinset.mp hw
      exact mem_wordFinset.mpr ⟨⟨x, hXY hx, k, hk⟩, hlen⟩))
end BalanceSpecification
