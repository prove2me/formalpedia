-- Prove2me | solution 1 for BalanceSpecification.tendsto_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:54:09.908802+00:00
-- url     : https://prove2.me/submissions/8f58dbc6-7ab8-4f36-98d6-21a78b6c7ad9

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Theorems.Thm_BalanceSpecification_wordCount_one_le
public import Theorems.Thm_BalanceSpecification_wordCount_submultiplicative
public import Theorems.Thm_BalanceSpecification_Growth_tendsto_rate


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A} (hX : X.carrier.Nonempty) :
    Tendsto (fun n : ℕ => Real.log (wordCount (language X) n) / n)
      atTop (𝓝 (entropy X hX)) :=
  Growth.tendsto_rate (wordCount_one_le hX) (wordCount_submultiplicative X)
end BalanceSpecification
