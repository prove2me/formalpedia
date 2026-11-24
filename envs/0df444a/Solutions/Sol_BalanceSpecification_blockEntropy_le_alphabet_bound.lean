-- Prove2me | solution 1 for BalanceSpecification.blockEntropy_le_alphabet_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:39.536987+00:00
-- url     : https://prove2.me/submissions/621ae83b-7c10-40a7-9199-901238a72a73

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_blockEntropy_le_log_wordCount
public import Theorems.Thm_BalanceSpecification_card_allWords
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter Set
open scoped Topology
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (hX : X.carrier.Nonempty)
    (μ : ProbabilityMeasure X.carrier) (n : ℕ) :
    blockEntropy μ n ≤ (n : ℝ) * Real.log (Fintype.card A) := by
  classical
  have hA : Nonempty A := ⟨hX.choose 0⟩
  let : Nonempty A := hA
  have hcount : wordCount (language X) n ≤ (Fintype.card A) ^ n := by
    calc
      wordCount (language X) n ≤ (allWords (A := A) n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = _ := card_allWords n
  calc
    blockEntropy μ n ≤ Real.log (wordCount (language X) n) := blockEntropy_le_log_wordCount μ n
    _ ≤ Real.log ((Fintype.card A : ℝ) ^ n) :=
      Real.log_le_log (by exact_mod_cast wordCount_pos_of_nonempty hX n) (by exact_mod_cast hcount)
    _ = (n : ℝ) * Real.log (Fintype.card A) := Real.log_pow _ _
end BalanceSpecification
