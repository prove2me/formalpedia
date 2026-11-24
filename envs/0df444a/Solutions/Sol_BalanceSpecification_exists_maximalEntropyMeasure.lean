-- Prove2me | solution 1 for BalanceSpecification.exists_maximalEntropyMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:21:54.848837+00:00
-- url     : https://prove2.me/submissions/b30a60e8-17a1-4fa4-9be9-f2569d80bba1

module
public import Definitions.Def_BalanceSpecificaton_EntropyContinuity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Definitions.Def_BalanceSpecificaton_BlockingEstimate
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_VariationalPrinciple
public import Theorems.Thm_BalanceSpecification_blockEntropy_longWordOrbitAverage_lower
public import Theorems.Thm_BalanceSpecification_continuous_blockEntropy
public import Theorems.Thm_BalanceSpecification_continuous_shiftMap
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_exists_measurePreserving_mapClusterPt_finiteOrbitProbability
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measureEntropy_le_entropy
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_extensionPairs
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_language_iff_exists_block_zero
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_tendsto_entropy
public import Theorems.Thm_BalanceSpecification_tendsto_measureEntropy
public import Theorems.Thm_BalanceSpecification_wordCount_pos_of_nonempty
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_extensionPairs
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



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
theorem _root_.solution (hX : X.carrier.Nonempty) :
    ∃ μ : ProbabilityMeasure X.carrier, IsMaximalEntropyMeasure hX μ := by
  classical
  let W (N : ℕ) := ↥(wordFinset (language X) (N + 1))
  have hW (N : ℕ) : (wordFinset (language X) (N + 1)).Nonempty :=
    Finset.card_pos.mp (wordCount_pos_of_nonempty hX _)
  let : ∀ N, Fintype (W N) := fun _ => inferInstance
  let : ∀ N, Nonempty (W N) := fun N => ⟨⟨(hW N).choose, (hW N).choose_spec⟩⟩
  have hrep : ∀ N (w : W N), ∃ x : X.carrier, block x.val 0 (N + 1) = w.val := by
    intro N w
    obtain ⟨x, hx, hblock⟩ := mem_language_iff_exists_block_zero.mp
      (mem_wordFinset.mp w.property).1
    refine ⟨⟨x, hx⟩, ?_⟩
    simpa only [(mem_wordFinset.mp w.property).2] using hblock
  choose x hx using hrep
  let : CompactSpace X.carrier := isCompact_iff_compactSpace.mp X.isClosed.isCompact
  obtain ⟨μ, hμ, hInv⟩ := exists_measurePreserving_mapClusterPt_finiteOrbitProbability
    (continuous_shiftMap X) x
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp hμ
  have hblock (n : ℕ) (hn : 0 < n) : (n : ℝ) * entropy X hX ≤ blockEntropy μ n := by
    have hleft : Tendsto (fun N : ℕ =>
        (n : ℝ) * (Real.log (wordCount (language X) (N + 1)) / ((N + 1 : ℕ) : ℝ)) -
          (3 * (n : ℝ)^2 * Real.log (Fintype.card A)) / ((N + 1 : ℕ) : ℝ))
        atTop (𝓝 ((n : ℝ) * entropy X hX)) := by
      have ht := ((tendsto_entropy hX).comp (tendsto_add_atTop_nat 1)).const_mul (n : ℝ)
      have hc := (tendsto_const_div_atTop_nhds_zero_nat
        (3 * (n : ℝ)^2 * Real.log (Fintype.card A))).comp (tendsto_add_atTop_nat 1)
      simpa only [sub_zero, Function.comp_def] using ht.sub hc
    have hright := (continuous_blockEntropy X n).tendsto μ |>.comp hlim
    apply le_of_tendsto_of_tendsto (hleft.mono_left hU) hright
    have hevent : ∀ᶠ N : ℕ in atTop, n ≤ N + 1 :=
      (eventually_ge_atTop n).mono fun N hN => by omega
    exact (hevent.mono fun N hN =>
      blockEntropy_longWordOrbitAverage_lower hX N n hn hN (x N) (hx N)).filter_mono hU
  refine ⟨μ, hInv, le_antisymm (measureEntropy_le_entropy hX hInv) ?_⟩
  apply ge_of_tendsto (tendsto_measureEntropy hInv)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.zero_lt_one.trans_le hn)
  exact (le_div_iff₀ hnp).mpr (by simpa only [mul_comm] using hblock n (Nat.zero_lt_one.trans_le hn))
end BalanceSpecification
