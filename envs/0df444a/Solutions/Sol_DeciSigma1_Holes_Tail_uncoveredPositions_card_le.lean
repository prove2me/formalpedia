-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.uncoveredPositions_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:56.006572+00:00
-- url     : https://prove2.me/submissions/11e8dbaa-875f-4240-a4b2-b3496cc99095

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (fs : List PeriodicFactor) {J T n len : ℕ} (hT : 0 < T)
    (hlen : len ≤ J + n * T + T)
    (hcov : ∀ m < n, ∃ y, J + m * T ≤ y ∧ y < J + m * T + T ∧ y < len ∧ Covers fs y) :
    (uncoveredPositions fs J len).card ≤ (fs.length + 1) * (2 * T) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := uncoveredPositions fs J len)
    (p := fun x => (x - J) / T + 1 < n)
  have hearly : (uncoveredPositions fs J len).filter (fun x => (x - J) / T + 1 < n) ⊆
      (fs.toFinset ×ˢ Finset.Icc 1 (2 * T)).image (fun q => q.1.start - q.2) := by
    intro x hx
    simp only [uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hx
    obtain ⟨⟨⟨hJx, hxl⟩, hunc⟩, hm⟩ := hx
    have hm1 : (x - J) / T * T ≤ x - J := Nat.div_mul_le_self _ _
    have hm2 : x - J < (x - J) / T * T + T := Nat.lt_div_mul_add hT
    obtain ⟨y, hy1, hy2, -, hyc⟩ := hcov ((x - J) / T + 1) hm
    rw [add_one_mul] at hy1 hy2
    have hex : ∃ z, x < z ∧ Covers fs z := ⟨y, by omega, hyc⟩
    have hz := Nat.find_spec hex
    have hzle : Nat.find hex ≤ y := Nat.find_min' hex ⟨by omega, hyc⟩
    obtain ⟨f, hf, hfs, hfe⟩ := hz.2
    have hfs0 : f.start = Nat.find hex := by
      by_contra hne
      by_cases hxz : x < Nat.find hex - 1
      · exact Nat.find_min hex (m := Nat.find hex - 1) (by omega) ⟨hxz, f, hf, by omega, by omega⟩
      · exact hunc ⟨f, hf, by omega, by omega⟩
    rw [Finset.mem_image]
    refine ⟨(f, Nat.find hex - x), Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hf,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, by simp only; omega⟩
  have hlate : (uncoveredPositions fs J len).filter (fun x => ¬ ((x - J) / T + 1 < n)) ⊆
      Finset.Ico (J + (n - 1) * T) len := by
    intro x hx
    simp only [uncoveredPositions, Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    obtain ⟨⟨⟨hJx, hxl⟩, -⟩, hm⟩ := hx
    have h2 : (x - J) / T * T ≤ x - J := Nat.div_mul_le_self _ _
    generalize (x - J) / T = q at hm h2
    have h1 : (n - 1) * T ≤ q * T := Nat.mul_le_mul_right _ (by omega)
    exact ⟨by omega, hxl⟩
  have hn := Nat.sub_one_mul n T
  have c1 := Finset.card_le_card hearly
  have c2 := Finset.card_le_card hlate
  have c3 : ((fs.toFinset ×ˢ Finset.Icc 1 (2 * T)).image (fun q => q.1.start - q.2)).card ≤
      fs.length * (2 * T) := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Nat.card_Icc]
    exact Nat.mul_le_mul (List.toFinset_card_le fs) (by omega)
  rw [Nat.card_Ico] at c2
  have : (fs.length + 1) * (2 * T) = fs.length * (2 * T) + 2 * T := by ring
  omega
end DeciSigma1.Holes.Tail
