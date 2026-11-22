-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.card_anchors_inside_marker_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:31:00.608761+00:00
-- url     : https://prove2.me/submissions/5f6d7576-77f5-474a-bd5b-0e7a9b7d65e9

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_occ_le_length
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_marker_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_ne_nil
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_marker_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_suffixOccurrenceCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_le_of_subset_biUnion
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {T : Table α S k} {W : Fin k → List α}
    (hfr : ∀ i, T.Fresh W i) (t : ℕ) {l : Fin k} (hl : l ∈ active W (t + 1))
    (ctx : List α) {a : ℕ} (hocc : marker W (t + 1) l <+: ctx.drop a) :
    ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p < a + (marker W (t + 1) l).length)).card ≤
      k * (Fintype.card S - 1) + 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hlen : (marker W (0 + 1) l).length = 1 := length_marker_one hl
    rw [hlen, filter_false_of_mem (fun p _ => by omega), card_empty]
    exact Nat.zero_le _
  obtain ⟨m, hm, hpre, hlt, hset⟩ := contextAnchors_marker_succ ht hl
  set σ := marker W (t + 1) l with hσ
  have hsub : (contextAnchors W t ctx).filter (fun p => a < p ∧ p < a + σ.length) ⊆
      insert (a + (marker W t m).length)
        (univ.biUnion (fun j => (suffixOccurrenceCuts W j σ).image (fun b => a +
            ((W j).length - b)))) := by
    intro p hp
    rw [mem_filter] at hp
    obtain ⟨hpa, hap, hpσ⟩ := hp
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨hpc, h, hh, hsuf⟩ := (mem_contextAnchors_succ W).mp hpa
    have hσle := occ_le_length hocc (marker_ne_nil (by omega) hl)
    have htake : ctx.take p = ctx.take a ++ σ.take (p - a) := by
      have h1 : (ctx.drop a).take (p - a) = σ.take (p - a) := by
        rw [List.prefix_iff_eq_take.mp hocc, List.take_take, Nat.min_eq_left (by omega)]
      rw [← h1, ← List.take_add, Nat.add_sub_cancel' hap.le]
    have hlenp : (σ.take (p - a)).length = p - a := by simp; omega
    rw [htake] at hsuf
    rcases le_or_gt (marker W (t' + 1) h).length (p - a) with hle | hgt
    · -- the marker lies inside the occurrence
      have hin : marker W (t' + 1) h <:+ σ.take (p - a) :=
        List.suffix_of_suffix_length_le hsuf (List.suffix_append _ _) (by omega)
      have hmem : p - a ∈ contextAnchors W (t' + 1) σ :=
        (mem_contextAnchors_succ W).mpr ⟨by omega, h, hh, hin⟩
      rw [hset, mem_insert, mem_singleton] at hmem
      rcases hmem with h1 | h1
      · exact mem_insert.mpr (Or.inl (by omega))
      · omega
    · -- the marker sticks out of the left end of the occurrence
      have hout : σ.take (p - a) <:+ marker W (t' + 1) h :=
        List.suffix_of_suffix_length_le (List.suffix_append _ _) hsuf (by omega)
      have hw : σ.take (p - a) <:+ W h := hout.trans (marker_suffix W _ h)
      have hpw : p - a ≤ (W h).length := hlenp ▸ hw.length_le
      have hdrop : (W h).drop ((W h).length - (p - a)) = σ.take (p - a) := by
        rw [List.suffix_iff_eq_drop.mp hw, hlenp]
      refine mem_insert_of_mem ?_
      simp only [mem_biUnion, mem_univ, true_and, mem_image]
      refine ⟨h, (W h).length - (p - a), mem_suffixOccurrenceCuts.mpr ⟨by omega, ?_⟩, by omega⟩
      rw [hdrop]; exact List.take_prefix _ _
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (univ.biUnion (fun j => (suffixOccurrenceCuts W j σ).image (fun b => a +
        ((W j).length - b)))).card + 1 :=
        card_insert_le _ _
    _ ≤ k * (Fintype.card S - 1) + 1 := by
        have := card_le_of_subset_biUnion hfr σ (fun j b => a + ((W j).length - b))
          (subset_refl _)
        omega
end DeciSigma1.Holes.Fresh
