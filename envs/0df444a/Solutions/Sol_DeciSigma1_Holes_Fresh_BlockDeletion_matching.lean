-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:36:33.556806+00:00
-- url     : https://prove2.me/submissions/488f2b67-4154-418d-bf69-de5abd926c2b

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_junction_sep
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_junction_window
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_transfer
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Words.deletePositions_empty
attribute [local simp] DeciSigma1.Words.deletePositions_nil
attribute [local simp] DeciSigma1.Words.greatestPreimage_empty
attribute [local simp] DeciSigma1.Words.retainedCount_empty
attribute [local simp] DeciSigma1.Words.retainedCount_greatestPreimage
attribute [local simp] DeciSigma1.Words.retainedCount_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {i j : Fin k} {a b L : ℕ} (hL : (m.apply j).length = b + L)
    (hpre : (m.apply j).drop b <+: (m.apply i).drop a)
    (hB : ∀ d,
        0 < d → d < L → IsJunction m.deletionLength (m.sites i)
            (a + d) → d + m.upperCutLength ≤ L) :
    ∀ d, 0 < d → d < L →
      (IsJunction m.deletionLength (m.sites i) (a + d) ↔ IsJunction m.deletionLength
          (m.sites j) (b + d)) := by
  obtain ⟨r, hr⟩ := hpre
  have hxa : ∀ d, 0 < d → d < L → a + L ≤ (m.apply i).length := by
    intro d h1 h2
    have := congrArg List.length hr
    simp only [List.length_append, List.length_drop] at this
    omega
  have htext : ∀ d, d + m.upperCutLength ≤ L →
      ((m.apply i).drop (a + d)).take m.upperCutLength =
          ((m.apply j).drop (b + d)).take m.upperCutLength := by
    intro d hd
    rw [← List.drop_drop, ← List.drop_drop, ← hr, List.drop_append_of_le_length (by simp; omega),
      List.take_append_of_le_length (by simp; omega)]
  suffices H : ∀ e d, L - d = e → 0 < d → d < L →
      (IsJunction m.deletionLength (m.sites i) (a + d) ↔ IsJunction m.deletionLength
          (m.sites j) (b + d)) from
    fun d h1 h2 => H _ d rfl h1 h2
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro d he hd0 hdL
  have IH : ∀ d', d < d' → d' < L →
      (IsJunction m.deletionLength (m.sites i) (a + d') ↔ IsJunction m.deletionLength
          (m.sites j) (b + d')) :=
    fun d' h1 h2 => ih (L - d') (by omega) d' rfl (by omega) h2
  constructor
  · intro hJ
    have hdn := hB d hd0 hdL hJ
    refine m.transfer hfr hJ (htext d hdn) ?_ (by omega)
    rintro J hJ' ⟨h1, h2⟩
    have h3 := (IH (J - b) (by omega) (by omega)).mpr (by rwa [Nat.add_sub_cancel' (by omega)])
    have := m.junction_sep hJ h3 (by omega)
    omega
  · intro hJ
    have hdn : d + m.upperCutLength ≤ L := by
      obtain ⟨c, hc, hce⟩ := hJ
      have := (m.junction_window hc).2.2.1
      omega
    refine m.transfer hfr hJ (htext d hdn).symm ?_ (by have := hxa d hd0 hdL; omega)
    rintro J hJ' ⟨h1, h2⟩
    have h3 := (IH (J - a) (by omega) (by omega)).mp (by rwa [Nat.add_sub_cancel' (by omega)])
    have := m.junction_sep hJ h3 (by omega)
    omega
end DeciSigma1.Holes.Fresh.BlockDeletion
