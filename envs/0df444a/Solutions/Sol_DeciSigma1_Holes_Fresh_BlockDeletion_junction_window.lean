-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.junction_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:27.932817+00:00
-- url     : https://prove2.me/submissions/aa848674-bb47-47c2-b921-8916171c60c4

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_upperCutLength_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_order
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_delta_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_strictlySeparated
public import Theorems.Thm_DeciSigma1_Holes_Fresh_StrictlySeparated_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_greatestPreimage_site
public import Theorems.Thm_DeciSigma1_Holes_Fresh_retainedCount_dist
public import Theorems.Thm_DeciSigma1_Holes_Fresh_retainedCount_site_right
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_drop_deleteSites
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_spec
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono


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
theorem _root_.solution {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    greatestPreimage (sitePositions m.deletionLength (m.sites l))
        (retainedCount (sitePositions m.deletionLength (m.sites l)) c) = c + m.deletionLength ∧
    (∀ J', IsJunction m.deletionLength (m.sites l) J' →
      J' ≤ retainedCount (sitePositions m.deletionLength (m.sites l)) c ∨
        retainedCount (sitePositions m.deletionLength (m.sites l)) c + m.upperCutLength ≤ J') ∧
    retainedCount (sitePositions m.deletionLength (m.sites l)) c + m.upperCutLength ≤
      (m.apply l).length ∧
    ((m.apply l).drop (retainedCount (sitePositions m.deletionLength (m.sites l)) c)).take
        m.upperCutLength =
      ((W l).drop (c + m.deletionLength)).take m.upperCutLength := by
  have hδ := m.delta_pos
  have hs := m.strictlySeparated l
  set cs := m.sites l with hcs
  obtain ⟨o, ho, hol, hth, hoc⟩ := m.site_occ hc
  have hnt := m.upperCutLength_spec ho hth
  rw [hoc] at hnt
  have hEl := (upperOcc_spec ho).2.1
  rw [hol] at hEl
  -- every other site is left of `c` or right of the end of its upper block
  have hother : ∀ c' ∈ cs, c' < c ∨ c' = c ∨ o.2.2 < c' := by
    intro c' hc'
    rcases lt_trichotomy c' c with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right
      obtain ⟨o', ho', hol', hth', hoc'⟩ := m.site_occ hc'
      have := m.site_order ho ho' hth hth' (hol.trans hol'.symm) (by rw [hoc, hoc']; exact h)
      have := m.site_spec ho' hth'
      omega
  have hretE : Retained m.deletionLength cs o.2.2 := by
    intro c' hc' ⟨h1, h2⟩
    rcases hother c' hc' with h | h | h
    · have := hs.lt hc' hc h; omega
    · omega
    · omega
  have hretc' : Retained m.deletionLength cs (c + m.deletionLength) := by
    intro c' hc' ⟨h1, h2⟩
    rcases hother c' hc' with h | h | h
    · have := hs.lt hc' hc h; omega
    · omega
    · omega
  have hkE : retainedCount (sitePositions m.deletionLength cs) o.2.2 =
      retainedCount (sitePositions m.deletionLength cs) c + m.upperCutLength := by
    rw [retainedCount_dist hretc' (q := o.2.2) (by omega) (fun c' hc' ⟨h1, h2⟩ => by
      rcases hother c' hc' with h | h | h <;> omega), retainedCount_site_right hc]
    congr 1; omega
  have j2 := greatestPreimage_site hs hc
  have hsep : ∀ J', IsJunction m.deletionLength cs J' →
      J' ≤ retainedCount (sitePositions m.deletionLength cs) c ∨
        retainedCount (sitePositions m.deletionLength cs) c + m.upperCutLength ≤ J' := by
    rintro J' ⟨c', hc', rfl⟩
    rcases hother c' hc' with h | h | h
    · exact Or.inl (retainedCount_mono h.le)
    · exact Or.inl (by rw [h])
    · exact Or.inr (hkE ▸ retainedCount_mono h.le)
  refine ⟨j2, hsep, ?_, ?_⟩
  · rw [← hkE, BlockDeletion.apply, length_deletePositions]
    exact retainedCount_mono hEl
  · rw [← j2]
    refine take_drop_deleteSites _ (fun J' hJ' ⟨h1, h2⟩ => ?_)
    rcases hsep J' hJ' with h | h <;> omega
end DeciSigma1.Holes.Fresh.BlockDeletion
