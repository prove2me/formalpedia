-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.tail_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:46.992542+00:00
-- url     : https://prove2.me/submissions/894d4293-44f3-47b1-a20d-a813368a9c0c

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_delta_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_text
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Holes_Fresh_retainedCount_dist
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_drop_deleteSites
public import Theorems.Thm_DeciSigma1_Words_deletePositions_empty
public import Theorems.Thm_DeciSigma1_Words_deletePositions_nil
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_retainedCount
public import Theorems.Thm_DeciSigma1_Words_length_deletePositions
public import Theorems.Thm_DeciSigma1_Words_retainedCount_empty
public import Theorems.Thm_DeciSigma1_Words_retainedCount_greatestPreimage
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono
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
theorem _root_.solution {l : Fin k} {P : ℕ}
    (hP : ∀ c ∈ m.sites l, c + m.deletionLength + P ≤ (W l).length) (hPl : P ≤ (W l).length)
    {b' : ℕ} (hb1 : (m.apply l).length - P ≤ b') (hb2 : b' ≤ (m.apply l).length) :
    (m.apply l).drop b' = (W l).drop ((W l).length - ((m.apply l).length - b')) ∧
      greatestPreimage (sitePositions m.deletionLength (m.sites l)) b' = (W l).length -
          ((m.apply l).length - b') := by
  have hδ := m.delta_pos
  have hret0 : Retained m.deletionLength (m.sites l) ((W l).length - P) := by
    intro c hc ⟨h1, h2⟩; have := hP c hc; omega
  have hdist : ∀ q, (W l).length - P ≤ q → q ≤ (W l).length →
      retainedCount (sitePositions m.deletionLength (m.sites l)) q =
        retainedCount (sitePositions m.deletionLength (m.sites l)) ((W l).length - P) +
          (q - ((W l).length - P)) := by
    intro q h1 h2
    exact retainedCount_dist hret0 h1 (fun c hc ⟨h3, h4⟩ => by have := hP c hc; omega)
  have hk0 := hdist (W l).length (by omega) le_rfl
  rw [← length_deletePositions, ← BlockDeletion.apply] at hk0
  set p := (W l).length - ((m.apply l).length - b')
  have hp1 : (W l).length - P ≤ p := by omega
  have hkp : retainedCount (sitePositions m.deletionLength (m.sites l)) p = b' := by
    rw [hdist p hp1 (by omega)]; omega
  have hpn : p ∉ sitePositions m.deletionLength (m.sites l) := by
    intro hm
    obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp hm
    have := hP c hc
    have := (m.site_text hc).1
    omega
  have hkR : greatestPreimage (sitePositions m.deletionLength (m.sites l)) b' = p := by
    rw [← hkp]; exact greatestPreimage_retainedCount hpn
  refine ⟨?_, hkR⟩
  have hfree : ∀ J, IsJunction m.deletionLength (m.sites l) J →
      ¬ (b' < J ∧ J < b' + ((m.apply l).length - b')) := by
    rintro J ⟨c, hc, rfl⟩ ⟨h1, -⟩
    have h3 := retainedCount_mono (D := sitePositions m.deletionLength (m.sites l))
      (show c ≤ (W l).length - P by have := hP c hc; omega)
    have h4 := hdist ((W l).length - P) le_rfl (by omega)
    omega
  have hw : ((m.apply l).drop b').take ((m.apply l).length - b') =
      ((W l).drop (greatestPreimage (sitePositions m.deletionLength (m.sites l)) b')).take
        ((m.apply l).length - b') := take_drop_deleteSites _ hfree
  rw [hkR, List.take_of_length_le (by simp), List.take_of_length_le (by simp; omega)] at hw
  exact hw
end DeciSigma1.Holes.Fresh.BlockDeletion
