-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.junction_not_in_labelWindow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:36:14.823127+00:00
-- url     : https://prove2.me/submissions/c456d7f8-9ab3-4ab2-a331-b15e6ca5a4e0

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_compatible_window
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_delta_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_strictlySeparated
public import Theorems.Thm_DeciSigma1_Holes_Fresh_StrictlySeparated_lt
public import Theorems.Thm_DeciSigma1_Holes_Fresh_greatestPreimage_site
public import Theorems.Thm_DeciSigma1_Holes_Fresh_retainedCount_dist
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
theorem _root_.solution [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {l : Fin k} {c J' : ℕ} (hc : c ∈ m.sites l)
    (hJ' : IsJunction m.deletionLength (m.sites l) J')
    (h1 : retainedCount (sitePositions m.deletionLength (m.sites l)) c -
      windowLength W t (W l) c < J')
    (h2 : J' < retainedCount (sitePositions m.deletionLength (m.sites l)) c) : False := by
  obtain ⟨c₂, hc₂, rfl⟩ := hJ'
  have hs := m.strictlySeparated l
  have hδ := m.delta_pos
  rcases lt_trichotomy c₂ c with hlt | rfl | hgt
  · -- the sites before `c` end before its label window, which is therefore retained text
    have hwin : ∀ c₃ ∈ m.sites l, c₃ < c →
        c₃ + m.deletionLength + windowLength W t (W l) c ≤ c :=
      fun c₃ hc₃ h => m.compatible_window hfr hc hc₃ h
    have hret : Retained m.deletionLength (m.sites l) (c - windowLength W t (W l) c) := by
      intro c₃ hc₃ ⟨h3, h4⟩
      rcases lt_trichotomy c₃ c with h5 | rfl | h5
      · have := hwin c₃ hc₃ h5; omega
      · omega
      · have := hs.lt hc hc₃ h5; omega
    have := hwin c₂ hc₂ hlt
    have hk1 := retainedCount_mono (D := sitePositions m.deletionLength (m.sites l))
      (show c₂ ≤ c - windowLength W t (W l) c by omega)
    have hk2 := retainedCount_dist hret (q := c) (by omega) fun c₃ hc₃ ⟨h3, h4⟩ => by
      rcases lt_trichotomy c₃ c with h5 | rfl | h5
      · have := hwin c₃ hc₃ h5; omega
      · omega
      · omega
    omega
  · omega
  · -- a later site has a later junction
    have := retainedCount_mono (D := sitePositions m.deletionLength (m.sites l)) hgt.le
    have hne' : retainedCount (sitePositions m.deletionLength (m.sites l)) c₂ ≠
        retainedCount (sitePositions m.deletionLength (m.sites l)) c := by
      intro he
      have k1 := greatestPreimage_site hs hc
      have k2 := greatestPreimage_site hs hc₂
      rw [he] at k2
      omega
    omega
end DeciSigma1.Holes.Fresh.BlockDeletion
