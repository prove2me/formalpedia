-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.channel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:48.764361+00:00
-- url     : https://prove2.me/submissions/d7f79458-da87-4b0f-918c-894d41732f76

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_matching
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_channel_pair_lifts_of_right_endpoint
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_delta_pos
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_length_not_mem_sitePositions
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_runPrefix_apply
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_text
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_strictlySeparated
public import Theorems.Thm_DeciSigma1_Holes_Fresh_prefix_of_matched
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_channel
public import Theorems.Thm_DeciSigma1_Readers_Table_pair_mem_channel
public import Theorems.Thm_DeciSigma1_Words_greatestPreimage_le_length


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
    (i j : Fin k) : T.channel m.apply i j ⊆ T.channel W i j := by
  intro pq hpq
  obtain ⟨a, ha, b, hb, hpre, rfl⟩ := Table.mem_channel.mp hpq
  have hL : (m.apply j).length = b + ((m.apply j).length - b) := by omega
  set L := (m.apply j).length - b
  by_cases hA : ∃ d, 0 < d ∧ d < L ∧ IsJunction m.deletionLength (m.sites i) (a + d) ∧ L < d +
      m.upperCutLength
  · obtain ⟨d, hd0, hdL, hJ, hlt⟩ := hA
    exact m.channel_pair_lifts_of_right_endpoint hfr hL hpre hd0 hdL hJ hlt
  · have hB : ∀ d, 0 < d → d < L → IsJunction m.deletionLength (m.sites i) (a + d) → d +
      m.upperCutLength ≤ L :=
      fun d h1 h2 h3 => Nat.le_of_not_lt fun h => hA ⟨d, h1, h2, h3, h⟩
    have hm := m.matching hfr hL hpre hB
    have hold :=
        prefix_of_matched (m.delta_pos) (m.strictlySeparated i)
            (m.strictlySeparated j)
      (fun c hc => m.site_text hc) (fun c hc => m.site_text hc) L a b hL hpre hm
    rw [m.runPrefix_apply i a, m.runPrefix_apply j b]
    exact Table.pair_mem_channel
      (greatestPreimage_le_length _ (m.length_not_mem_sitePositions i) ha)
      (greatestPreimage_le_length _ (m.length_not_mem_sitePositions j) hb) hold
end DeciSigma1.Holes.Fresh.BlockDeletion
