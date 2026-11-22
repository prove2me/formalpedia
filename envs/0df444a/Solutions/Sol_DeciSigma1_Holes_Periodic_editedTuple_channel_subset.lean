-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.editedTuple_channel_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:24.219804+00:00
-- url     : https://prove2.me/submissions/e8514efb-9075-40e8-bbc4-045c0daa7580

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
public import Theorems.Thm_DeciSigma1_Holes_Periodic_drop_prefix_iff_suffixComparison
public import Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_suffixComparison_lift
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_channel


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution (T : Table α S k)
    (hx : AdmissibleDeletion W ρ (Fintype.card S) x) (i j : Fin k) :
    T.channel (editedTuple W ρ (Fintype.card S) x) i j ⊆ T.channel W i j := by
  intro pq hpq
  obtain ⟨a', ha', b', hb', hpre, rfl⟩ := mem_channel.mp hpq
  have hN : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨T.start i⟩
  obtain ⟨a, ha, b, hb, hcmp, hqa, hqb⟩ :=
    hx.suffixComparison_lift T rfl hN i j ha' hb' (drop_prefix_iff_suffixComparison.mp hpre)
  exact mem_channel.mpr ⟨a, ha, b, hb, drop_prefix_iff_suffixComparison.mpr hcmp, by rw [hqa, hqb]⟩
end DeciSigma1.Holes.Periodic
