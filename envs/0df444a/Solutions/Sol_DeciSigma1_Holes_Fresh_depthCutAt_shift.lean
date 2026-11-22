-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.depthCutAt_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:50.941193+00:00
-- url     : https://prove2.me/submissions/a9de36b8-305c-44b9-b426-37c91bd80dc3

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Theorems.Thm_DeciSigma1_Holes_Fresh_anchorCount_self
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCutAt_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_previousAnchor
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_le
public import Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_spec


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {A Q : Finset ℕ} {base n lo : ℕ}
    (hag : ∀ q, lo ≤ q → q ≤ n → (base + q ∈ A ↔ q ∈ Q)) (hlo : lo ∈ Q) (hn : n ∈ Q)
    (hlon : lo ≤ n) : ∀ d ≤ anchorCount Q lo n, depthCutAt A (base + n) d = base +
        depthCutAt Q n d := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    have hlt : lo < n := by
      rcases Nat.eq_or_lt_of_le hlon with h | h
      · subst h; rw [anchorCount_self] at hd; omega
      · exact h
    obtain ⟨hall, hlast⟩ := depthCutAt_spec hlt hn (Or.inr hlo)
    obtain ⟨hrQ, hlr, hrn, -⟩ := hall d (by omega)
    have hr' : depthCutAt Q n (d + 1) ∈ Q ∧ lo ≤ depthCutAt Q n (d + 1) := by
      rcases Nat.lt_or_ge (d + 1) (anchorCount Q lo n) with h | h
      · obtain ⟨h1, h2, -, -⟩ := hall (d + 1) h; exact ⟨h1, h2.le⟩
      · have : d + 1 = anchorCount Q lo n := by omega
        rw [this, hlast]; exact ⟨hlo, le_rfl⟩
    have hprev : depthCutAt Q n (d + 1) = previousAnchor Q (depthCutAt Q n d) := rfl
    have hlt' : depthCutAt Q n (d + 1) < depthCutAt Q n d := by
      rw [hprev]; exact (previousAnchor_spec ⟨lo, hlo, hlr⟩).2
    change previousAnchor A (depthCutAt A (base + n) d) = base + depthCutAt Q n (d + 1)
    rw [ih (by omega)]
    apply le_antisymm
    · apply previousAnchor_le
      intro q hq hqr
      by_contra hcon
      have hqQ : q - base ∈ Q := (hag (q - base) (by omega) (by omega)).mp
        (by rwa [Nat.add_sub_cancel' (by omega)])
      have := le_previousAnchor hqQ (show q - base < depthCutAt Q n d by omega)
      rw [← hprev] at this
      omega
    · exact le_previousAnchor ((hag _ hr'.2 (by omega)).mpr hr'.1) (by omega)
end DeciSigma1.Holes.Fresh
