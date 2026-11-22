-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.sites_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:32:01.822805+00:00
-- url     : https://prove2.me/submissions/792fb93d-95a7-4cc1-9ccf-d02fe39761c8

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_mem_sites
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_ext
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOccurrences_le_start
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution {l : Fin k} {c c' : ℕ} (hc : c ∈ m.sites l)
    (hc' : c' ∈ m.sites l) (hlt : c < c') : c + m.deletionLength < c' := by
  obtain ⟨o, ho, hl, hth, rfl⟩ := m.mem_sites.mp hc
  obtain ⟨o', ho', hl', hth', rfl⟩ := m.mem_sites.mp hc'
  have s1 := m.site_spec ho hth
  have s2 := m.site_spec ho' hth'
  rcases lt_trichotomy o.2.2 o'.2.2 with h | h | h
  · have := upperOccurrences_le_start ho ho' (hl.trans hl'.symm) h
    omega
  · have := upperOcc_ext ho ho' (hl.trans hl'.symm) h
    subst this; omega
  · have := upperOccurrences_le_start ho' ho (hl'.trans hl.symm) h
    omega
end DeciSigma1.Holes.Fresh.BlockDeletion
