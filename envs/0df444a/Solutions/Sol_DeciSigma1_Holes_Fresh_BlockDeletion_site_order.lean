-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.site_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:26.072333+00:00
-- url     : https://prove2.me/submissions/7532c25b-20ac-4540-ac0b-36c6e34ae98a

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOcc_ext
public import Theorems.Thm_DeciSigma1_Holes_Fresh_upperOccurrences_le_start


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
theorem _root_.solution {o o' : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (ho' : o' ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o) (hth' : m.edge.TraversedBy o')
        (hl : o.1 = o'.1)
    (hlt : depthCut W t o m.maxDepth < depthCut W t o' m.maxDepth) : o.2.2 ≤ o'.2.1 := by
  have s1 := m.site_spec ho hth
  have s2 := m.site_spec ho' hth'
  rcases lt_trichotomy o.2.2 o'.2.2 with h | h | h
  · exact upperOccurrences_le_start ho ho' hl h
  · have := upperOcc_ext ho ho' hl h; subst this; omega
  · have := upperOccurrences_le_start ho' ho hl.symm h; omega
end DeciSigma1.Holes.Fresh.BlockDeletion
