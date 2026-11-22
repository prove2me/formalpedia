-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:53.39581+00:00
-- url     : https://prove2.me/submissions/8affddb6-a616-4dbf-9f1a-2aa0b87104e6

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Theorems.Thm_DeciSigma1_Words_retainedCount_lt_of_not_mem


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx
omit hx
namespace DeciSigma1.Holes.Periodic.AdmissibleDeletion
theorem _root_.solution {l : Fin k} {c₁ c₂ c' : ℕ} (h₁ :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c₁ c')
    (h₂ : CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c₂ c') :
    c₁ = c₂ := by
  obtain ⟨h1l, h1k, h1r⟩ := h₁
  obtain ⟨h2l, h2k, h2r⟩ := h₂
  unfold keepCut at h1k h2k
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := retainedCount_lt_of_not_mem (h1r (by omega)) h; omega
  · have := retainedCount_lt_of_not_mem (h2r (by omega)) h; omega
end DeciSigma1.Holes.Periodic.AdmissibleDeletion
