-- Prove2me | solution 1 for DegreeSequences.egReduce_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:47:25.87829+00:00
-- url     : https://prove2.me/submissions/887d6ff9-3c7a-4ff4-b055-4739359d5521

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) (htp : t ≠ p) (ht : 1 ≤ d t)
    (hp : 1 ≤ d p) (i : Fin n) :
    d i = egReduce d t p i + (if i = t then 1 else 0) + (if i = p then 1 else 0) := by
  unfold egReduce
  rcases eq_or_ne i t with rfl | hit
  · simp [htp]; omega
  rcases eq_or_ne i p with rfl | hip
  · simp [hit]; omega
  simp [hit, hip]
end DegreeSequences
