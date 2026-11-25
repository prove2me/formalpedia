-- Prove2me | solution 1 for ChromaticReconstruction.mem_extEdges_inr_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:48:27.307795+00:00
-- url     : https://prove2.me/submissions/f9040917-b2d4-4c8b-9bce-ee3f325b975a

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster
import Theorems.Thm_ChromaticReconstruction_mem_extEdges_inl_inr

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
namespace ChromaticReconstruction
theorem _root_.solution {l0 : Σ i, Fin (m i)} {F : Finset (Sym2 K)} {a : K}
    {l : Σ i, Fin (m i)} :
    s(.inr l, .inl a) ∈ extEdges m l0 F ↔ l.1 = a ∧ l ≠ l0 := by
  rw [Sym2.eq_swap]; exact mem_extEdges_inl_inr
end ChromaticReconstruction
