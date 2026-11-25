-- Prove2me | solution 1 for ChromaticReconstruction.mem_edgeSet_PL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:41:51.509645+00:00
-- url     : https://prove2.me/submissions/2c1302be-b5fb-44a2-b8b3-9a5c520e0944

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
import Theorems.Thm_ChromaticReconstruction_vx_val
import Theorems.Thm_ChromaticReconstruction_vx_eq_self
import Theorems.Thm_ChromaticReconstruction_PL_adj_vx
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.vx_val

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c : ℕ} (hc : c < n) (e : Sym2 (Fin (n + 1))) :
    e ∈ (PL n c).edgeSet ↔ (∃ i, i + 1 < n ∧ e = pe n i) ∨ e = lf n c := by
  induction e using Sym2.ind with
  | _ x y =>
  rw [SimpleGraph.mem_edgeSet, ← vx_eq_self x, ← vx_eq_self y,
    PL_adj_vx (by omega) (by omega)]
  have hx := x.isLt
  have hy := y.isLt
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩)
    · exact Or.inl ⟨x.val, by omega, by rw [pe, ← h1]⟩
    · exact Or.inl ⟨y.val, by omega, by rw [pe, ← h1, Sym2.eq_swap]⟩
    · exact Or.inr (by rw [lf, h1, h2])
    · exact Or.inr (by rw [lf, h1, h2, Sym2.eq_swap])
  · rintro (⟨i, hi, h⟩ | h)
    · simp only [pe, Sym2.eq_iff, Fin.ext_iff, vx_val] at h
      omega
    · simp only [lf, Sym2.eq_iff, Fin.ext_iff, vx_val] at h
      omega
end ChromaticReconstruction
