-- Prove2me | solution 1 for DynFairDiv.Uniform.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:00:39.12744+00:00
-- url     : https://prove2.me/submissions/0be77a8c-3ad9-4c9c-8854-0d03ebf3ff29

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

open DynFairDiv.Uniform

theorem solution (ψ : ℕ → ℕ) (σ σ' : ℝ) (hσ' : σ' ≠ 0) (t : ℕ) :
    ffa ψ σ t = (ffa ψ σ' t).map (fun x => x * (σ / σ')) := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    rw [ffa, ffa, ih, List.map_append, List.map_drop, List.map_replicate]
    congr 2
    field_simp
