-- Prove2me | solution 2 for DynFairDiv.Uniform.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:17:03.388489+00:00
-- url     : https://prove2.me/submissions/7c1776fb-63c1-4e27-bab4-3f4ed18aeba0

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

set_option autoImplicit false
open DynFairDiv.Uniform

theorem solution (ψ : ℕ → ℕ) (σ σ' : ℝ) (hσ' : σ' ≠ 0) (t : ℕ) :
    ffa ψ σ t = (ffa ψ σ' t).map (fun x => x * (σ / σ')) := by
  induction t with
  | zero => simp [ffa]
  | succ t ih =>
    rw [ffa, ffa, ih, List.map_append, List.map_drop, List.map_replicate]
    congr 2
    field_simp
