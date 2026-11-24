-- Prove2me | solution 1 for BSLambda.Construction.cert_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:50:37.368158+00:00
-- url     : https://prove2.me/submissions/7f40fddf-5a65-4835-8ce8-bf5516e29914

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι} {v : Coord ι r} {b : Bool}


theorem solution :
    cert Arc γ i v = some b ↔
      (v.1 = i ∧ b = true) ∨ (v.1 ≠ i ∧ Arc i v.1 ∧ v.2 = γ i v.1 ∧ b = false) := by
  by_cases e : v.1 = i <;> by_cases a : Arc i v.1 <;> by_cases k : v.2 = γ i v.1 <;> cases b <;> simp [cert,e,a,k]
