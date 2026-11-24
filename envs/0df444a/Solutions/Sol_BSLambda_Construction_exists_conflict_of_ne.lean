-- Prove2me | solution 1 for BSLambda.Construction.exists_conflict_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:50:34.841784+00:00
-- url     : https://prove2.me/submissions/7dfe2309-34fc-406e-b258-0217ded15624

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}


theorem solution (hT : IsTournament Arc) (hij : i ≠ j) :
    ∃ v : Coord ι r, (cert Arc γ i).Conflict (cert Arc γ j) v := by
  by_cases a : Arc i j
  · exact ⟨gateCoord γ i j, false, by simp [cert,gateCoord,hij.symm,a], by simp [cert,gateCoord]⟩
  · have b : Arc j i := by rw [hT.arc_eq_not_arc hij.symm]; simpa using a
    exact ⟨gateCoord γ j i, true, by simp [cert,gateCoord], by simp [cert,gateCoord,hij,b]⟩
