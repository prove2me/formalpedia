-- Prove2me | solution 1 for BSLambda.le_bsAt_of_family
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:53:49.683693+00:00
-- url     : https://prove2.me/submissions/c24ee33a-d028-41b5-b526-e627f9910cad

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]


theorem solution [Finite V] {f : Input V → Bool} {x : Input V} {𝓑 : Finset (Finset V)}
    (h : IsBlockFamily f x 𝓑) : 𝓑.card ≤ bsAt f x := by
  classical
  letI := Fintype.ofFinite V
  apply le_csSup _ (show 𝓑.card ∈ blockFamilyCards f x from ⟨𝓑,h,rfl⟩)
  refine ⟨Fintype.card (Finset V),?_⟩
  rintro n ⟨F,hF,rfl⟩; exact Finset.card_le_univ F
