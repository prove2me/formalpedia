-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.Intertwined.sum
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:12:06.140336+00:00
-- url     : https://prove2.me/submissions/d2036393-04c0-4820-b5b0-6577c81480e5

import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2

open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.DifferentialL2

-- Finite sums preserve the registered intertwining equation by linearity.
theorem solution {ι : Type*} (s : Finset ι)
    {T : ι → lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel}
    {T' : ι → (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3))}
    (h : ∀ i ∈ s, Intertwined (T i) (T' i)) :
    Intertwined (∑ i ∈ s, T i) (∑ i ∈ s, T' i) := by
  intro x
  simp only [LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun i hi ↦ h i hi x)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
