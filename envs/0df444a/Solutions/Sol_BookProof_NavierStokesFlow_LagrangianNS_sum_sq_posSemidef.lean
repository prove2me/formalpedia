-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianNS.sum_sq_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T01:00:15.480214+00:00
-- url     : https://prove2.me/submissions/715699fe-645b-4c5b-8e25-37c2e84991c0

import Mathlib.Analysis.Matrix.PosDef

open scoped BigOperators Matrix ComplexOrder

theorem solution {m : ℕ} {R : Fin 3 → Matrix (Fin m) (Fin m) ℂ}
    (hR : ∀ i, (R i)ᴴ = R i) : (∑ i, R i * R i).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [hR i] using Matrix.posSemidef_conjTranspose_mul_self (R i)

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solution
