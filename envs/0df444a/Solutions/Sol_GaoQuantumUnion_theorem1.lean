-- Prove2me | solution 1 for GaoQuantumUnion.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T06:18:37.635659+00:00
-- url     : https://prove2.me/submissions/ea922edb-c77c-4d96-a756-00fe1559b68b

import Definitions.Def_GaoQuantumUnion_Model
import Theorems.Thm_GaoQuantumUnion_probability
import Theorems.Thm_GaoQuantumUnion_disturbance
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    1-4*failureSum P ρ ≤ successProb P ρ ∧
    (0 < successProb P ρ → traceDist ρ (postState P ρ) ≤ 2*Real.sqrt (failureSum P ρ)) ∧
    (successProb P ρ=1-4*failureSum P ρ ↔ ∀ i, failureTerm (P i) ρ=0) :=
  ⟨(GaoQuantumUnion.probability ρ hρ P hP).1,
   fun hq => GaoQuantumUnion.disturbance ρ hρ P hP hq,
   (GaoQuantumUnion.probability ρ hρ P hP).2⟩
