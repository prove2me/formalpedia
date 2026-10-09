-- Prove2me | solution 1 for BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_gauge_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:24:30.678578+00:00
-- url     : https://prove2.me/submissions/49fb5bfb-0463-488f-9b75-3703b4380320

-- Generated from ChapterGaugeAdjointAlgebra.lean — solution of BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_gauge_invariant
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
import Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_inner_adjVar_self_eq_zero
open BookProof.ChapterGaugeAdjointAlgebra





open Finset

variable {L : Type*} [LieRing L]

variable {L : Type*} [LieRing L]

set_option maxHeartbeats 1000000 in
theorem solution {κ : L → L → ℝ}
    (hinv : ∀ x y z : L, κ ⁅x, z⁆ y + κ x ⁅y, z⁆ = 0)
    (hsymm : ∀ x y : L, κ x y = κ y x)
    (π : Fin 3 → L) (B : Fin 3 → Fin 3 → L) (θ : L) :
    (∑ i, κ ⁅π i, θ⁆ (π i)) + (1 / 2) * ∑ i, ∑ j, κ ⁅B i j, θ⁆ (B i j) = 0 := by

  have h1 : ∀ i, κ ⁅π i, θ⁆ (π i) = 0 := fun i =>
    inner_adjVar_self_eq_zero hinv hsymm _ _
  have h2 : ∀ i j, κ ⁅B i j, θ⁆ (B i j) = 0 := fun i j =>
    inner_adjVar_self_eq_zero hinv hsymm _ _
  simp [h1, h2]
