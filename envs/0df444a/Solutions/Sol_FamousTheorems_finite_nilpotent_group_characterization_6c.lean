-- Prove2me | solution 1 for FamousTheorems.finite_nilpotent_group_characterization_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:06:10.722981+00:00
-- url     : https://prove2.me/submissions/65a32f0e-6fb3-491c-862c-7677bc1946d1

import Mathlib

theorem solution {G : Type*} [Group G] [Finite G] :
    List.TFAE
      [Group.IsNilpotent G, NormalizerCondition G, ∀ H : Subgroup G, IsCoatom H → H.Normal,
        ∀ (p : ℕ) (_ : Fact p.Prime) (P : Sylow p G), (P : Subgroup G).Normal,
        Nonempty ((∀ p : (Nat.card G).primeFactors, ∀ P : Sylow p G, (P : Subgroup G)) ≃* G)] :=
  Group.isNilpotent_of_finite_tfae
