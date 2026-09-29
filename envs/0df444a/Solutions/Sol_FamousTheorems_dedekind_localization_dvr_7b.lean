-- Prove2me | solution 1 for FamousTheorems.dedekind_localization_dvr_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:59:24.083895+00:00
-- url     : https://prove2.me/submissions/ea9fb2a1-7544-4bcb-9822-8db8635cd06f

import Mathlib

theorem solution (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] {P : Ideal A} (hP : P ≠ ⊥) [P.IsPrime]
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] :
    IsDiscreteValuationRing Aₘ :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP Aₘ
