-- Prove2me | solution 1 for FamousTheorems.dedekind_different_ramification_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:01:17.799147+00:00
-- url     : https://prove2.me/submissions/700f36c7-454a-4160-a393-bac96a7a0291

import Mathlib

theorem solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsDomain A] [IsDedekindDomain A]
    [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B] (P : Ideal B) [P.IsPrime] :
    letI := FractionRing.liftAlgebra A (FractionRing B)
    Algebra.IsSeparable (FractionRing A) (FractionRing B) →
      (¬P ∣ differentIdeal A B ↔ Algebra.IsUnramifiedAt A P) :=
  by intros; exact not_dvd_differentIdeal_iff
