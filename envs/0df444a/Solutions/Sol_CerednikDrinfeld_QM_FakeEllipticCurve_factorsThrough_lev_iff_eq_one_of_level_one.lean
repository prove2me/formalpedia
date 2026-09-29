-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.factorsThrough_lev_iff_eq_one_of_level_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c07f430b-6524-51ac-bc30-ddfd44448b7e

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_eq_one_of_level_one

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ 1 S)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    FactorsThrough E.lev P ↔ P = E.L.one t := by
  constructor
  · intro h
    have h1 := E.lev_torsion t P h
    change E.L.mul t (E.L.one t) P = E.L.one t at h1
    rwa [E.L.one_mul] at h1
  · rintro rfl
    exact E.lev_one t

end S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_eq_one_of_level_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_iff_eq_one_of_level_one (solution)
