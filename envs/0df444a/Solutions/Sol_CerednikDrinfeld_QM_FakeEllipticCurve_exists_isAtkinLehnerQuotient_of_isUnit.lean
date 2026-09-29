-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotient_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/3da0acd8-19d7-59ca-aec3-b08126da394d

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotient_of_isUnit
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion
open CerednikDrinfeld QuaternionAlgebra

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (r : ℕ) (hr : r = q ∨ r = q')
    (S : Type) [CommRing S] (hrS : IsUnit ((r : ℕ) : S)) (E : QM.FakeEllipticCurve Λ N S) :
    ∃ E' : QM.FakeEllipticCurve Λ N S, QM.FakeEllipticCurve.IsAtkinLehnerQuotient r E E' :=
  CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotient hqq' hB Λ hΛ hqN hq'N r hr S E

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotient_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotient_of_isUnit (solution)
