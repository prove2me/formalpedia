-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_equiv_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/511f779b-4126-50e5-9451-e6657c0d044b

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_equiv_points

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [Field k] [IsAlgClosed k] (hℓk : (ℓ : k) ≠ 0)
    (E : FakeEllipticCurve Λ N k) (K : E.ExtraLevel ℓ) :
    ∃ e : ZMod ℓ × ZMod ℓ ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough K.levK P},
      ∀ x y : ZMod ℓ × ZMod ℓ,
        ((e (x + y) : {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f // FactorsThrough K.levK P}) :
            SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) E.f) =
          E.L.mul (𝟙 (Spec (CommRingCat.of k))) (e x) (e y) := by
  have h : geomPoint k (RingHom.id k) = 𝟙 (Spec (CommRingCat.of k)) := by
    simp [geomPoint]
  exact h ▸ K.levK_fibre k (RingHom.id k) hℓk

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_equiv_points
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_equiv_points (solution)
