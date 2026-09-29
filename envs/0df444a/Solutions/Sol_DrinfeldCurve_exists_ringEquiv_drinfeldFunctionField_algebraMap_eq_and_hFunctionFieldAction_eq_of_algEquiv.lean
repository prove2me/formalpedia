-- Prove2me | solution 1 for DrinfeldCurve.exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3561e3d3-c27c-5fb6-805e-bde3bed4c29c

import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv

set_option autoImplicit false

open MvPolynomial

namespace DrinfeldPhi

open DrinfeldCurve

variable (q : ℕ) {k k' : Type} [Field k] [Field k']

private theorem mapEquiv_drinfeldPoly_sub_one (e : k ≃+* k') :
    MvPolynomial.mapEquiv (Fin 2) e (drinfeldPoly q k - 1) = drinfeldPoly q k' - 1 := by
  simp [MvPolynomial.mapEquiv_apply, drinfeldPoly, map_sub, map_mul, map_pow, MvPolynomial.map_X, map_one]

private theorem drinfeldIdeal_eq_map (e : k ≃+* k') :
    drinfeldIdeal q k' = (drinfeldIdeal q k).map (MvPolynomial.mapEquiv (Fin 2) e : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k') := by
  rw [drinfeldIdeal, drinfeldIdeal, Ideal.map_span, Set.image_singleton]
  congr 2
  exact (mapEquiv_drinfeldPoly_sub_one q e).symm

private noncomputable def coordEquiv (e : k ≃+* k') : CoordRing q k ≃+* CoordRing q k' :=
  Ideal.quotientEquiv (drinfeldIdeal q k) (drinfeldIdeal q k') (MvPolynomial.mapEquiv (Fin 2) e)
    (drinfeldIdeal_eq_map q e)

private theorem coordEquiv_mk (e : k ≃+* k') (p : MvPolynomial (Fin 2) k) :
    coordEquiv q e (DrinfeldCurve.mk q k p) = DrinfeldCurve.mk q k' (MvPolynomial.map (e : k →+* k') p) := by
  show Ideal.quotientEquiv _ _ _ _ (Ideal.Quotient.mk (drinfeldIdeal q k) p) = Ideal.Quotient.mk (drinfeldIdeal q k') _
  rw [Ideal.quotientEquiv_mk]
  rfl

private theorem coordEquiv_algebraMap (e : k ≃+* k') (a : k) :
    coordEquiv q e (algebraMap k (CoordRing q k) a) = algebraMap k' (CoordRing q k') (e a) := by
  have h1 : algebraMap k (CoordRing q k) a = DrinfeldCurve.mk q k (C a) := by
    rw [← MvPolynomial.algebraMap_eq]; rfl
  have h2 : algebraMap k' (CoordRing q k') (e a) = DrinfeldCurve.mk q k' (C (e a)) := by
    rw [← MvPolynomial.algebraMap_eq]; rfl
  rw [h1, h2, coordEquiv_mk, MvPolynomial.map_C]
  rfl

private theorem coordEquiv_x (e : k ≃+* k') : coordEquiv q e (DrinfeldCurve.x q k) = DrinfeldCurve.x q k' := by
  rw [DrinfeldCurve.x, DrinfeldCurve.x, coordEquiv_mk, MvPolynomial.map_X]

private theorem coordEquiv_y (e : k ≃+* k') : coordEquiv q e (DrinfeldCurve.y q k) = DrinfeldCurve.y q k' := by
  rw [DrinfeldCurve.y, DrinfeldCurve.y, coordEquiv_mk, MvPolynomial.map_X]

section Action

variable [Fact q.Prime] [Algebra (GaloisField q 2) k] [Algebra (GaloisField q 2) k']

private theorem algEquiv_ofZMod (e : k ≃ₐ[GaloisField q 2] k') (a : ZMod q) : e (ofZMod q k a) = ofZMod q k' a := by
  show e (algebraMap (GaloisField q 2) k (algebraMap (ZMod q) (GaloisField q 2) a)) =
    algebraMap (GaloisField q 2) k' (algebraMap (ZMod q) (GaloisField q 2) a)
  exact e.commutes _

private theorem algEquiv_scalarOf (e : k ≃ₐ[GaloisField q 2] k') (ζ : (GaloisField q 2)ˣ) :
    e (scalarOf q k ζ) = scalarOf q k' ζ :=
  e.commutes _

private theorem map_substPoly (e : k ≃ₐ[GaloisField q 2] k') (g : Matrix (Fin 2) (Fin 2) (ZMod q)) (p : MvPolynomial (Fin 2) k) :
    MvPolynomial.map (e : k →+* k') (substPoly q k g p) = substPoly q k' g (MvPolynomial.map (e : k →+* k') p) := by

  have key : (MvPolynomial.map (e : k →+* k')).comp (substPoly q k g : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k) =
      (substPoly q k' g : MvPolynomial (Fin 2) k' →+* MvPolynomial (Fin 2) k').comp (MvPolynomial.map (e : k →+* k')) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
        MvPolynomial.map_C]
    · intro j
      simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_X, substPoly_X, map_sum, map_mul,
        MvPolynomial.map_C, MvPolynomial.map_X, RingHom.coe_coe]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [algEquiv_ofZMod]
  exact RingHom.congr_fun key p

private theorem map_scalePoly (e : k ≃ₐ[GaloisField q 2] k') (ζ : (GaloisField q 2)ˣ) (p : MvPolynomial (Fin 2) k) :
    MvPolynomial.map (e : k →+* k') (scalePoly k (scalarOf q k ζ) p) =
      scalePoly k' (scalarOf q k' ζ) (MvPolynomial.map (e : k →+* k') p) := by
  have key : (MvPolynomial.map (e : k →+* k')).comp (scalePoly k (scalarOf q k ζ) : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k) =
      (scalePoly k' (scalarOf q k' ζ) : MvPolynomial (Fin 2) k' →+* MvPolynomial (Fin 2) k').comp (MvPolynomial.map (e : k →+* k')) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
        MvPolynomial.map_C]
    · intro j
      simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_X, scalePoly_X, map_mul,
        MvPolynomial.map_C, MvPolynomial.map_X]
      rw [algEquiv_scalarOf]
  exact RingHom.congr_fun key p

private theorem coordEquiv_hAction (e : k ≃ₐ[GaloisField q 2] k') (h : hSubgroup q) (a : CoordRing q k) :
    coordEquiv q (e : k ≃+* k') (hAction q k h a) = hAction q k' h (coordEquiv q (e : k ≃+* k') a) := by
  obtain ⟨p, rfl⟩ := DrinfeldCurve.mk_surjective q k a
  rw [hAction_mk, coordEquiv_mk, coordEquiv_mk, hAction_mk]
  congr 1
  rw [show ((e : k ≃+* k') : k →+* k') = ((e : k →+* k')) from rfl, map_scalePoly, map_substPoly]

end Action

end DrinfeldPhi

open DrinfeldCurve

theorem solution
    (q : ℕ) [Fact q.Prime]
    (k : Type) [Field k] [Algebra (GaloisField q 2) k] [IsDomain (DrinfeldCurve.CoordRing q k)]
    (k' : Type) [Field k'] [Algebra (GaloisField q 2) k'] [IsDomain (DrinfeldCurve.CoordRing q k')]
    (e : k ≃ₐ[GaloisField q 2] k') :
    ∃ φ : drinfeldFunctionField q k ≃+* drinfeldFunctionField q k',
      (∀ a : k, φ (algebraMap k (drinfeldFunctionField q k) a) = algebraMap k' (drinfeldFunctionField q k') (e a)) ∧
      φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (DrinfeldCurve.x q k)) =
        algebraMap (CoordRing q k') (drinfeldFunctionField q k') (DrinfeldCurve.x q k') ∧
      φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (DrinfeldCurve.y q k)) =
        algebraMap (CoordRing q k') (drinfeldFunctionField q k') (DrinfeldCurve.y q k') ∧
      (∀ (h : hSubgroup q) (f : drinfeldFunctionField q k),
        φ (hFunctionFieldAction q k h f) = hFunctionFieldAction q k' h (φ f)) := by
  classical
  set ψ : CoordRing q k ≃+* CoordRing q k' := DrinfeldPhi.coordEquiv q (e : k ≃+* k') with hψ
  let φ : drinfeldFunctionField q k ≃+* drinfeldFunctionField q k' := IsFractionRing.ringEquivOfRingEquiv ψ
  have hφ : ∀ a : CoordRing q k, φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) a) =
      algebraMap (CoordRing q k') (drinfeldFunctionField q k') (ψ a) :=
    fun a => IsFractionRing.ringEquivOfRingEquiv_algebraMap ψ a
  refine ⟨φ, fun a => ?_, ?_, ?_, fun h => ?_⟩
  · rw [IsScalarTower.algebraMap_apply k (CoordRing q k) (drinfeldFunctionField q k) a, hφ,
      hψ, DrinfeldPhi.coordEquiv_algebraMap,
      ← IsScalarTower.algebraMap_apply k' (CoordRing q k') (drinfeldFunctionField q k')]
    rfl
  · rw [hφ, hψ, DrinfeldPhi.coordEquiv_x]
  · rw [hφ, hψ, DrinfeldPhi.coordEquiv_y]
  ·
    have key : ((φ : drinfeldFunctionField q k ≃+* drinfeldFunctionField q k') :
          drinfeldFunctionField q k →+* drinfeldFunctionField q k').comp
          ((hFunctionFieldAction q k h : drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
            drinfeldFunctionField q k →+* drinfeldFunctionField q k) =
        ((hFunctionFieldAction q k' h : drinfeldFunctionField q k' ≃ₐ[k'] drinfeldFunctionField q k') :
            drinfeldFunctionField q k' →+* drinfeldFunctionField q k').comp
          ((φ : drinfeldFunctionField q k ≃+* drinfeldFunctionField q k') :
            drinfeldFunctionField q k →+* drinfeldFunctionField q k') := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q k))
      ext a
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [hFunctionFieldAction_algebraMap, hφ, hφ, hFunctionFieldAction_algebraMap, hψ, DrinfeldPhi.coordEquiv_hAction]
    intro f
    exact RingHom.congr_fun key f

end S_DrinfeldCurve_exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv
end P2MW
export P2MW.S_DrinfeldCurve_exists_ringEquiv_drinfeldFunctionField_algebraMap_eq_and_hFunctionFieldAction_eq_of_algEquiv (solution)
