-- Prove2me | solution 1 for FCP.Jacobian.etale_and_flat_aeval_of_isUnit_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:52:46.345567+00:00
-- url     : https://prove2.me/submissions/b4aee3f0-6e0d-4957-a3aa-66b3df23d0e7

import Mathlib
import Definitions.Def_FCP_Jacobian
import Theorems.Thm_Algebra_FormallySmooth_etale_aeval_of_basis_kaehlerDifferential

namespace FCP.Jacobian

open MvPolynomial KaehlerDifferential

/-- A unit polynomial Jacobian makes polynomial substitution étale. -/
theorem etale_aeval_of_isUnit_jacobian {k : Type} [CommRing k] {n : ℕ}
    (F : PolyMap k n) (hF : IsUnit (jacobian F).det) :
    (MvPolynomial.aeval (R := k) F).toRingHom.Etale := by
  classical
  let b := KaehlerDifferential.mvPolynomialBasis k (Fin n)
  let L := b.constr (MvPolynomial (Fin n) k)
    (fun i => KaehlerDifferential.D k (MvPolynomial (Fin n) k) (F i))
  have hmat : LinearMap.toMatrix b b L = (jacobian F).transpose := by
    ext i j : 1
    rw [LinearMap.toMatrix_apply]
    change b.repr ((b.constr (MvPolynomial (Fin n) k)
      (fun i => D k (MvPolynomial (Fin n) k) (F i))) (b j)) i = _
    rw [Module.Basis.constr_basis]
    exact KaehlerDifferential.mvPolynomialBasis_repr_apply k (Fin n) (F j) i
  have hdet : IsUnit L.det := by
    rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_transpose]
    exact hF
  have hbij : Function.Bijective L :=
    (Module.End.isUnit_iff L).mp ((LinearMap.isUnit_iff_isUnit_det L).mpr hdet)
  let e := LinearEquiv.ofBijective L hbij
  exact Algebra.FormallySmooth.etale_aeval_of_basis_kaehlerDifferential
    F (b.map e) (fun i => by simp [e, L])

/-- Flatness is for the algebra structure induced by the substitution map. -/
theorem flat_aeval_of_isUnit_jacobian {k : Type} [CommRing k] {n : ℕ}
    (F : PolyMap k n) (hF : IsUnit (jacobian F).det) :
    (MvPolynomial.aeval (R := k) F).toRingHom.Flat :=
  (RingHom.Etale.iff_flat_and_formallyUnramified.mp
    (etale_aeval_of_isUnit_jacobian F hF)).1

end FCP.Jacobian

theorem solution {k : Type} [CommRing k] {n : ℕ}
    (F : FCP.Jacobian.PolyMap k n) (hF : IsUnit (FCP.Jacobian.jacobian F).det) :
    (MvPolynomial.aeval (R := k) F).toRingHom.Etale ∧ (MvPolynomial.aeval (R := k) F).toRingHom.Flat :=
  ⟨FCP.Jacobian.etale_aeval_of_isUnit_jacobian F hF,
    FCP.Jacobian.flat_aeval_of_isUnit_jacobian F hF⟩
