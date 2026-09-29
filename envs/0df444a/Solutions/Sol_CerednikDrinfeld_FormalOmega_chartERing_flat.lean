-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.chartERing.flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/75113624-8805-56cc-85f2-0e57a1f5e8be

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_flat

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega
open Polynomial

noncomputable section

namespace ChartFlat

variable (R : Type) [CommRing R] (π : R)

def g : (R[X])[X] := X ^ 2 + (C (X : R[X]) * X - C (C π))

theorem g_monic : (g R π).Monic := by
  unfold g
  refine monic_X_pow_add ?_
  refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
  · exact (degree_C_mul_X_le _).trans_lt (by exact_mod_cast one_lt_two)
  · exact degree_C_le.trans_lt (by exact_mod_cast two_pos)

abbrev B : Type := AdjoinRoot (g R π)

scoped instance : Module.Free R[X] (B R π) := (g_monic R π).free_adjoinRoot

scoped instance : Module.Flat R (B R π) := Module.Flat.trans R R[X] (B R π)

abbrev ξq : edgeQuot R π := edgeQuot.mk R π (MvPolynomial.X 0)
abbrev ηq : edgeQuot R π := edgeQuot.mk R π (MvPolynomial.X 1)

theorem ξq_mul_ηq : ξq R π * ηq R π = algebraMap R (edgeQuot R π) π := by
  have h := edgeQuot.mk_edgeRel R π
  unfold edgeRel at h
  rw [map_sub, map_mul, sub_eq_zero] at h
  rw [h]; exact (edgeQuot.mk R π).commutes π

def gen (i : Fin 2) : B R π := if i = 0 then AdjoinRoot.root (g R π) else AdjoinRoot.root (g R π) + AdjoinRoot.of (g R π) X

theorem gen_zero : gen R π 0 = AdjoinRoot.root (g R π) := rfl
theorem gen_one : gen R π 1 = AdjoinRoot.root (g R π) + AdjoinRoot.of (g R π) X := rfl

theorem root_rel : AdjoinRoot.root (g R π) * (AdjoinRoot.root (g R π) + AdjoinRoot.of (g R π) X) =
    algebraMap R (B R π) π := by
  have h : Polynomial.aeval (AdjoinRoot.root (g R π)) (X ^ 2 + (C (X : R[X]) * X - C (C π)) : (R[X])[X]) = 0 :=
    (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  rw [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, aeval_C] at h
  rw [IsScalarTower.algebraMap_apply R R[X] (B R π), algebraMap_eq, ← AdjoinRoot.algebraMap_eq]
  linear_combination h

def φ : edgeQuot R π →ₐ[R] B R π :=
  Ideal.Quotient.liftₐ (Ideal.span {edgeRel R π}) (MvPolynomial.aeval (gen R π))
    (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      rw [map_mul]
      refine mul_eq_zero_of_left ?_ _
      show MvPolynomial.aeval (gen R π) (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π) = 0
      rw [map_sub, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_C, gen_zero, gen_one,
        root_rel, sub_self])

theorem φ_mk (p : MvPolynomial (Fin 2) R) : φ R π (edgeQuot.mk R π p) = MvPolynomial.aeval (gen R π) p := rfl

def ψ : B R π →ₐ[R] edgeQuot R π :=
  AdjoinRoot.liftAlgHom (g R π) (Polynomial.aeval (R := R) (ηq R π - ξq R π)) (ξq R π)
    (by
      unfold g
      rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
      simp only [AlgHom.coe_toRingHom, aeval_X, aeval_C]
      rw [← ξq_mul_ηq]; ring)

theorem ψ_root : ψ R π (AdjoinRoot.root (g R π)) = ξq R π := AdjoinRoot.liftAlgHom_root _ _ _ _

theorem ψ_of (p : R[X]) : ψ R π (AdjoinRoot.of (g R π) p) = Polynomial.aeval (R := R) (ηq R π - ξq R π) p :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ p

theorem ψ_φ (x : edgeQuot R π) : ψ R π (φ R π x) = x := by
  suffices h : (ψ R π).comp (φ R π) = AlgHom.id R (edgeQuot R π) from AlgHom.congr_fun h x
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · show ψ R π (φ R π (edgeQuot.mk R π (MvPolynomial.X 0))) = edgeQuot.mk R π (MvPolynomial.X 0)
    rw [φ_mk, MvPolynomial.aeval_X, gen_zero, ψ_root]
  · show ψ R π (φ R π (edgeQuot.mk R π (MvPolynomial.X 1))) = edgeQuot.mk R π (MvPolynomial.X 1)
    rw [φ_mk, MvPolynomial.aeval_X, gen_one, map_add, ψ_root, ψ_of, aeval_X]; ring

theorem φ_ψ (y : B R π) : φ R π (ψ R π y) = y := by
  have hroot : φ R π (ψ R π (AdjoinRoot.root (g R π))) = AdjoinRoot.root (g R π) := by
    rw [ψ_root]; show φ R π (edgeQuot.mk R π (MvPolynomial.X 0)) = _; rw [φ_mk, MvPolynomial.aeval_X, gen_zero]
  have hX : φ R π (ψ R π (AdjoinRoot.of (g R π) X)) = AdjoinRoot.of (g R π) X := by
    rw [ψ_of, aeval_X, map_sub]
    show φ R π (edgeQuot.mk R π (MvPolynomial.X 1)) - φ R π (edgeQuot.mk R π (MvPolynomial.X 0)) = _
    rw [φ_mk, φ_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, gen_zero, gen_one]; ring

  suffices h : ((φ R π).comp (ψ R π)).toRingHom.comp (AdjoinRoot.mk (g R π)) =
      (AlgHom.id R (B R π)).toRingHom.comp (AdjoinRoot.mk (g R π)) by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    exact RingHom.congr_fun h p
  apply Polynomial.ringHom_ext
  · intro p
    show φ R π (ψ R π (AdjoinRoot.mk (g R π) (C p))) = AdjoinRoot.mk (g R π) (C p)
    rw [AdjoinRoot.mk_C]

    suffices h' : ((φ R π).comp (ψ R π)).toRingHom.comp (AdjoinRoot.of (g R π)) = AdjoinRoot.of (g R π) from
      RingHom.congr_fun h' p
    apply Polynomial.ringHom_ext
    · intro r
      show φ R π (ψ R π (AdjoinRoot.of (g R π) (C r))) = AdjoinRoot.of (g R π) (C r)
      rw [← algebraMap_eq, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply R R[X] (B R π),
        AlgHom.commutes, AlgHom.commutes]
    · exact hX
  · show φ R π (ψ R π (AdjoinRoot.mk (g R π) X)) = AdjoinRoot.mk (g R π) X
    rw [AdjoinRoot.mk_X]; exact hroot

def e : edgeQuot R π ≃ₗ[R] B R π :=
  LinearEquiv.ofBijective (φ R π).toLinearMap
    ⟨Function.LeftInverse.injective (g := ψ R π) (ψ_φ R π), Function.RightInverse.surjective (g := ψ R π) (φ_ψ R π)⟩

theorem flat_edgeQuot : Module.Flat R (edgeQuot R π) := Module.Flat.of_linearEquiv (e R π)

end ChartFlat
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_flat.ChartFlat"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_flat.ChartFlat"

theorem solution
    (R : Type) [CommRing R] (π : R) (q : ℕ) :
    Module.Flat R (chartERing R π q) := by
  have h1 : Module.Flat R (edgeQuot R π) := ChartFlat.flat_edgeQuot R π
  have h2 : Module.Flat (edgeQuot R π) (chartERing R π q) := IsLocalization.flat _ (Submonoid.powers (edgeQuot.discr R π q))
  exact @Module.Flat.trans R (edgeQuot R π) (chartERing R π q) _ _ _ _ _ _ _ h1 h2

end S_CerednikDrinfeld_FormalOmega_chartERing_flat
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_flat (solution)
