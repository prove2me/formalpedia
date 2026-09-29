-- Prove2me | solution 1 for DrinfeldCurve.isIntegral_of_apply_x_eq_pow_of_apply_y_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/758f4bbc-b265-59f5-be37-3c8de9a8b4f0

import Mathlib
import Definitions.Def_DrinfeldCurve_FunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_isIntegral_of_apply_x_eq_pow_of_apply_y_eq_pow

set_option autoImplicit false

namespace DrinfeldCurve
p2m_export "DrinfeldCurve" "drinfeldFunctionField CoordRing mk_surjective x y"
namespace IntAux
p2m_open "DrinfeldCurve"

open MvPolynomial

variable (q : ℕ) (k : Type) [Field k] [IsDomain (CoordRing q k)]

private theorem _root_.DrinfeldCurve.IntAux.algebraMap_mem (E : IntermediateField k (drinfeldFunctionField q k))
    (hx : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ∈ E)
    (hy : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ∈ E) (c : CoordRing q k) :
    algebraMap (CoordRing q k) (drinfeldFunctionField q k) c ∈ E := by
  obtain ⟨P, rfl⟩ := mk_surjective q k c
  induction P using MvPolynomial.induction_on with
  | C a =>
    change algebraMap (CoordRing q k) (drinfeldFunctionField q k) (algebraMap k (CoordRing q k) a) ∈ E
    rw [← IsScalarTower.algebraMap_apply]
    exact E.algebraMap_mem a
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact E.add_mem h₁ h₂
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine E.mul_mem hp ?_
    fin_cases i
    · exact hx
    · exact hy

p2m_export "DrinfeldCurve.IntAux" "algebraMap_mem"

theorem eq_top_of_mem (E : IntermediateField k (drinfeldFunctionField q k))
    (hx : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ∈ E)
    (hy : algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ∈ E) : E = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := CoordRing q k) z
  exact E.div_mem (algebraMap_mem q k E hx hy a) (algebraMap_mem q k E hx hy b)

end DrinfeldCurve.IntAux

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_isIntegral_of_apply_x_eq_pow_of_apply_y_eq_pow.DrinfeldCurve in

theorem solution (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsDomain (CoordRing q k)]
    (φ : drinfeldFunctionField q k →ₐ[k] drinfeldFunctionField q k) (n : ℕ)
    (hφx : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) ^ q ^ n)
    (hφy : φ (algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k)) =
      algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) ^ q ^ n) :
    φ.toRingHom.IsIntegral := by
  have hm : q ^ n ≠ 0 := pow_ne_zero _ (Fact.out : q.Prime).ne_zero
  set R : IntermediateField k (drinfeldFunctionField q k) := φ.fieldRange with hR

  have hint : ∀ z : drinfeldFunctionField q k, φ z = z ^ q ^ n → IsIntegral R z := by
    intro z hz
    refine ⟨Polynomial.X ^ q ^ n - Polynomial.C (⟨φ z, ⟨z, rfl⟩⟩ : R), Polynomial.monic_X_pow_sub_C _ hm, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero, ← hz]
    rfl
  set xF := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (x q k) with hxF
  set yF := algebraMap (CoordRing q k) (drinfeldFunctionField q k) (y q k) with hyF

  set E : IntermediateField R (drinfeldFunctionField q k) := IntermediateField.adjoin R {xF, yF} with hE
  haveI : FiniteDimensional R E := by
    apply IntermediateField.finiteDimensional_adjoin
    intro z hz
    rcases hz with rfl | rfl
    · exact hint _ hφx
    · exact hint _ hφy
  have hEtop : E = ⊤ := by
    have h := DrinfeldCurve.IntAux.eq_top_of_mem q k (E.restrictScalars k)
      (IntermediateField.subset_adjoin R _ (Set.mem_insert _ _))
      (IntermediateField.subset_adjoin R _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ E.restrictScalars k := by rw [h]; trivial
    exact hz
  haveI : Module.Finite R (drinfeldFunctionField q k) :=
    Module.Finite.equiv ((IntermediateField.equivOfEq hEtop).trans IntermediateField.topEquiv).toLinearEquiv

  set g : drinfeldFunctionField q k →+* R := φ.toRingHom.codRestrict R (fun z => ⟨z, rfl⟩) with hg
  have hgs : Function.Surjective g := by
    rintro ⟨w, z, rfl⟩
    exact ⟨z, rfl⟩
  have hcomp : φ.toRingHom = (algebraMap R (drinfeldFunctionField q k)).comp g := RingHom.ext fun z => rfl
  rw [hcomp]
  exact (RingHom.isIntegral_of_surjective g hgs).trans _ _ (algebraMap_isIntegral_iff.mpr (Algebra.IsIntegral.of_finite R (drinfeldFunctionField q k)))

end S_DrinfeldCurve_isIntegral_of_apply_x_eq_pow_of_apply_y_eq_pow
end P2MW
export P2MW.S_DrinfeldCurve_isIntegral_of_apply_x_eq_pow_of_apply_y_eq_pow (solution)
