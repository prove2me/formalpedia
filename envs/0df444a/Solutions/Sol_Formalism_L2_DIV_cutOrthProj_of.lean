-- Prove2me | solution 1 for Formalism.L2.DIV.cutOrthProj_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.497162+00:00
-- url     : https://prove2.me/submissions/9adb80b3-dec1-4b3f-8538-eaa6ceca3a5c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_exists_mul_of_range_le
import Theorems.Thm_Formalism_DivisionValues_orthogonal_projection_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution (h1 : ImESpec) (h2 : GaMatHom) (h3 : GaMatAdj) : CutOrthProj := by
  intro K _ _ _ v0 hv S hpos G _ _ r hr a hidem hself
  obtain ⟨hinj, hrange⟩ := h1 K S.dim (S.gaMat r a)
  obtain ⟨-, hHdet, -, hOP, -⟩ := orthogonal_projection_exists K v0 hv S.dim _ S.H hpos (S.cutE r a) hinj
  have hOP' : IsOrthProj S.H (S.cutE r a) (S.cutPr r a) := hOP
  refine ⟨hOP', ?_⟩
  obtain ⟨-, hO⟩ := hOP'
  have hAA : S.gaMat r a * S.gaMat r a = S.gaMat r a := by rw [← (h2 K S G r).2, hidem]
  have hadj : (S.gaMat r a)ᴴ * S.H = S.H * S.gaMat r a := by rw [h3 K S G r hr a, hself]
  have hrE : LinearMap.range (S.cutE r a).mulVecLin = LinearMap.range (S.gaMat r a).mulVecLin := hrange
  obtain ⟨C, hC⟩ := exists_mul_of_range_le (A := S.cutE r a) (B := S.gaMat r a) hrE.ge
  obtain ⟨D, hD⟩ := exists_mul_of_range_le (A := S.gaMat r a) (B := S.cutE r a) hrE.le
  have hU : IsUnit S.H := (Matrix.isUnit_iff_isUnit_det S.H).mpr hHdet
  set E := S.cutE r a
  set Pr := S.cutPr r a
  set A := S.gaMat r a
  have hAE : A * E = E := by rw [hD, ← Matrix.mul_assoc, hAA]
  have hEH : Eᴴ * S.H = Eᴴ * S.H * (E * Pr) := by
    have h' := hO
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h'
    exact h'
  symm
  apply hU.mul_left_cancel
  calc S.H * A = Aᴴ * S.H := hadj.symm
    _ = Cᴴ * (Eᴴ * S.H) := by rw [hC, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Cᴴ * (Eᴴ * S.H * (E * Pr)) := by rw [← hEH]
    _ = Aᴴ * S.H * (E * Pr) := by rw [hC, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = S.H * (A * (E * Pr)) := by rw [hadj, Matrix.mul_assoc]
    _ = S.H * (E * Pr) := by rw [← Matrix.mul_assoc A, hAE]
end Formalism.L2.DIV
