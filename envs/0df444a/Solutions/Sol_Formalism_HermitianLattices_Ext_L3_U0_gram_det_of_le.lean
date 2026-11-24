-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.gram_det_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:04.216794+00:00
-- url     : https://prove2.me/submissions/4b04cbbd-aa62-4a61-a35f-91f469b6682d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_coeff
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hS : IsHermSemilocal S) {n : ℕ} {x y : Fin n → V}
    (hxy : ∀ i, x i ∈ spanS S y) : ∃ c ∈ S, (gram h x).det = c * (gram h y).det := by
  choose T hT using fun i => exists_coeff (hxy i)
  have e : gram h x = ((S.subtype.mapMatrix (Matrix.of T)).map star) * gram h y *
      (S.subtype.mapMatrix (Matrix.of T)).transpose := by
    ext i l
    simp only [gram, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      RingHom.mapMatrix_apply, Subring.subtype_apply]
    conv_lhs => rw [hT i, hT l]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : ((S.subtype.mapMatrix (Matrix.of T)).map star).det =
      star (S.subtype.mapMatrix (Matrix.of T)).det := by
    have := (starRingEnd K).map_det (S.subtype.mapMatrix (Matrix.of T))
    rw [starRingEnd_apply] at this
    rw [this]
    rfl
  have e3 : (S.subtype.mapMatrix (Matrix.of T)).det ∈ S := by
    rw [← RingHom.map_det]
    exact (Matrix.of T).det.2
  refine ⟨star (S.subtype.mapMatrix (Matrix.of T)).det * (S.subtype.mapMatrix (Matrix.of T)).det,
    S.mul_mem (hS.star_mem _ e3) e3, ?_⟩
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e2]
  ring
end Formalism.HermitianLattices.Ext.L3.U0
