-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.gram_det_dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:47.728327+00:00
-- url     : https://prove2.me/submissions/7b256710-1551-45c8-81eb-607310ca5d36

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mem
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
theorem _root_.solution (hπ : IsUnif S π) {n : ℕ} (x : Fin (n + 2) → V)
    (hx : ∀ i j, Dv S π (h (x i) (x j))) : Dv S π ((gram h x).det * π⁻¹) := by
  have e : gram h x = π • S.subtype.mapMatrix
      (Matrix.of fun i j => (⟨h (x i) (x j) * π⁻¹, hx i j⟩ : S)) := by
    ext i j
    have := hπ.ne
    simp only [gram, Matrix.of_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Subring.subtype_apply, smul_eq_mul]
    field_simp
  rw [e, Matrix.det_smul, ← RingHom.map_det, Fintype.card_fin]
  unfold Dv
  have e2 : ∀ d : K, π ^ (n + 2) * d * π⁻¹ * π⁻¹ = π ^ n * d := by
    intro d
    have := hπ.ne
    field_simp
    ring
  rw [e2]
  exact S.mul_mem (S.pow_mem hπ.mem n) (Subtype.mem _)
end Formalism.HermitianLattices.Ext.L3.U0
