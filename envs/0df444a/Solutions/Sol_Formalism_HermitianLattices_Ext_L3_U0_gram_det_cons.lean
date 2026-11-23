-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.gram_det_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:33.185745+00:00
-- url     : https://prove2.me/submissions/78b6bbe7-f595-4fdd-991d-2db91e653bbf

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq
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
theorem _root_.solution (hs : h.IsSymm) {n : ℕ} (f : V) (x : Fin n → V) (hf : ∀ k, h f (x k) = 0) :
    (gram h (Fin.cons f x : Fin (n + 1) → V)).det = h f f * (gram h x).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h1 : ∀ i : Fin n, (-1 : K) ^ (i.succ : ℕ) * gram h (Fin.cons f x : Fin (n + 1) → V) i.succ 0 *
      ((gram h (Fin.cons f x : Fin (n + 1) → V)).submatrix i.succ.succAbove Fin.succ).det = 0 := by
    intro i
    have : gram h (Fin.cons f x : Fin (n + 1) → V) i.succ 0 = 0 := by
      simp only [gram, Matrix.of_apply, Fin.cons_succ, Fin.cons_zero]
      rw [← show star (h f (x i)) = h (x i) f from hs.eq f (x i), hf, star_zero]
    rw [this]
    ring
  rw [Finset.sum_eq_zero fun i _ => h1 i, add_zero]
  have h2 : (gram h (Fin.cons f x : Fin (n + 1) → V)).submatrix (Fin.succAbove 0) Fin.succ =
      gram h x := by
    ext i j
    simp [gram]
  rw [h2]
  simp [gram]
end Formalism.HermitianLattices.Ext.L3.U0
