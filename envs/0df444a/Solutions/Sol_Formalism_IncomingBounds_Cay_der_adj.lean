-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.der_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:22.035154+00:00
-- url     : https://prove2.me/submissions/44afbba6-a659-4c34-ba27-e187c4ad0868

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_map_mul_der

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (D : Derivation R A A)
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (N : Matrix n n A) (a b : n) :
    N.det * D (adjugate N a b) =
      D N.det * adjugate N a b - ∑ p, ∑ q, adjugate N a p * D (N p q) * adjugate N q b := by
  have h1 : (adjugate N).map D * N + adjugate N * N.map D = D N.det • (1 : Matrix n n A) := by
    rw [← map_mul_der, adjugate_mul]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have h2 : N.det • (adjugate N).map D + adjugate N * (N.map D * adjugate N) =
      D N.det • adjugate N := by
    have h3 := congrArg (fun M => M * adjugate N) h1
    simp only [Matrix.add_mul, Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.one_mul] at h3
    exact h3
  have h4 := congrFun (congrFun h2 a) b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply] at h4
  have h5 : (adjugate N * (N.map D * adjugate N)) a b =
      ∑ p, ∑ q, adjugate N a p * D (N p q) * adjugate N q b := by
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, mul_assoc]
  rw [h5] at h4
  rw [eq_sub_iff_add_eq]
  exact h4
end Formalism.IncomingBounds.Cay
