-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.det_update_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:27.837604+00:00
-- url     : https://prove2.me/submissions/92962109-360d-45f2-92e3-67041a173bfc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
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
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (x : ι → V)
    (a : ι → K) (i : ι) : b.det (Function.update x i (∑ k, a k • x k)) = a i * b.det x := by
  rw [Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose,
    ← Matrix.det_transpose (b.toMatrix x)]
  have e : Matrix.transpose (b.toMatrix (Function.update x i (∑ k, a k • x k))) =
      (Matrix.transpose (b.toMatrix x)).updateRow i (∑ k, a k • Matrix.transpose (b.toMatrix x) k) := by
    ext r s
    rcases eq_or_ne r i with rfl | hr
    · simp [Basis.toMatrix_apply, Matrix.updateRow_self, Finset.sum_apply, map_sum, map_smul]
    · simp [Basis.toMatrix_apply, Matrix.updateRow_ne hr, Function.update_apply, hr]
  rw [e, Matrix.det_updateRow_sum, smul_eq_mul]
end Formalism.HermitianLattices.Ext.L3.BallB
