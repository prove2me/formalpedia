-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BallB.gram_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:44:48.458806+00:00
-- url     : https://prove2.me/submissions/bc91e1c6-fff1-4be0-ab5e-aaca22e402d4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
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
variable {K V ι : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.HermitianLattices.Ext.L3.BallB
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis ι K V) (u w : ι → V) :
    (Matrix.of fun i j => h (u i) (w j)).det =
      star (b.det u) * (Matrix.of fun i j => h (b i) (b j)).det * b.det w := by
  have hm : (Matrix.of fun i j => h (u i) (w j)) =
      (b.toMatrix u).conjTranspose * (Matrix.of fun i j => h (b i) (b j)) * b.toMatrix w := by
    ext i j
    rw [Matrix.of_apply]
    conv_lhs => rw [← b.sum_repr (u i), ← b.sum_repr (w j)]
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Basis.toMatrix_apply, Matrix.of_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Basis.det_apply,
    Basis.det_apply]
end Formalism.HermitianLattices.Ext.L3.BallB
