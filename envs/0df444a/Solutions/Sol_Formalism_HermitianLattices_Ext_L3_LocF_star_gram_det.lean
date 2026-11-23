-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.star_gram_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:01.388424+00:00
-- url     : https://prove2.me/submissions/bbaf77a0-0015-4c1e-b16d-163ae691a958

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
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
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution (hs : h.IsSymm) (x : Fin n → V) :
    star (Matrix.of fun i j => h (x i) (x j)).det = (Matrix.of fun i j => h (x i) (x j)).det := by
  rw [← Matrix.det_conjTranspose]
  congr 1
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  first
  | exact hs.eq (x j) (x i)
  | exact hs (x j) (x i)
end Formalism.HermitianLattices.Ext.L3.LocF
