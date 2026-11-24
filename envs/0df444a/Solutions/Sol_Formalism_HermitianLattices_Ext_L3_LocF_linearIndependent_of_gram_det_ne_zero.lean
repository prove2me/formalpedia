-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LocF.linearIndependent_of_gram_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:30.60011+00:00
-- url     : https://prove2.me/submissions/07802fc9-87bf-4143-99fd-cfe698954e4f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_gram_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ}
namespace Formalism.HermitianLattices.Ext.L3.LocF
theorem _root_.solution (x : Fin n → V)
    (hdet : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0) : LinearIndependent K x := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hG : (Matrix.of fun i j => h (x i) (x j)) *ᵥ c = 0 := by
    funext i
    rw [gram_mulVec h x c i, hc, map_zero, Pi.zero_apply]
  exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hG) i
end Formalism.HermitianLattices.Ext.L3.LocF
