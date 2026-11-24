-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.form_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:11.724092+00:00
-- url     : https://prove2.me/submissions/e785320b-7235-4dfb-939f-d076588dc085

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNeZeroOfIsLattice
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
open NumberField Module nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution (h : K →ₗ⋆[K] K →ₗ[K] K) (x y : K) : h x y = star x * y * h 1 1 := by
  rw [show h x y = h (x • (1 : K)) (y • (1 : K)) by simp only [smul_eq_mul, mul_one],
    LinearMap.map_smulₛₗ₂, LinearMap.map_smul, starRingEnd_apply]
  simp only [smul_eq_mul]
  ring
end Formalism.HermitianLattices.Ext.L3.RankOne
