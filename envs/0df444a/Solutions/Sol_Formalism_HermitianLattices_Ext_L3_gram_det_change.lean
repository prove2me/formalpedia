-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.gram_det_change
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:25.742936+00:00
-- url     : https://prove2.me/submissions/5f11f120-add1-403e-88c8-71d3e0f02c22

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandG
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GramEqConjTransposeMul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_gram_eq_conjTranspose_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {n : ℕ}
    (h : V →ₗ⋆[K] V →ₗ[K] K) (b b' : Basis (Fin n) K V) :
    (gram h b).det = star (b'.det b) * b'.det b * (gram h b').det := by
  rw [gram_eq_conjTranspose_mul h b b', Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Basis.det_apply]
  ring
end Formalism.HermitianLattices.Ext.L3
