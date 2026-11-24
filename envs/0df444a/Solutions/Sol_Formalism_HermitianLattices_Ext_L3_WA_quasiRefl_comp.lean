-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.quasiRefl_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:39.541719+00:00
-- url     : https://prove2.me/submissions/f8f5871f-1dea-4aea-8743-87cb95ac3eaa

import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_quasiRefl_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.WA
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) {a b : K}
    (hab : a + b = a * b * h u u) : quasiRefl h u a ∘ₗ quasiRefl h u b = LinearMap.id := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [quasiRefl_apply, quasiRefl_apply]
  simp only [map_sub, map_smul, map_smulₛₗ, RingHom.id_apply, smul_eq_mul]
  rw [sub_sub, ← add_smul, sub_eq_self, smul_eq_zero]
  left
  linear_combination (h u v) * hab
end Formalism.HermitianLattices.Ext.L3.WA
