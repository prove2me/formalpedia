-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.quasiRefl_isom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:39.868465+00:00
-- url     : https://prove2.me/submissions/8d7bb260-3b84-4443-bc21-63427b07b250

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
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {a : K}
    (ha : a + star a = a * star a * h u u) (v w : V) :
    h (quasiRefl h u a v) (quasiRefl h u a w) = h v w := by
  have hsym : star (h u v) = h v u := by
    have := hs.eq u v
    simpa [starRingEnd_apply] using this
  rw [quasiRefl_apply, quasiRefl_apply]
  simp only [map_sub, map_smulₛₗ, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_mul, hsym, RingHom.id_apply]
  linear_combination (-(h v u * h u w)) * ha
end Formalism.HermitianLattices.Ext.L3.WA
