-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.quasiRefl_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:29.114747+00:00
-- url     : https://prove2.me/submissions/d7433d65-05fc-40df-a8e4-a4284ab7c583

import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix

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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (u : V) (a : K) (v : V) :
    quasiRefl h u a v = v - (a * h u v) • u := by
  first
  | simp [quasiRefl, smul_smul]
  | rw [quasiRefl, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, smul_smul]
end Formalism.HermitianLattices.Ext.L3.WA
