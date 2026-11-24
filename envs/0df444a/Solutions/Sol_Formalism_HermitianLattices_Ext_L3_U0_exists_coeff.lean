-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.exists_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:46.471269+00:00
-- url     : https://prove2.me/submissions/468fc53d-e1f8-4c73-8a0d-680c90b3b9fc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution {n : ℕ} {y : Fin n → V} {v : V} (hv : v ∈ spanS S y) :
    ∃ c : Fin n → S, v = ∑ j, (c j : K) • y j := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hv
  exact ⟨c, hc.symm⟩
end Formalism.HermitianLattices.Ext.L3.U0
