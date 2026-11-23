-- Prove2me | solution 1 for Formalism.L2.DIV.schur_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:29.335774+00:00
-- url     : https://prove2.me/submissions/c3fc6a0d-77e9-428d-914f-905cc2d8b4a2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
open Representation
namespace Formalism.L2.DIV
theorem _root_.solution {k V G : Type} [Field k] [IsAlgClosed k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] (T : V →ₗ[k] V)
    (hT : ∀ g v, T (ρ g v) = ρ g (T v)) : ∃ c : k, T = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).2
    (T.intertwiningMap_of_isIntertwiningMap ρ ρ hT)
  refine ⟨c, ?_⟩
  ext v
  have := congrArg (fun f : IntertwiningMap ρ ρ => f v) hc
  simpa using this.symm
end Formalism.L2.DIV
