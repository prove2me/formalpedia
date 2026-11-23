-- Prove2me | solution 1 for Formalism.L2.DIV.CSD.star_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:40.148795+00:00
-- url     : https://prove2.me/submissions/4e6a2012-093d-4897-8ef3-05fc29590903

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge

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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
namespace Formalism.L2.DIV.CSD
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {z : K}
    (hz : z ∈ (1 : Submodule (𝓞 K) K)) : star z ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hz
  exact Submodule.mem_one.mpr ⟨cO K a, rfl⟩
end Formalism.L2.DIV.CSD
