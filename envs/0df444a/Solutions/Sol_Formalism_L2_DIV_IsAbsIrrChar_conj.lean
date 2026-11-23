-- Prove2me | solution 1 for Formalism.L2.DIV.IsAbsIrrChar.conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:08.902629+00:00
-- url     : https://prove2.me/submissions/17515737-4e1b-4f52-9321-9e2f5a6b650c

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
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
namespace IsAbsIrrChar
theorem _root_.solution {χ : G → K} (h : IsAbsIrrChar χ) (s t : G) : χ (s * t * s⁻¹) = χ t := by
  obtain ⟨n, ρ, -, hχ⟩ := h
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [← hχ, ← hχ]
  show LinearMap.trace _ _ (ρ (s * t * s⁻¹)) = LinearMap.trace _ _ (ρ t)
  rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ, ← map_mul ρ, inv_mul_cancel,
    one_mul]
end IsAbsIrrChar
end Formalism.L2.DIV
