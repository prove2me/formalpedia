-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.mem_sc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:21.490695+00:00
-- url     : https://prove2.me/submissions/5e1c4f65-a38a-492c-97e0-52085e877f68

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxPsiGood

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {K : Type} [Field K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] (a : K) (A : Submodule (𝓞 K) Z) (x : Z) :
    x ∈ sc a A ↔ ∃ y ∈ A, a • y = x := by
  unfold sc
  rw [Submodule.mem_map]
  rfl
end Formalism.EigenvalueLevelCeiling
