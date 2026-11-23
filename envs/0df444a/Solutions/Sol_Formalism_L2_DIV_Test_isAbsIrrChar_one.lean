-- Prove2me | solution 1 for Formalism.L2.DIV.Test.isAbsIrrChar_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:17.119827+00:00
-- url     : https://prove2.me/submissions/b6eaf77b-c961-4d51-a946-97ba3661dbba

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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
namespace Formalism.L2.DIV.Test
theorem _root_.solution : IsAbsIrrChar (fun _ : G => (1 : K)) := by
  refine ⟨1, 1, ?_, ?_⟩
  · have hs : IsSimpleOrder (Submodule (AlgebraicClosure K) (Fin 1 → AlgebraicClosure K)) := by
      have : IsSimpleModule (AlgebraicClosure K) (Fin 1 → AlgebraicClosure K) :=
        isSimpleModule_iff_finrank_eq_one.mpr (by simp)
      exact this.1
    have : Nontrivial (Subrepresentation (1 : Representation (AlgebraicClosure K) G
        (Fin 1 → AlgebraicClosure K))) :=
      ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
    refine ⟨fun σ => ?_⟩
    rcases hs.eq_bot_or_eq_top σ.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  · intro t
    simp [Representation.character]
end Formalism.L2.DIV.Test
