-- Prove2me | solution 1 for Formalism.L2.DIV.subHasRat_of_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:21.581362+00:00
-- url     : https://prove2.me/submissions/8dcf5d20-392b-4d85-b4a7-1e9d3e2e01bf

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
variable {K : Type} [Field K] [StarRing K] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (Z : Submodule K (Fin n → K)) (T : Set (Fin n → K))
    (hT : Submodule.span K T = Z) (hrat : ∀ v ∈ T, ∀ i, v i ∈ cmMax K) : SubHasRatBasis Z := by
  obtain ⟨b, hbT, hspan, hli⟩ := exists_linearIndependent K T
  have hZ : Submodule.span K (Set.range ((↑) : b → Fin n → K)) = Z := by
    rw [Subtype.range_coe, hspan, hT]
  refine ⟨((Basis.span hli).map (LinearEquiv.ofEq _ _ hZ)).reindex
      (((Basis.span hli).map (LinearEquiv.ofEq _ _ hZ)).indexEquiv (Module.finBasis K Z)), fun j i => ?_⟩
  rw [Basis.reindex_apply, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  exact hrat _ (hbT (Subtype.mem _)) i
end Formalism.L2.DIV
