-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:52:55.494331+00:00
-- url     : https://prove2.me/submissions/b3b720b4-1056-48a9-8002-4474d61dcf0b

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hA : A ≠ ⊥) :
    rkK (K := K) A ≠ 0 := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  unfold rkK
  intro h
  apply hA
  rw [Submodule.finrank_eq_zero] at h
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ Submodule.span K (A : Set V) := Submodule.subset_span hx
  rw [h] at hx'
  exact (Submodule.mem_bot _).mpr ((Submodule.mem_bot K).mp hx')
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
