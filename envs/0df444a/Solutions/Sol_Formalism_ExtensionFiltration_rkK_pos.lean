-- Prove2me | solution 1 for Formalism.ExtensionFiltration.rkK_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:01.163332+00:00
-- url     : https://prove2.me/submissions/9c6f185a-5a4f-4b1d-ad6e-a2eef678a126

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_DescentCut
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentCut

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
namespace Formalism.ExtensionFiltration
theorem _root_.solution {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] (b : Basis ι K V)
    (A : Submodule (𝓞 K) V) (hA : A ≠ ⊥) : 0 < rkK (K := K) A := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  unfold rkK
  rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  intro h
  apply hA
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ Submodule.span K (A : Set V) := Submodule.subset_span hx
  rw [h, Submodule.mem_bot] at hx'
  simp [hx']
end Formalism.ExtensionFiltration
