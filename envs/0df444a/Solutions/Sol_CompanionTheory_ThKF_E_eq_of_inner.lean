-- Prove2me | solution 1 for CompanionTheory.ThKF.E.eq_of_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:15.159617+00:00
-- url     : https://prove2.me/submissions/6741e5dd-a83d-499c-bb23-70719ae8b28a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKF CompanionTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKF.E
theorem _root_.solution {u v : Sch l} (h : ∀ φ : Sch l, inner ℂ (φ.toLp 2 volume) (u.toLp 2 volume) =
    inner ℂ (φ.toLp 2 volume) (v.toLp 2 volume)) : u = v := by
  apply injective_toLp 2 volume
  have := h (u - v)
  rw [← sub_eq_zero, ← inner_sub_right, ← toLpCLM_apply (𝕜 := ℂ), map_sub] at this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)
end CompanionTheory.ThKF.E
