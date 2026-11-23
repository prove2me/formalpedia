-- Prove2me | solution 1 for Formalism.L2.Indef.IndefLink2.toR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:07.239883+00:00
-- url     : https://prove2.me/submissions/a0e6a5f9-5fc6-4aa5-8e10-c7a4b3b61ecb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef
namespace IndefLink2
theorem _root_.solution {Ix : ℝ → Type} {F : ∀ x, Ix x → IndefFace2} {CH : ℝ}
    {Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop}
    (h : IndefLink2 Ix F CH Q) : IndefLinkR Ix F CH Q := by
  obtain ⟨C, x0, hC⟩ := h
  exact ⟨C, x0, fun x hx i => by
    obtain ⟨P, hP⟩ := hC x hx i
    exact ⟨P.toR, hP⟩⟩
end IndefLink2
end Formalism.L2.Indef
