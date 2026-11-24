-- Prove2me | solution 1 for Formalism.L2.Indef.IndefLink2.forget
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:18:31.685045+00:00
-- url     : https://prove2.me/submissions/053b4a23-c450-47bd-8525-a1d192ec44e8

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
    (h : IndefLink2 Ix F CH Q) : IndefLink Ix (fun x i => (F x i).toIndefFace) CH Q := by
  obtain ⟨C, x0, hC⟩ := h
  exact ⟨C, x0, fun x hx i => by
    obtain ⟨P, hP⟩ := hC x hx i
    exact ⟨P.forget, hP⟩⟩
end IndefLink2
end Formalism.L2.Indef
