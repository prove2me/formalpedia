-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mp_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:48:58.970806+00:00
-- url     : https://prove2.me/submissions/98aaaecc-b688-448e-95e8-b11154f49dc8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution (β : ℂ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (σ : ι ≃ ι') :
    MeasurePreserving (fun v : ι' → ℂ => v ∘ σ) (muPi β ι') (muPi β ι) := by
  have h := measurePreserving_piCongrLeft (α := fun _ : ι => ℂ) (fun _ : ι => mu β) σ.symm
  have he : (fun v : ι' → ℂ => v ∘ σ) = MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) σ.symm := by
    funext v i
    obtain ⟨j, rfl⟩ := σ.symm.surjective i
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    simp
  rw [he]
  exact h
end Formalism.FourierDecayAlt.P.G5
