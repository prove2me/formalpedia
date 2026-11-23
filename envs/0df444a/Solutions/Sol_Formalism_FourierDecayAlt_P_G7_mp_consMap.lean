-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.mp_consMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:19.239415+00:00
-- url     : https://prove2.me/submissions/41599709-e6a7-42a1-ab62-0c8a767d5fe2

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (β : ℂ) (m : ℕ) : MeasurePreserving (consMap m) (muRed β m) (muBlock β (m + 1)) := by
  have h1 := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => mu β) 0).symm
  have h2 := (measurePreserving_prodAssoc (mu β) (muPi β (Fin m))
    ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1))))).symm
  have h3 := (h1.prod (MeasurePreserving.id ((muPi β (UT (m + 1))).prod (muPi β (Fin (m + 1)))))).comp h2
  have e : consMap m = (Prod.map (⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0).symm) id) ∘
      ⇑(MeasurableEquiv.prodAssoc : ((ℂ × (Fin m → ℂ)) × ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))) ≃ᵐ _).symm := by
    funext q
    simp only [consMap, Function.comp, Prod.map]
    refine Prod.ext ?_ rfl
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodAssoc]
  rw [e]
  exact h3
end Formalism.FourierDecayAlt.P.G7
