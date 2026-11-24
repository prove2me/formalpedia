-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SettingConstruction.sum_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:27:52.161503+00:00
-- url     : https://prove2.me/submissions/e1150094-798b-4017-9d55-db23817a8b02

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r : ℕ)
namespace Formalism.FourierDecayAlt.P.SettingConstruction
theorem _root_.solution (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by
  symm
  refine Fintype.sum_of_injective (wI k r) ?_ (fun j => f (wI k r j)) f ?_ (fun _ => rfl)
  · intro a b hab
    have := congrArg Fin.val hab
    simp only [wI] at this
    ext; omega
  · intro c hc
    apply hf
    by_contra hcon
    push_neg at hcon
    exact hc ⟨⟨c.val - r, by omega⟩, by ext; simp only [wI]; omega⟩
end Formalism.FourierDecayAlt.P.SettingConstruction
