-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HighestWeightPolynomials.indep_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:32:29.506797+00:00
-- url     : https://prove2.me/submissions/390d84df-fdcf-4174-b1a1-021313b554bd

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Bl_general_b_fact_second_ter_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HighestWeightPolynomials
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials
theorem _root_.solution {ι : Type*} (C : ℂ → Module.End ℂ V) (χ : ι → ℂ → ℂ) (hχ : Function.Injective χ)
    (p : ι → Submodule ℂ V) (hp : ∀ i v, v ∈ p i ↔ ∀ w, C w v = χ i w • v) : iSupIndep p := by
  first | exact Bl.general_b_fact_second_ter_form.goal1 .. | (apply Bl.general_b_fact_second_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_ter_form.goal1 <;> assumption)
end Formalism.FourierDecayAlt.P.HighestWeightPolynomials
