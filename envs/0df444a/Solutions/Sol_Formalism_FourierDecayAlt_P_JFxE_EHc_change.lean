-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.EHc_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:25:16.774242+00:00
-- url     : https://prove2.me/submissions/0b90fa96-daf3-4af5-8ce9-5da8ebf5284f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EH_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_EHc_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_conj_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Psi_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rep1
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Psi_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {y : Mat k r} (hy : y ∈ GV k r) (c d : Fin (2 * r + k + 1)) (φ : Mat k r → E)
    (hφ : CkOn 1 (GV k r) φ) : ∀ g ∈ GV k r,
      EHc k r y c d φ g = ∑ a, ∑ b, (y⁻¹ a c * y d b) • Q.EH k r a b φ g := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, hff⟩ := rep1 hφ hg
  rw [EHc_psi hy hU hgU hg hF hff c d, conj_single, Psi_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Psi_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Psi_smul, EH_psi hU hgU hg hF hff a b]
end Formalism.FourierDecayAlt.P.JFxE
