-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.decay.sum_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:49:49.458797+00:00
-- url     : https://prove2.me/submissions/40a3eed1-77f5-4f61-a29e-9f906fa1e979

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.JCx1.decay
theorem _root_.solution {Z X : Type} [DecidableEq Z] (P : Finset Z) (F : Z → ℂ) (Y : Finset X) (g : X → Z)
    (hg : ∀ h ∈ Y, g h ∈ P) :
    ∑ p : P, (∑ h ∈ Y, if g h = (p : Z) then (1 : ℂ) else 0) * F p = ∑ h ∈ Y, F (g h) := by
  simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.sum_eq_single (⟨g h, hg h hh⟩ : P)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro e
    exact hb (Subtype.ext e.symm)
  · intro hn
    exact absurd (Finset.mem_univ _) hn
end Formalism.FourierDecayAlt.P.JCx1.decay
