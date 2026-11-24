-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:22:54.772869+00:00
-- url     : https://prove2.me/submissions/f0359061-fd6d-46e3-8e84-29b281c680ef

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNormalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BesselCapelliCommutation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.BesselCapelliCommutation
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) : psi k r z c 1 = 1 := by
  have heI : ∀ (a : Fin r) (h : (a : ℕ) + 1 < r), eI k r a ≠ eI k r ⟨a + 1, h⟩ := by
    intro a h he
    have := congrArg Fin.val he
    simp [eI] at this
  have hz' : ∀ a : Fin r, z (eI k r a) = 0 := fun a => hz _ (Or.inl (by simp [eI]))
  simp [psi, ell, Matrix.one_apply_ne, heI, hz']
end Formalism.FourierDecayAlt.P.BesselCapelliCommutation
