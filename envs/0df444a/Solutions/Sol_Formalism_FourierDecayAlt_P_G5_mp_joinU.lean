-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.mp_joinU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:28.989807+00:00
-- url     : https://prove2.me/submissions/64fa4450-b495-402f-a6c2-65f8934c55b2

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_comp_equiv

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
theorem _root_.solution (β : ℂ) (n : ℕ) :
    MeasurePreserving (joinU : (UT n → ℂ) × (Fin n → ℂ) → UT (n + 1) → ℂ)
      ((muPi β (UT n)).prod (muPi β (Fin n))) (muPi β (UT (n + 1))) := by
  have h1 := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : UT n ⊕ Fin n => ℂ) (fun _ => mu β)
  have h2 := mp_comp_equiv β (idxEquiv n).symm
  have h3 := h2.comp h1
  have he : (joinU : (UT n → ℂ) × (Fin n → ℂ) → UT (n + 1) → ℂ) =
      (fun v : UT n ⊕ Fin n → ℂ => v ∘ (idxEquiv n).symm) ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : UT n ⊕ Fin n => ℂ)).symm := by
    funext q p
    simp only [joinU, Function.comp]
    rcases (idxEquiv n).symm p with s | s <;> rfl
  rw [he]
  exact h3
end Formalism.FourierDecayAlt.P.G5
