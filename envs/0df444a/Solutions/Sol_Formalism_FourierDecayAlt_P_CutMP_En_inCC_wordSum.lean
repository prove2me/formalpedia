-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.En.inCC_wordSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:51:18.636121+00:00
-- url     : https://prove2.me/submissions/4be95fb3-c78c-434e-8921-268e140922dc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCVInCC
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_InCC_Rw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sInCC_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En
namespace Formalism.FourierDecayAlt.P.CutMP.En
theorem _root_.solution {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m n : ℕ}
    {F : B.Mat k r → E} (hF : B.InCC A (m + n) F) :
    ∀ L : List (ℂ × List (B.Mat k r)), (∀ cw ∈ L, (∀ X ∈ cw.2, B.unitLie k r X) ∧ cw.2.length ≤ n) →
      B.InCC A m (fun g => (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum)
  | [], _ => ⟨0, by simpa using (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_zero (k := k) (r := r) (E := E) (A := A) (m := m))⟩
  | cw :: L, hL => by
    have h1 : B.InCC A m (fun g => cw.1 • B.Rw cw.2 F g) := by
      have hw := hL cw (by simp)
      have h0 : B.InCC A (m + cw.2.length) F :=
        Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono le_rfl (by omega) hF
      obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw (fun X hX => (hw.1 X hX).1) h0
      exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul cw.1 hc⟩
    have h2 := solution hF L (fun cw' hcw' => hL cw' (by simp [hcw']))
    obtain ⟨c₁, hc₁⟩ := h1
    obtain ⟨c₂, hc₂⟩ := h2
    refine ⟨c₁ + c₂, ?_⟩
    simpa [List.map_cons, List.sum_cons] using Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc₁ hc₂
end Formalism.FourierDecayAlt.P.CutMP.En
