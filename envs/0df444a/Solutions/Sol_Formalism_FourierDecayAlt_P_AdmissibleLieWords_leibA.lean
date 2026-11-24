-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.leibA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:47:54.530349+00:00
-- url     : https://prove2.me/submissions/3818be4d-3ac9-4567-89bb-279dd911925d

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dif
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_cdx
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dw_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dx_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_cd_app
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_dif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
section app
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
private lemma dw_append_singleton' {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (w : List (Bool × Mat k r))
    (x : Bool × Mat k r) (f : Mat k r → E') : Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl
end app
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ (a : Mat k r → (F →L[ℝ] E)) (b : Mat k r → F), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      (∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g (b g)) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb h
    have h0 := h [] [] ⟨List.Sublist.slnil, List.Sublist.slnil, List.Perm.nil⟩
    simp only [Dw, List.foldr_nil, List.length_nil, pow_zero, one_mul] at h0 ⊢
    exact (ContinuousLinearMap.le_opNorm _ _).trans h0
  | append_singleton w x ih =>
    intro a b ha hb h
    have splL : ∀ {w₁ w₂ : List (Bool × Mat k r)}, Spl w w₁ w₂ → Spl (w ++ [x]) (w₁ ++ [x]) w₂ := by
      intro w₁ w₂ hs
      refine ⟨hs.1.append (List.Sublist.refl [x]), hs.2.1.trans (List.sublist_append_left w [x]), ?_⟩
      have hp : (w₁ ++ [x] ++ w₂).Perm (w₁ ++ w₂ ++ [x]) := by
        simpa [List.append_assoc] using (List.perm_append_comm (l₁ := [x]) (l₂ := w₂)).append_left w₁
      exact hp.trans (hs.2.2.append_right [x])
    have splR : ∀ {w₁ w₂ : List (Bool × Mat k r)}, Spl w w₁ w₂ → Spl (w ++ [x]) w₁ (w₂ ++ [x]) := by
      intro w₁ w₂ hs
      refine ⟨hs.1.trans (List.sublist_append_left w [x]), hs.2.1.append (List.Sublist.refl [x]), ?_⟩
      rw [← List.append_assoc]
      exact hs.2.2.append_right [x]
    have h1 : ‖Dw w (fun g => Dx x a g (b g)) g‖ ≤ 2 ^ w.length * M :=
      ih (Dx x a) b (cdx x ha) hb fun w₁ w₂ hs => by
        have h' := h (w₁ ++ [x]) w₂ (splL hs)
        rwa [dw_append_singleton'] at h'
    have h2 : ‖Dw w (fun g => a g (Dx x b g)) g‖ ≤ 2 ^ w.length * M :=
      ih a (Dx x b) ha (cdx x hb) fun w₁ w₂ hs => by
        have h' := h w₁ (w₂ ++ [x]) (splR hs)
        rwa [dw_append_singleton'] at h'
    rw [dw_append_singleton', dx_app x (dif ha) (dif hb), dw_add w (cd_app (cdx x ha) hb) (cd_app ha (cdx x hb))]
    beta_reduce
    refine (norm_add_le _ _).trans ?_
    rw [List.length_append, List.length_singleton, pow_succ]
    linarith
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
