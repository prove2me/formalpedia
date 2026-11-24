-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.fold_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:43:43.605606+00:00
-- url     : https://prove2.me/submissions/366beb4c-be84-437a-aae3-a7f613ab9dda

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_top_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_top_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_spread


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution (ts : List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) :
    ∀ (Φ₁ Φ₂ : Mat k r → E) (g : Mat k r), g ∈ GV k r → Loc (ts.length : ℕ∞) Φ₁ g →
      Loc (ts.length : ℕ∞) Φ₂ g → ∀ c : ℂ,
        fold M ts (fun x => Φ₁ x + c • Φ₂ x) g = fold M ts Φ₁ g + c • fold M ts Φ₂ g := by
  induction ts with
  | nil => intro Φ₁ Φ₂ g _ _ _ c; rfl
  | cons t ts ih =>
    intro Φ₁ Φ₂ g hg h₁ h₂ c
    obtain ⟨U₁, hU₁, hgU₁, hU₁'⟩ := loc_spread h₁
    obtain ⟨U₂, hU₂, hgU₂, hU₂'⟩ := loc_spread h₂
    have hle : (ts.length : ℕ∞) ≤ ((t :: ts).length : ℕ∞) := by exact_mod_cast Nat.le_succ ts.length
    have heq : ∀ x ∈ U₁ ∩ U₂, x ∈ GV k r →
        fold M ts (fun y => Φ₁ y + c • Φ₂ y) x = (fun y => fold M ts Φ₁ y + c • fold M ts Φ₂ y) x :=
      fun x hx hxG => ih Φ₁ Φ₂ x hxG (loc_mono hle (hU₁' x hx.1)) (loc_mono hle (hU₂' x hx.2)) c
    have e1 : 1 + ts.length = (t :: ts).length := by simp only [List.length_cons]; omega
    have hf₁ : Loc 1 (fold M ts Φ₁) g := by
      have := fold_loc M ts 1 Φ₁ g (by rw [e1]; exact h₁)
      simpa using this
    have hf₂ : Loc 1 (fold M ts Φ₂) g := by
      have := fold_loc M ts 1 Φ₂ g (by rw [e1]; exact h₂)
      simpa using this
    rw [fold_cons, fold_cons, fold_cons, top_congr M (hU₁.inter hU₂) heq t.1 t.2.1 t.2.2 g ⟨hgU₁, hgU₂⟩ hg]
    exact top_lin M hf₁ hf₂ hg c t.1 t.2.1 t.2.2
end Formalism.FourierDecayAlt.P.FourTermExpansion
