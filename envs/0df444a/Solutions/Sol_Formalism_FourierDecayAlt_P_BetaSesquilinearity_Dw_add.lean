-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:35:11.62968+00:00
-- url     : https://prove2.me/submissions/c9eeee45-d5c1-402f-b6bd-fab4b901093e

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {w : List (Bool × Mat k r)} (hw : ∀ x ∈ w, inLie k r x.2) {f₁ f₂ : Mat k r → E}
    (h₁ : CkOn w.length (GV k r) f₁) (h₂ : CkOn w.length (GV k r) f₂) :
    ∀ g ∈ GV k r, Dw w (fun g => f₁ g + f₂ g) g = Dw w f₁ g + Dw w f₂ g := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hw' : ∀ y ∈ w, inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : inLie k r x.2 := hw x (by simp)
    have e : (((x :: w).length : ℕ) : ℕ∞) = 1 + (w.length : ℕ∞) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    have h₁' : CkOn (1 + w.length) (GV k r) f₁ := by rw [← e]; exact h₁
    have h₂' : CkOn (1 + w.length) (GV k r) f₂ := by rw [← e]; exact h₂
    have hle : ((w.length : ℕ) : ℕ∞) ≤ (((x :: w).length : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.le_succ w.length
    have hm₁ : CkOn (w.length) (GV k r) f₁ := sCkOn_mono hle h₁
    have hm₂ : CkOn (w.length) (GV k r) f₂ := sCkOn_mono hle h₂
    show Dx x (Dw w (fun g => f₁ g + f₂ g)) g = Dx x (Dw w f₁) g + Dx x (Dw w f₂) g
    rw [Dx_congr hx (ih hw' hm₁ hm₂) g hg]
    exact Dx_add hx (CkOn_Dw hw' h₁') (CkOn_Dw hw' h₂') g hg
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
