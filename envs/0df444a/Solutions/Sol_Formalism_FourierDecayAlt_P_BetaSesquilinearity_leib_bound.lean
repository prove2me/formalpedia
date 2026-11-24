-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.leib_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:13.358524+00:00
-- url     : https://prove2.me/submissions/fbf24dd6-54af-4eee-b56a-dff304f611bb

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_leib

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
variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU) (g : Mat k r) (hg : g ∈ GV k r)
    (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ (a : Mat k r → (E →L[ℂ] E')) (Φ : Mat k r → E), (∀ x ∈ w, inLie k r x.2) → Pr O UU w.length a Φ →
      (∀ w₁ w₂ : List (Bool × Mat k r), w₁.Sublist w → w₂.Sublist w → w₁.length + w₂.length = w.length →
        ‖Dw w₁ a g‖ * ‖Dw w₂ Φ g‖ ≤ M) →
      ‖Dw w (ap a Φ) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a Φ _ _ hM
    have := hM [] [] (List.Sublist.refl _) (List.Sublist.refl _) rfl
    simp only [Dw, List.foldr_nil, List.length_nil, pow_zero, one_mul] at this ⊢
    exact ((a g).le_opNorm _).trans this
  | append_singleton w x ih =>
    intro a Φ hw hP hM
    have hw' : ∀ y ∈ w, inLie k r y.2 := fun y hy => hw y (by simp [hy])
    have hx : inLie k r x.2 := hw x (by simp)
    have hlen : (((w ++ [x]).length : ℕ) : ℕ∞) = (w.length : ℕ∞) + 1 := by simp
    rw [hlen] at hP
    have hPl := hP.left hx
    have hPr := hP.right hO hx
    have e1 : Dw (w ++ [x]) (ap a Φ) g = Dw w (ap (Dx x a) Φ) g + Dw w (ap a (Dx x Φ)) g := by
      rw [Dw_append]
      show Dw w (Dx x (ap a Φ)) g = _
      rw [Dw_congr hw' (Pr.leib hO hcov hx (hP.mono le_add_self)) g hg]
      exact Dw_add hw' (hPl.ck hO hcov) (hPr.ck hO hcov) g hg
    have b1 := ih (Dx x a) Φ hw' hPl (by
      intro w₁ w₂ h₁ h₂ hl
      have := hM (w₁ ++ [x]) w₂ (List.Sublist.append h₁ (List.Sublist.refl _))
        (h₂.trans (List.sublist_append_left _ _)) (by simp; omega)
      rwa [Dw_append] at this)
    have b2 := ih a (Dx x Φ) hw' hPr (by
      intro w₁ w₂ h₁ h₂ hl
      have := hM w₁ (w₂ ++ [x]) (h₁.trans (List.sublist_append_left _ _))
        (List.Sublist.append h₂ (List.Sublist.refl _)) (by simp; omega)
      rwa [Dw_append] at this)
    rw [e1]
    calc ‖Dw w (ap (Dx x a) Φ) g + Dw w (ap a (Dx x Φ)) g‖
        ≤ 2 ^ w.length * M + 2 ^ w.length * M := (norm_add_le _ _).trans (add_le_add b1 b2)
      _ = 2 ^ (w ++ [x]).length * M := by simp [pow_succ]; ring
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
