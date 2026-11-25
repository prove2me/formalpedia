-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutBP.jdCCLowerQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:37:26.873005+00:00
-- url     : https://prove2.me/submissions/d9c66e26-1bfb-439b-ba25-9d1ca54f8743

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutNFApxDomThQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_ccleQ_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_ccleQ_mono_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_word_le_opOrder
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_Rw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_mono_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Rw_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_nrm_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_prodBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutBP
theorem _root_.solution {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ)
    (hd : 0 ≤ d) (hG : CutMP.GlobCoef Θ d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CkOn ⊤ (B.GV k r) F →
      B.CCle A (m + B.opOrder Θ) F b → B.CCle (A - d) m (B.opApply Θ F) (K * b) := by
  have _hd := hd
  set o := B.opOrder Θ with ho
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg

  have hterm : ∀ T ∈ Θ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ),
      B.CCle A (m + o) F b → B.CCle (A - d) m (ap T.coef (B.Rw T.word F)) (K * b) := by
    intro T hT
    obtain ⟨hc1, -, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    set s : ℂ := (((T.word.map nz).prod : ℝ) : ℂ) with hs
    refine ⟨2 ^ m * (|C| * ‖s‖), by positivity, fun F b hF => ?_⟩
    have hb0 : 0 ≤ b := ccleQ_nonneg hF
    have hlen : T.word.length ≤ o := word_le_opOrder Θ T hT
    have hF1 : B.CCle A (m + (T.word.map nrm).length) F b :=
      CCle_mono_m (by simp; omega) hF
    have hunit : ∀ X ∈ T.word.map nrm, unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact nrm_unit (T.word_lie Y hY)
    have hR : B.CCle A m (B.Rw T.word F) (‖s‖ * b) := by
      rw [Rw_scale]
      exact CCle_smul s (CCle_Rw hunit hF1)
    have hR' : B.CCle (A - d + d) m (B.Rw T.word F) (‖s‖ * b) := by rw [sub_add_cancel]; exact hR
    have hP := prodBound hO hcov (sCkOn_mono le_top hc1)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).1) hR' (fun g _ hg => by simp at hg)
    refine ccleQ_mono_c hP (le_of_eq ?_)
    rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) hb0)]
    ring

  have hsum : ∀ L : List (B.DTerm k r Wp Wq), (∀ T ∈ L, T ∈ Θ) → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ), B.CCle A (m + o) F b →
        B.CCle (A - d) m (fun g => (L.map fun T => ap T.coef (B.Rw T.word F) g).sum) (K * b) := by
    intro L
    induction L with
    | nil =>
      intro _
      refine ⟨0, le_rfl, fun F b _ => ?_⟩
      simpa using (CCle_zero : B.CCle (A - d) m (fun _ : B.Mat k r => (0 : Wq →L[ℂ] Wp)) 0)
    | cons T L ih =>
      intro hL
      obtain ⟨K₁, hK₁, h₁⟩ := hterm T (hL T (by simp))
      obtain ⟨K₂, hK₂, h₂⟩ := ih fun S hS => hL S (by simp [hS])
      refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun F b hF => ?_⟩
      have h := CCle_add (h₁ F b hF) (h₂ F b hF)
      have e : (K₁ + K₂) * b = K₁ * b + K₂ * b := by ring
      rw [e]
      simpa using h
  obtain ⟨K, hK, hKb⟩ := hsum Θ fun T hT => hT
  refine ⟨K, hK, fun F b _ hF => ?_⟩
  have hop : B.opApply Θ F = fun g => (Θ.map fun T => ap T.coef (B.Rw T.word F) g).sum := rfl
  rw [hop]
  exact hKb F b hF
end Formalism.FourierDecayAlt.P.CutBP
