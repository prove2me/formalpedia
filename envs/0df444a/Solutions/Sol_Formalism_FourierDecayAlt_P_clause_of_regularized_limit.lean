-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.clause_of_regularized_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:54.685193+00:00
-- url     : https://prove2.me/submissions/5c72ca23-ca2a-47c6-962d-fad72c9b8dfe

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_InCC_Rw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sInCC_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Rw_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_prodBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Rw_trn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Gf_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gPos_stable
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_suppIn_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_aesm_of_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_InCC_opsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CC_bdd
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_word_le_order
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_rho_eq_trn

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.StepClause := by
  intro k r Wp Wq _ _ _ _ _ _ D A hA hCC
  refine ⟨gPos_stable D, ?_⟩
  intro Θ ε d hε hd hS hP F F' hF hF' hsF hsF'
  set O : Set (Mat k r) := {g | Gf k r D.z D.z' g < ε} with hOdef
  have hO : IsOpen O := isOpen_lt (Gf_cont _ _) continuous_const
  have hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ GPos D := by
    intro g hg
    rcases lt_or_ge (Gf k r D.z D.z' g) ε with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hg, lt_of_lt_of_le hε h⟩
  have hz : ∀ g ∈ GV k r, g ∈ O → F g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd (hsF g hg hne) (not_le.mpr hgO)
  have hz' : ∀ g ∈ GV k r, g ∈ O → F' g = 0 := by
    intro g hg hgO
    by_contra hne
    exact absurd (hsF' g hg hne) (not_le.mpr hgO)
  have hAd : A ≤ A + d := by linarith
  have hAd0 : 0 ≤ A + d := by linarith

  have hadj : ∀ T ∈ Θ, InCC A (opOrder Θ + 5) (ap T.coefAdj F') := by
    intro T hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c', hc'⟩ := hF'
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top (hS T hT).2)
      (fun u v hu hv hl g hg hgO => (hC u v hu hv hl g hg (not_lt.mp hgO)).2) hc' hz'⟩
  refine ⟨suppIn_of D hε hsF, suppIn_of D hε hsF', sInCC_mono hAd (by omega) hF, sInCC_mono hAd (by omega) hF',
    ?_, ?_, ?_⟩
  ·
    refine InCC_opsum Θ (fun T => ap T.coef (Rw T.word F)) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨C, hC⟩ := hP T hT
    obtain ⟨c, hc⟩ : InCC (A + d) 5 (Rw T.word F) :=
      InCC_Rw T.word_lie (sInCC_mono le_rfl (by omega) hF)
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top (hS T hT).1)
      (fun u v hu hv hl g hg hgO => (hC u v hu hv (by omega) g hg (not_lt.mp hgO)).1) hc
      (Rw_vanish hO T.word_lie hz)⟩
  ·
    refine InCC_opsum Θ
      (fun T => fun g => ((-1 : ℂ) ^ T.word.length) • Rw T.word.reverse (ap T.coefAdj F') g) ?_
    intro T hT
    have hlen := word_le_order Θ hT
    obtain ⟨c, hc⟩ : InCC A 5 (Rw T.word.reverse (ap T.coefAdj F')) :=
      InCC_Rw (fun X hX => T.word_lie X (List.mem_reverse.mp hX))
        (sInCC_mono le_rfl (by simp; omega) (hadj T hT))
    exact ⟨_, CCle_smul _ hc⟩
  ·
    intro p hp T hT i j hij hj
    have hlen := word_le_order Θ hT
    set a : Mat k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ with hadef
    set b : Mat k r := Matrix.of p.2.2 * Matrix.of p.2.1 with hbdef
    have ha : a ∈ GV k r := gv_mul (gv_inv hp.1.1) (gv_inv hp.2.1.1)
    have hb : b ∈ GV k r := gv_mul hp.2.2.2.1 hp.2.2.1.1
    have hlie1 : ∀ X ∈ (T.word.take i).reverse, inLie k r X := fun X hX =>
      T.word_lie X (List.mem_of_mem_take (List.mem_reverse.mp hX))
    have hlie2 : ∀ X ∈ T.word.drop j, inLie k r X := fun X hX => T.word_lie X (List.mem_of_mem_drop hX)
    have hl1 : (T.word.take i).reverse.length ≤ opOrder Θ := by
      simp only [List.length_reverse, List.length_take]; omega
    have hl2 : (T.word.drop j).length ≤ opOrder Θ := by
      simp only [List.length_drop]; omega
    obtain ⟨K₁, hK₁⟩ : InCC A 0 (Rw (T.word.take i).reverse (ap T.coefAdj F')) :=
      InCC_Rw hlie1 (sInCC_mono le_rfl (by omega) (hadj T hT))
    obtain ⟨K₂, hK₂⟩ : InCC (A + d) 0 (Rw ((T.word.drop j).map fun X => b⁻¹ * X * b) F) :=
      InCC_Rw (fun X hX => by
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
        exact lie_conj (hlie2 Y hY) hb) (sInCC_mono le_rfl (by simp only [List.length_map]; omega) hF)
    obtain ⟨cF, hcF⟩ := hF
    have hFk : CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) F := hcF.1
    set f₁ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.take i).reverse (ap T.coefAdj F') with hf₁
    set f₂ : Mat k r → (Wq →L[ℂ] Wp) := Rw (T.word.drop j) (rho D p F) with hf₂
    have hc₁ : ContinuousOn f₁ (GV k r) := CkOn_cont subset_rfl hK₁.1
    have hc₂ : ContinuousOn f₂ (GV k r) := by
      apply CkOn_cont subset_rfl
      rw [hf₂, ← Dw_wR, rho_eq_trn]
      apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) hlie2 x (by simpa [wL] using hx))
      apply CkOn_trn _ ha hb
      refine sCkOn_mono ?_ hFk
      simp only [wR, List.length_map, zero_add]
      exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)
    have hb₂ : ∀ g ∈ GV k r, ‖f₂ g‖ ≤ ‖Lp D p‖ * K₂ := by
      intro g hg
      rw [hf₂, rho_eq_trn, Rw_trn _ ha hb _ hlie2
        (sCkOn_mono (by exact_mod_cast (by omega : (T.word.drop j).length ≤ opOrder Θ + 5)) hFk) g hg]
      exact ((Lp D p).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (CC_bdd hAd0 hK₂ _ (gv_mul (gv_mul ha hg) hb)) (norm_nonneg _))
    set G : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((‖f₂ g‖ : ℝ) : ℂ) • f₁ g with hG
    have hGn : ∀ g, ‖G g‖ = ‖f₁ g‖ * ‖f₂ g‖ := by
      intro g
      simp only [hG, norm_smul, Complex.norm_real, norm_norm]
      ring
    have hGc : ContinuousOn G (GV k r) := (Complex.continuous_ofReal.comp_continuousOn hc₂.norm).smul hc₁
    have hGm := aesm_of_continuousOn D hGc
    have hfin := hCC G (‖Lp D p‖ * K₂ * K₁) hGm (by
      intro g hg
      have h1 : gN g ^ A * ‖f₁ g‖ ≤ K₁ := hK₁.2 [] [] (by simp) (by simp) (by simp) g hg
      have h0 : 0 ≤ gN g ^ A * ‖f₁ g‖ := mul_nonneg (Real.rpow_nonneg (gN_pos hg).le _) (norm_nonneg _)
      calc gN g ^ A * ‖G g‖ = ‖f₂ g‖ * (gN g ^ A * ‖f₁ g‖) := by rw [hGn]; ring
        _ ≤ ‖Lp D p‖ * K₂ * K₁ := mul_le_mul (hb₂ g hg) h1 h0 ((norm_nonneg _).trans (hb₂ g hg)))
    have hint : Integrable (fun g : Mt k r => G (Matrix.of g)) D.μG := ⟨hGm, hfin⟩
    refine hint.norm.congr (Filter.Eventually.of_forall fun g => ?_)
    exact hGn _
end Formalism.FourierDecayAlt.P
