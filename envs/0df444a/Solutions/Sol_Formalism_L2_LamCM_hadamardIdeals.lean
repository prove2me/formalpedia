-- Prove2me | solution 1 for Formalism.L2.LamCM.hadamardIdeals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:28.909291+00:00
-- url     : https://prove2.me/submissions/92ba7145-7157-4197-889a-c0c6ddd3e801

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Theorems.Thm_P2M_Formalism_L2_LamCM_A2_absNorm_pos__7ef009ed3ead
import Theorems.Thm_P2M_Formalism_L2_LamCM_A2_absNorm_anti__8418fc33d666
import Theorems.Thm_Formalism_L2_LamCM_A2_absNorm_span_real
import Theorems.Thm_Formalism_L2_LamCM_A2_det_re_pos
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_ne_zero
import Theorems.Thm_Formalism_L2_LamCM_A2_deg_detLine
import Theorems.Thm_Formalism_L2_LamCM_A2_gramC_eq
import Theorems.Thm_Formalism_L2_LamCM_A2_gramC_det
import Theorems.Thm_Formalism_L2_LamCM_hadamardInequality
import Theorems.Thm_Formalism_L2_LamCM_A2_prod_mul_le_detIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open A2
namespace Formalism.L2.LamCM
theorem _root_.solution : HadamardIdeals := by
  intro K _ _ m L ℓ u La hL hℓ hli hu hLa hsq
  set d := (Matrix.of u).det with hd
  have hdne : d ≠ 0 := by
    have : IsUnit (Matrix.of u) := Matrix.linearIndependent_rows_iff_isUnit.1 hli
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hX0 : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => (hℓ j).1)
      (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
  have hN := absNorm_anti' (prod_mul_le_detIdeal L hL ℓ u hu) hX0
  have hposI : ∀ j, (0 : ℝ) < ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) := fun j => by
    exact_mod_cast absNorm_pos' (hℓ j).1
  have hposd : ∀ σ : K →+* ℂ, 0 < ‖σ d‖ := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hdne)
  have hposD := absNorm_pos' (detIdeal_ne_zero L hL)
  have hNX : ((FractionalIdeal.absNorm ((∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d) : ℚ) : ℝ) =
      (∏ j, ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ)) * ∏ σ : K →+* ℂ, ‖σ d‖ := by
    rw [map_mul, map_prod, Rat.cast_mul, Rat.cast_prod, absNorm_span_real]
  have hlogN : Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) ≤
      ∑ j, Real.log ((FractionalIdeal.absNorm (ℓ j).I : ℚ) : ℝ) + ∑ σ : K →+* ℂ, Real.log ‖σ d‖ := by
    rw [← Real.log_prod (fun j _ => (hposI j).ne'), ← Real.log_prod (fun σ _ => (hposd σ).ne'),
      ← Real.log_mul (Finset.prod_pos fun j _ => hposI j).ne' (Finset.prod_pos fun σ _ => hposd σ).ne', ← hNX]
    exact Real.log_le_log (by exact_mod_cast hposD) (by exact_mod_cast hN)
  have hσ : ∀ σ : K →+* ℂ, Real.log ‖σ d‖ + Real.log (Real.sqrt (L.H σ).det.re) ≤
      ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
    intro σ
    have hD := det_re_pos (hL.2.2 σ)
    have hGpd : (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u).PosDef := by
      rw [gramC_eq]
      apply (hL.2.2 σ).conjTranspose_mul_mul_same
      apply Matrix.mulVec_injective_iff_isUnit.2
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact IsUnit.mk0 _ ((map_ne_zero σ).2 hdne)
    have hdiagpos : ∀ j, 0 < (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u j j).re := fun j => by
      simpa using (Complex.lt_def.1 (hGpd.diag_pos (i := j))).1
    have hH := hadamardInequality m _ hGpd
    rw [gramC_det, Complex.re_ofReal_mul] at hH
    have hbound : ∏ j, (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ u j j).re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      apply Finset.prod_le_prod
      · intro j _
        exact (hdiagpos j).le
      · intro j _
        exact hsq σ j
    have key : ‖σ d‖ ^ 2 * (L.H σ).det.re ≤ ∏ j, (La * (ℓ j).n σ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hH.trans hbound
    have hpos' : 0 < ‖σ d‖ ^ 2 * (L.H σ).det.re := by
      have := hposd σ
      positivity
    have hlog := Real.log_le_log hpos' key
    have hnpos : ∀ j, 0 < (ℓ j).n σ := fun j => (hℓ j).2 σ
    rw [Real.log_mul (by have := hposd σ; positivity) hD.ne', Real.log_pow,
      Real.log_prod (fun j _ => by have := hnpos j; positivity)] at hlog
    have hs : ∑ j, Real.log ((La * (ℓ j).n σ) ^ 2) = 2 * ∑ j, (Real.log La + Real.log ((ℓ j).n σ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Real.log_pow, Real.log_mul hLa.ne' (hnpos j).ne']
      push_cast
      ring
    rw [hs] at hlog
    rw [Real.log_sqrt hD.le]
    push_cast at hlog
    linarith
  have hsumσ := Finset.sum_le_sum fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) => hσ σ
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsumσ
  have hc : ∑ σ : K →+* ℂ, ∑ j, Real.log ((ℓ j).n σ) = ∑ j, ∑ σ : K →+* ℂ, Real.log ((ℓ j).n σ) :=
    Finset.sum_comm
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast NumberField.Embeddings.card K ℂ
  rw [hc, hcard] at hsumσ
  rw [deg_detLine]
  simp only [MLine.deg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linarith
end Formalism.L2.LamCM
