-- Prove2me | solution 1 for Formalism.L2.Th1.H.characterIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:26:19.739809+00:00
-- url     : https://prove2.me/submissions/88d6284c-abc7-4869-b244-18aa18f001e1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionFiltrationStable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open MeasureTheory Module
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution : CharIntegral := by
  intro V _ _ _ _ _ μ _ H _ hH Λ' D' hD v hv hv0
  set f : V → ℂ := fun z => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H v z : ℂ)) with hf
  have hadd : ∀ x y : V, altE H v (x + y) = altE H v x + altE H v y := by
    intro x y
    simp [altE, map_add]
  have hmul : ∀ x y : V, f (x + y) = f x * f y := by
    intro x y
    simp only [hf, hadd]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hper : ∀ (g : Λ') (z : V), f (g +ᵥ z) = f z := by
    intro g z
    obtain ⟨m, hm⟩ := hv g g.2
    show f ((g : V) + z) = f z
    rw [hmul]
    have : f (g : V) = 1 := by
      simp only [hf, hm]
      have := Complex.exp_int_mul_two_pi_mul_I m
      rw [← this]
      congr 1
      push_cast
      ring
    rw [this, one_mul]
  by_cases hμ : μ D' = 0
  · exact setIntegral_measure_zero _ hμ
  haveI : Countable Λ' := by
    have hc := Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := μ) (As := fun g : Λ' => g +ᵥ D')
      (fun g => hD.nullMeasurableSet_vadd g) hD.aedisjoint
    have huniv : {g : Λ' | 0 < μ (g +ᵥ D')} = Set.univ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [measure_vadd]
      exact pos_iff_ne_zero.mpr hμ
    rw [huniv] at hc
    exact Set.countable_univ_iff.mp hc
  have htr : ∀ w : V, ∫ z in D', f z ∂μ = f w * ∫ z in D', f z ∂μ := by
    intro w
    have hD2 : IsAddFundamentalDomain Λ' (w +ᵥ D') μ := hD.vadd_of_comm w
    have e1 : ∫ z in w +ᵥ D', f z ∂μ = ∫ z in D', f z ∂μ := hD2.setIntegral_eq hD hper
    have e2 : ∫ z in w +ᵥ D', f z ∂μ = ∫ z in D', f (w + z) ∂μ := by
      rw [← Set.image_vadd]
      exact (measurePreserving_add_left μ w).setIntegral_image_emb (measurableEmbedding_addLeft w) f D'
    calc ∫ z in D', f z ∂μ = ∫ z in w +ᵥ D', f z ∂μ := e1.symm
      _ = ∫ z in D', f (w + z) ∂μ := e2
      _ = f w * ∫ z in D', f z ∂μ := by
        simp only [hmul]
        rw [integral_const_mul]
  have ha : 0 < (H v v).re := hH v hv0
  set c : ℂ := ((1 / (2 * (H v v).re) : ℝ) : ℂ) * Complex.I with hc
  have hw : altE H v (c • v) = -(1 / 2) := by
    simp only [altE, LinearMap.map_smulₛₗ, hc, smul_eq_mul, Complex.mul_im, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im]
    field_simp
    ring
  have hfw : f (c • v) = -1 := by
    simp only [hf, hw]
    push_cast
    have : 2 * (Real.pi : ℂ) * Complex.I * -(1 / 2) = -(Real.pi * Complex.I) := by ring
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have := htr (c • v)
  rw [hfw] at this
  linear_combination this / 2
end Formalism.L2.Th1.H
