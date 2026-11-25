-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.LemmaU.lemmaU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:40.264818+00:00
-- url     : https://prove2.me/submissions/90de30c9-3430-4f5a-b12f-5ecbc83ab9e8

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_LemmaU_choose_eq
import Theorems.Thm_P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_3f124dd9bb9d
import Theorems.Thm_P2M_Formalism_DoubleCosetMeasures_P_LemmaU_toRows__mul_a68189d70cdc
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_LemmaU_II_mul
import Theorems.Thm_P2M_Formalism_DoubleCosetMeasures_P_LemmaU_suppJ__bdf06674c24b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ComplexConjugate
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.LemmaU
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P.LemmaU
theorem _root_.solution : LemmaUSplit := by
  intro F _ _ _ _ _ _ _ a t O hO ϖ hϖ J' hJc hJint ρ hρ χ nrm lam heq c hc μ ν₁ ν₂ _ _

  have hMatrixOpensMeasurable : ∀ (m n : Type) [Fintype m] [Fintype n],
      OpensMeasurableSpace (Matrix m n F) := fun m n _ _ =>
    inferInstanceAs (OpensMeasurableSpace (m → n → F))
  haveI := hMatrixOpensMeasurable (Fin a) (Fin a)
  have hJm : MeasurableSet (Jset J') :=
    ((hJc.image Units.continuous_val).isClosed).measurableSet
  have hOpen1 : IsOpen {z : F | ∃ o ∈ O, z = ϖ * o} := by
    have : {z : F | ∃ o ∈ O, z = ϖ * o} = (fun z => ϖ⁻¹ * z) ⁻¹' (O : Set F) := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
      constructor
      · rintro ⟨o, ho, rfl⟩; rwa [← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]
      · intro h; exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]⟩
    rw [this]; exact hO.preimage (continuous_const.mul continuous_id)
  have hIIm : MeasurableSet (IIset (a := a) (t := t) O ϖ) := by
    have : IIset (a := a) (t := t) O ϖ = ⋂ i, ⋂ j, (fun y : Matrix (Fin t) (Fin a) F => y i j) ⁻¹'
        {z : F | ∃ o ∈ O, z = ϖ * o} := by
      ext y; simp [IIset]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    exact (hOpen1.measurableSet).preimage
      ((measurable_pi_apply j).comp (measurable_pi_apply i))
  have hR1 : Measurable (fun x : Matrix (Fin a ⊕ Fin t) (Fin a) F => toRows₁ x) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inl i)
  have hR2 : Measurable (fun x : Matrix (Fin a ⊕ Fin t) (Fin a) F => toRows₂ x) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (Sum.inr i)
  have hFR : Measurable (fun p : Matrix (Fin a) (Fin a) F × Matrix (Fin t) (Fin a) F =>
      Matrix.fromRows p.1 p.2) := by
    refine measurable_pi_lambda _ fun i => ?_
    cases i with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr i => exact (measurable_pi_apply i).comp measurable_snd
  set S : Set (Matrix (Fin a ⊕ Fin t) (Fin a) F) :=
    {x | toRows₁ x ∈ Jset J' ∧ toRows₂ x ∈ IIset O ϖ} with hSdef
  have hSm : MeasurableSet S := (hR1 hJm).inter (hR2 hIIm)
  set ν := (ν₁.prod ν₂).map (fun p => Matrix.fromRows p.1 p.2) with hνdef
  have hνS : ν S = ν₁ (Jset J') * ν₂ (IIset O ϖ) := by
    rw [hνdef, Measure.map_apply hFR hSm]
    have : (fun p : Matrix (Fin a) (Fin a) F × Matrix (Fin t) (Fin a) F =>
        Matrix.fromRows p.1 p.2) ⁻¹' S = Jset J' ×ˢ IIset O ϖ := by
      ext p; simp [hSdef]
    rw [this, Measure.prod_prod]

  have hW : ∀ g (hg : g ∈ J'), weilIP ν (omegaS χ nrm g (phiU O ϖ J' ρ)) (phiU O ϖ J' ρ) =
      ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^
        ((Fintype.card (Fin a ⊕ Fin t) : ℝ) / 2) : ℝ) : ℂ) * ((ρ ⟨g, hg⟩ : ℂˣ) : ℂ) *
      (((ν₁ (Jset J')).toReal * (ν₂ (IIset O ϖ)).toReal : ℝ) : ℂ) := by
    intro g hg
    unfold weilIP
    have hpt : ∀ x, omegaS χ nrm g (phiU O ϖ J' ρ) x * conj (phiU O ϖ J' ρ x) =
        S.indicator (fun _ => ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
      (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^
        ((Fintype.card (Fin a ⊕ Fin t) : ℝ) / 2) : ℝ) : ℂ) * ((ρ ⟨g, hg⟩ : ℂˣ) : ℂ)) x := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        obtain ⟨⟨k, hk, ek⟩, hxII⟩ := hx
        have h1 : (∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧
            toRows₂ x ∈ IIset O ϖ := ⟨⟨⟨k, hk⟩, ek⟩, hxII⟩
        have ekg : ((⟨k * g, J'.mul_mem hk hg⟩ : J') : GL (Fin a) F) =
            toRows₁ (x * (g : Matrix (Fin a) (Fin a) F)) := by
          simp [toRows₁_mul, ← ek]
        have h2 : (∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) =
            toRows₁ (x * (g : Matrix (Fin a) (Fin a) F))) ∧
            toRows₂ (x * (g : Matrix (Fin a) (Fin a) F)) ∈ IIset O ϖ :=
          ⟨⟨_, ekg⟩, by rw [toRows₂_mul]; exact II_mul O ϖ _ hxII _ (hJint g hg)⟩
        unfold omegaS phiU
        rw [dif_pos h1, dif_pos h2, choose_eq h1.1 ⟨k, hk⟩ ek, choose_eq h2.1 _ ekg]
        have hmul : (⟨k * g, J'.mul_mem hk hg⟩ : J') = ⟨k, hk⟩ * ⟨g, hg⟩ := rfl
        rw [hmul, map_mul, Units.val_mul]
        have hn : ((ρ ⟨k, hk⟩ : ℂˣ) : ℂ) * conj ((ρ ⟨k, hk⟩ : ℂˣ) : ℂ) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hρ]; simp
        linear_combination (((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          (((nrm ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ^
          ((Fintype.card (Fin a ⊕ Fin t) : ℝ) / 2) : ℝ) : ℂ) * ((ρ ⟨g, hg⟩ : ℂˣ) : ℂ)) * hn
      · rw [Set.indicator_of_notMem hx]
        have hn : ¬ ((∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧
            toRows₂ x ∈ IIset O ϖ) := by
          rintro ⟨⟨k, ek⟩, h2⟩; exact hx ⟨⟨k, k.2, ek⟩, h2⟩
        simp only [phiU]; rw [dif_neg hn]; simp
    simp_rw [hpt]
    rw [integral_indicator_const _ hSm]
    simp only [Measure.real, hνS, ENNReal.toReal_mul, Complex.real_smul]
    push_cast; ring

  have hJ'm : MeasurableSet (J' : Set (GL (Fin a) F)) := hJc.isClosed.measurableSet
  have hint : ∀ g, weilIP ν (omegaS χ nrm g (phiU O ϖ J' ρ)) (phiU O ϖ J' ρ) * conj (c g) =
      (J' : Set (GL (Fin a) F)).indicator (fun _ =>
        (((ν₁ (Jset J')).toReal * (ν₂ (IIset O ϖ)).toReal : ℝ) : ℂ) * conj (c 1)) g := by
    intro g
    by_cases hg : g ∈ J'
    · rw [Set.indicator_of_mem (show g ∈ (J' : Set _) from hg), hW g hg]
      have hcg : c g = ((lam ⟨g, hg⟩ : ℂˣ) : ℂ) * c 1 := by
        have := hc 1 ⟨g, hg⟩; simpa using this
      have he := heq ⟨g, hg⟩
      have hcard : (Fintype.card (Fin a ⊕ Fin t) : ℝ) = ((a + t : ℕ) : ℝ) := by simp
      rw [hcard, hcg, map_mul]
      simp only at he
      linear_combination ((((ν₁ (Jset J')).toReal * (ν₂ (IIset O ϖ)).toReal : ℝ) : ℂ) *
        conj (c 1)) * he
    · rw [Set.indicator_of_notMem (show g ∉ (J' : Set _) from hg)]
      have := Formalism.DoubleCosetMeasures.P.LemmaU.suppJ' F a t O ϖ J' ρ χ nrm ν g hg
      rw [this, zero_mul]
  unfold localZ
  simp_rw [hint]
  rw [integral_indicator_const _ hJ'm]
  simp only [Measure.real, Complex.real_smul]
  push_cast; ring
end Formalism.DoubleCosetMeasures.P.LemmaU
