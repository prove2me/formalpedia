-- Prove2me | solution 1 for CondConvexRisk.Entropic.entropic_representation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T08:19:24.817624+00:00
-- url     : https://prove2.me/submissions/6472617c-501b-4062-b3eb-09139f47fc65

import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk
import Mathlib

-- Accepted foundations by mrfancypants; provenance is included in the proof bundle.

-- Source module: Solutions.EntropicAccepted


-- Accepted sources by mrfancypants, reused with attribution.


open MeasureTheory

namespace CondConvexRisk.Entropic

theorem aux_cre_trim_eq {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} (hm : m ≤ mΩ)
    (Q : PG m P) : Q.1.trim hm = P.trim hm := by
  refine @Measure.ext _ m _ _ (fun s hs => ?_)
  rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs]
  exact Q.2.2.2 s hs

theorem aux_cre_change {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (Q : PG m P) (g : Ω → ENNReal) (hg : Measurable g) :
    Q.1⁻[g | m] =ᵐ[P] P⁻[fun x => Q.1.rnDeriv P x * g x | m] := by
  have : IsProbabilityMeasure Q.1 := Q.2.1
  refine ae_eq_condLExp hm P _ (measurable_condLExp _ _ _) ?_
  intro s hs
  rw [setLIntegral_rnDeriv_mul Q.2.2.1 hg.aemeasurable (hm s hs)]
  rw [← setLIntegral_trim hm (measurable_condLExp _ _ _) hs, ← aux_cre_trim_eq hm Q]
  exact setLIntegral_condLExp_trim hm Q.1 g hs

end CondConvexRisk.Entropic

open CondConvexRisk.Entropic
open MeasureTheory

theorem CondConvexRisk.Entropic.condRelEntropy_eq_condExp_log_accepted {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (Q : PG m P) :
    (P[density m P Q | m] =ᵐ[P] 1) ∧
      condRelEntropy m P Q =ᵐ[P] condExpExt m Q.1 (fun ω => Real.log (density m P Q ω)) := by
  have : IsProbabilityMeasure Q.1 := Q.2.1
  constructor
  · refine (ae_eq_condExp_of_forall_setIntegral_eq hm ?_ ?_ ?_ ?_).symm
    · exact Measure.integrable_toReal_rnDeriv
    · intro s _ _
      exact (integrable_const (1 : ℝ)).integrableOn
    · intro s hs _
      rw [show density m P Q = fun ω => (Q.1.rnDeriv P ω).toReal from rfl]
      rw [Measure.setIntegral_toReal_rnDeriv Q.2.2.1 s]
      simp [measureReal_def, Q.2.2.2 s hs]
    · exact (stronglyMeasurable_const).aestronglyMeasurable
  · have hmeas : Measurable (density m P Q) := by
      exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have h1 := aux_cre_change hm Q (fun x => ENNReal.ofReal (Real.log (density m P Q x)))
      (ENNReal.measurable_ofReal.comp (Real.measurable_log.comp hmeas))
    have h2 := aux_cre_change hm Q (fun x => ENNReal.ofReal (-Real.log (density m P Q x)))
      (ENNReal.measurable_ofReal.comp (Real.measurable_log.comp hmeas).neg)
    have hfin := Measure.rnDeriv_lt_top Q.1 P
    have e1 : (fun x => ENNReal.ofReal (density m P Q x * Real.log (density m P Q x)))
        =ᵐ[P] (fun x => Q.1.rnDeriv P x * ENNReal.ofReal (Real.log (density m P Q x))) := by
      filter_upwards [hfin] with x hx
      rw [show density m P Q x = (Q.1.rnDeriv P x).toReal from rfl]
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
    have e2 : (fun x => ENNReal.ofReal (-(density m P Q x * Real.log (density m P Q x))))
        =ᵐ[P] (fun x => Q.1.rnDeriv P x * ENNReal.ofReal (-Real.log (density m P Q x))) := by
      filter_upwards [hfin] with x hx
      rw [show density m P Q x = (Q.1.rnDeriv P x).toReal from rfl]
      rw [← mul_neg, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
    have k1 := condLExp_congr_ae (mΩ := m) e1
    have k2 := condLExp_congr_ae (mΩ := m) e2
    filter_upwards [h1, h2, k1, k2] with x hx1 hx2 hk1 hk2
    simp only [condRelEntropy, condExpExt]
    rw [hk1, hk2, hx1, hx2]


open MeasureTheory

namespace CondConvexRisk.Entropic

lemma aux_mpdv_cancel (a b : ℝ) (h : a * b = 1) (x : EReal) :
    (a : EReal) * ((b : EReal) * x) = x := by
  rw [← mul_assoc, ← EReal.coe_mul, h, EReal.coe_one, one_mul]

lemma aux_mpdv_dir {Ω ι κ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ι → Ω → EReal) (G : κ → Ω → EReal) (c : ℝ) (hc : 0 < c)
    (h1 : ∀ i, ∃ k, G k =ᵐ[P] fun ω => (c : EReal) * F i ω)
    (h2 : ∀ k, ∃ i, G k =ᵐ[P] fun ω => (c : EReal) * F i ω) (V : Ω → EReal) :
    IsEssSup P F V → IsEssSup P G (fun ω => (c : EReal) * V ω) := by
  rintro ⟨hV, hle, hmin⟩
  have hc0 : (0 : EReal) ≤ (c : EReal) := EReal.coe_nonneg.2 hc.le
  have hci0 : (0 : EReal) ≤ ((c⁻¹ : ℝ) : EReal) := EReal.coe_nonneg.2 (inv_pos.2 hc).le
  refine ⟨hV.const_mul _, ?_, ?_⟩
  · intro k
    obtain ⟨i, hi⟩ := h2 k
    filter_upwards [hi, hle i] with ω h1 h2
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 hc0
  · intro W hW hWle
    have key : V ≤ᵐ[P] fun ω => ((c⁻¹ : ℝ) : EReal) * W ω := by
      refine hmin _ (hW.const_mul _) (fun i => ?_)
      obtain ⟨k, hk⟩ := h1 i
      filter_upwards [hk, hWle k] with ω h1 h2
      rw [h1] at h2
      calc F i ω = ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * F i ω) :=
            (aux_mpdv_cancel _ _ (inv_mul_cancel₀ hc.ne') _).symm
        _ ≤ ((c⁻¹ : ℝ) : EReal) * W ω := mul_le_mul_of_nonneg_left h2 hci0
    filter_upwards [key] with ω h
    calc (c : EReal) * V ω ≤ (c : EReal) * (((c⁻¹ : ℝ) : EReal) * W ω) :=
          mul_le_mul_of_nonneg_left h hc0
      _ = W ω := aux_mpdv_cancel _ _ (mul_inv_cancel₀ hc.ne') _

lemma aux_mpdv_QP {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (Q : PG m P) {f g : Ω → ℝ} (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) (h : f =ᵐ[Q.1] g) : f =ᵐ[P] g := by
  have hs : MeasurableSet[m] {ω | f ω = g ω} := hf.measurableSet_eq_fun hg
  have hs' : MeasurableSet[m] {ω | ¬ f ω = g ω} := hs.compl
  rw [Filter.EventuallyEq, ae_iff] at h ⊢
  rw [← Q.2.2.2 _ hs']
  exact h

lemma aux_mpdv_core {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} (γ : ℝ) (hγ : γ ≠ 0) (Q : PG m P)
    (X Z : LInf P) (hZ : Z.1 = fun x => -γ * X.1 x) :
    (dvFamily m P Q Z =ᵐ[P]
        fun ω => (γ : EReal) * penaltyFamily m P (rhoGamma m P γ) Q X ω) ∧
      (penaltyFamily m P (rhoGamma m P γ) Q X =ᵐ[P]
        fun ω => ((γ⁻¹ : ℝ) : EReal) * dvFamily m P Q Z ω) := by
  have hce : Q.1[Z.1 | m] =ᵐ[P] fun ω => -γ * Q.1[X.1 | m] ω := by
    apply aux_mpdv_QP Q stronglyMeasurable_condExp
      (stronglyMeasurable_condExp.const_mul (-γ))
    rw [hZ]
    exact condExp_smul (-γ) X.1 m
  have hexp : (fun x => Real.exp (Z.1 x)) = fun x => Real.exp (-γ * X.1 x) := by
    rw [hZ]
  constructor
  · filter_upwards [hce] with ω hω
    simp only [dvFamily, penaltyFamily, rhoGamma]
    rw [hexp, hω, ← EReal.coe_mul]
    congr 1
    field_simp
  · filter_upwards [hce] with ω hω
    simp only [dvFamily, penaltyFamily, rhoGamma]
    rw [hexp, hω, ← EReal.coe_mul]
    congr 1
    field_simp

end CondConvexRisk.Entropic

open MeasureTheory CondConvexRisk.Entropic

theorem CondConvexRisk.Entropic.minimalPenalty_rhoGamma_eq_dv_accepted {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) (Q : PG m P) (V : Ω → EReal) :
    IsEssSup P (dvFamily m P Q) V ↔
      IsEssSup P (penaltyFamily m P (rhoGamma m P γ) Q) (fun ω => ((γ⁻¹ : ℝ) : EReal) * V ω) := by
  have hγ0 : γ ≠ 0 := hγ.ne'
  -- Z = -γ X
  have hA : ∀ X : LInf P, ∃ Z : LInf P, Z.1 = fun x => -γ * X.1 x :=
    fun X => ⟨⟨fun x => -γ * X.1 x, X.2.const_mul _⟩, rfl⟩
  -- X = -γ⁻¹ Z
  have hB : ∀ Z : LInf P, ∃ X : LInf P, Z.1 = fun x => -γ * X.1 x := by
    intro Z
    refine ⟨⟨fun x => -γ⁻¹ * Z.1 x, Z.2.const_mul _⟩, ?_⟩
    funext x
    simp only
    field_simp
  constructor
  · apply aux_mpdv_dir _ _ γ⁻¹ (inv_pos.2 hγ)
    · intro Z
      obtain ⟨X, hX⟩ := hB Z
      exact ⟨X, (aux_mpdv_core γ hγ0 Q X Z hX).2⟩
    · intro X
      obtain ⟨Z, hZ⟩ := hA X
      exact ⟨Z, (aux_mpdv_core γ hγ0 Q X Z hZ).2⟩
  · intro h
    have := aux_mpdv_dir (P := P) (penaltyFamily m P (rhoGamma m P γ) Q) (dvFamily m P Q) γ hγ
      (fun X => by
        obtain ⟨Z, hZ⟩ := hA X
        exact ⟨Z, (aux_mpdv_core γ hγ0 Q X Z hZ).1⟩)
      (fun Z => by
        obtain ⟨X, hX⟩ := hB Z
        exact ⟨X, (aux_mpdv_core γ hγ0 Q X Z hX).1⟩) _ h
    convert this using 1
    funext ω
    exact (aux_mpdv_cancel _ _ (mul_inv_cancel₀ hγ0) _).symm


open MeasureTheory

namespace CondConvexRisk.Entropic

theorem aux_egcc_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : MemLp X ⊤ P) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂P, |X ω| ≤ C := by
  have hlt : eLpNormEssSup X P < ⊤ := by simpa [eLpNorm_exponent_top] using hX.2
  refine ⟨(eLpNormEssSup X P).toReal, ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := X) (μ := P)] with ω hω
  have := ENNReal.toReal_mono hlt.ne hω
  simpa using this

theorem aux_egcc_sm {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (X : Ω → ℝ) : StronglyMeasurable[m] (rhoGamma m P γ X) := by
  unfold rhoGamma
  exact ((Real.measurable_log.comp stronglyMeasurable_condExp.measurable).const_mul
    _).stronglyMeasurable

theorem aux_egcc_props {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) (γ : ℝ) (hγ : 0 < γ)
    {X : Ω → ℝ} (hX : MemLp X ⊤ P) :
    ∃ C : ℝ, 0 ≤ C ∧ Integrable (fun x => Real.exp (-γ * X x)) P ∧
      ∀ᵐ ω ∂P, |X ω| ≤ C ∧ 0 < (P[fun x => Real.exp (-γ * X x) | m]) ω ∧
        |rhoGamma m P γ X ω| ≤ C ∧
        Real.exp (γ * rhoGamma m P γ X ω) = (P[fun x => Real.exp (-γ * X x) | m]) ω := by
  obtain ⟨C, hC0, hC⟩ := aux_egcc_bound hX
  have hint : Integrable (fun x => Real.exp (-γ * X x)) P := by
    refine Integrable.of_bound ?_ (Real.exp (γ * C)) ?_
    · exact Real.continuous_exp.comp_aestronglyMeasurable (hX.1.const_mul (-γ))
    · filter_upwards [hC] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      have := abs_le.1 hω
      nlinarith
  have h1 : P[fun _ => Real.exp (-(γ * C)) | m] ≤ᵐ[P] P[fun x => Real.exp (-γ * X x) | m] := by
    apply condExp_mono (integrable_const _) hint
    filter_upwards [hC] with ω hω
    show Real.exp (-(γ * C)) ≤ Real.exp (-γ * X ω)
    apply Real.exp_le_exp.2
    have := abs_le.1 hω
    nlinarith
  have h2 : P[fun x => Real.exp (-γ * X x) | m] ≤ᵐ[P] P[fun _ => Real.exp (γ * C) | m] := by
    apply condExp_mono hint (integrable_const _)
    filter_upwards [hC] with ω hω
    show Real.exp (-γ * X ω) ≤ Real.exp (γ * C)
    apply Real.exp_le_exp.2
    have := abs_le.1 hω
    nlinarith
  rw [condExp_const hm] at h1 h2
  refine ⟨C, hC0, hint, ?_⟩
  filter_upwards [h1, h2, hC] with ω h1 h2 hω
  have hpos : 0 < (P[fun x => Real.exp (-γ * X x) | m]) ω :=
    lt_of_lt_of_le (Real.exp_pos _) h1
  have hl1 : -(γ * C) ≤ Real.log ((P[fun x => Real.exp (-γ * X x) | m]) ω) := by
    rw [← Real.log_exp (-(γ * C))]
    exact Real.log_le_log (Real.exp_pos _) h1
  have hl2 : Real.log ((P[fun x => Real.exp (-γ * X x) | m]) ω) ≤ γ * C := by
    rw [← Real.log_exp (γ * C)]
    exact Real.log_le_log hpos h2
  refine ⟨hω, hpos, ?_, ?_⟩
  · unfold rhoGamma
    rw [abs_le]
    have hγi : 0 ≤ γ⁻¹ := inv_nonneg.2 hγ.le
    have e1 : γ⁻¹ * (γ * C) = C := by field_simp
    have e2 : γ⁻¹ * (-(γ * C)) = -C := by field_simp
    constructor
    · have := mul_le_mul_of_nonneg_left hl1 hγi
      linarith
    · have := mul_le_mul_of_nonneg_left hl2 hγi
      linarith
  · unfold rhoGamma
    rw [← mul_assoc, mul_inv_cancel₀ hγ.ne', one_mul, Real.exp_log hpos]

end CondConvexRisk.Entropic

open CondConvexRisk.Entropic
open MeasureTheory

theorem CondConvexRisk.Entropic.risk_axioms_accepted {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) :
    IsCondConvexRiskMeasure m P (rhoGamma m P γ) := by
  refine
  { ae_congr := ?_
    stronglyMeasurable := ?_
    memLp := ?_
    translation := ?_
    monotone := ?_
    convex := ?_
    map_zero := ?_ }
  · intro X Y _ _ hXY
    have : (fun x => Real.exp (-γ * X x)) =ᵐ[P] (fun x => Real.exp (-γ * Y x)) := by
      filter_upwards [hXY] with ω hω
      rw [hω]
    filter_upwards [condExp_congr_ae (m := m) this] with ω hω
    simp only [rhoGamma, hω]
  · intro X _
    exact aux_egcc_sm m P γ X
  · intro X hX
    obtain ⟨C, _, _, hp⟩ := aux_egcc_props hm γ hγ hX
    refine memLp_top_of_bound ((aux_egcc_sm m P γ X).mono hm).aestronglyMeasurable C ?_
    filter_upwards [hp] with ω hω
    rw [Real.norm_eq_abs]
    exact hω.2.2.1
  · intro X Z hX hZ hZm
    obtain ⟨C, hC0, hint, hprops⟩ := aux_egcc_props hm γ hγ hX
    obtain ⟨D, hD0, hD⟩ := aux_egcc_bound hZ
    have hfun : (fun x => Real.exp (-γ * (X + Z) x)) =
        (fun x => Real.exp (-γ * Z x)) * (fun x => Real.exp (-γ * X x)) := by
      ext x
      simp only [Pi.add_apply, Pi.mul_apply, ← Real.exp_add]
      ring_nf
    have hsm : StronglyMeasurable[m] (fun x => Real.exp (-γ * Z x)) :=
      (Real.continuous_exp.measurable.comp (hZm.measurable.const_mul (-γ))).stronglyMeasurable
    have hpull := condExp_stronglyMeasurable_mul_of_bound hm hsm hint (Real.exp (γ * D)) (by
      filter_upwards [hD] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      have := abs_le.1 hω
      nlinarith)
    filter_upwards [hpull, hprops] with ω h1 h2
    obtain ⟨_, hA, _, _⟩ := h2
    simp only [rhoGamma, hfun, h1, Pi.sub_apply]
    rw [Pi.mul_apply, Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp]
    field_simp
    ring
  · intro X Y hX hY hXY
    obtain ⟨C, _, hintX, hpX⟩ := aux_egcc_props hm γ hγ hX
    obtain ⟨D, _, hintY, hpY⟩ := aux_egcc_props hm γ hγ hY
    have hmono : P[fun x => Real.exp (-γ * Y x) | m] ≤ᵐ[P]
        P[fun x => Real.exp (-γ * X x) | m] := by
      apply condExp_mono hintY hintX
      filter_upwards [hXY] with ω hω
      exact Real.exp_le_exp.2 (by nlinarith)
    filter_upwards [hmono, hpX, hpY] with ω h hx hy
    unfold rhoGamma
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hy.2.1 h) (inv_nonneg.2 hγ.le)
  · intro X Y Λ hX hY hΛ hΛb
    obtain ⟨C, hC0, hintX, hpX⟩ := aux_egcc_props hm γ hγ hX
    obtain ⟨D, hD0, hintY, hpY⟩ := aux_egcc_props hm γ hγ hY
    have hWm : MemLp (Λ * X + (1 - Λ) * Y) ⊤ P := by
      refine memLp_top_of_bound ?_ (C + D) ?_
      · exact ((hΛ.mono hm).aestronglyMeasurable.mul hX.1).add
          (((stronglyMeasurable_const.sub hΛ).mono hm).aestronglyMeasurable.mul hY.1)
      · filter_upwards [hpX, hpY, hΛb] with ω hx hy hl
        have hx' := abs_le.1 hx.1
        have hy' := abs_le.1 hy.1
        simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Real.norm_eq_abs]
        rw [abs_le]
        constructor <;> nlinarith [hl.1, hl.2]
    obtain ⟨E, hE0, hintW, hpW⟩ := aux_egcc_props hm γ hγ hWm
    have hf := aux_egcc_sm m P γ X
    have hg := aux_egcc_sm m P γ Y
    have hk0 : StronglyMeasurable[m] (fun ω => Real.exp (-γ *
        (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω))) :=
      (Real.continuous_exp.measurable.comp (((hΛ.measurable.mul hf.measurable).add
        ((measurable_const.sub hΛ.measurable).mul hg.measurable)).const_mul (-γ))).stronglyMeasurable
    have hk1 : StronglyMeasurable[m] (fun ω => Λ ω * Real.exp (-γ * rhoGamma m P γ X ω)) :=
      (hΛ.measurable.mul (Real.continuous_exp.measurable.comp
        (hf.measurable.const_mul (-γ)))).stronglyMeasurable
    have hk2 : StronglyMeasurable[m] (fun ω => (1 - Λ ω) * Real.exp (-γ * rhoGamma m P γ Y ω)) :=
      ((measurable_const.sub hΛ.measurable).mul (Real.continuous_exp.measurable.comp
        (hg.measurable.const_mul (-γ)))).stronglyMeasurable
    have hb0 : ∀ᵐ ω ∂P, ‖Real.exp (-γ *
        (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω))‖ ≤ Real.exp (γ * (C + D)) := by
      filter_upwards [hpX, hpY, hΛb] with ω hx hy hl
      have hx' := abs_le.1 hx.2.2.1
      have hy' := abs_le.1 hy.2.2.1
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.2
      have h1 : -(C + D) ≤ Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω := by
        nlinarith [hl.1, hl.2]
      nlinarith
    have hb1 : ∀ᵐ ω ∂P, ‖Λ ω * Real.exp (-γ * rhoGamma m P γ X ω)‖ ≤ Real.exp (γ * C) := by
      filter_upwards [hpX, hΛb] with ω hx hl
      have hx' := abs_le.1 hx.2.2.1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl.1 (Real.exp_pos _).le)]
      have : Real.exp (-γ * rhoGamma m P γ X ω) ≤ Real.exp (γ * C) :=
        Real.exp_le_exp.2 (by nlinarith)
      nlinarith [Real.exp_pos (-γ * rhoGamma m P γ X ω), hl.1, hl.2]
    have hb2 : ∀ᵐ ω ∂P, ‖(1 - Λ ω) * Real.exp (-γ * rhoGamma m P γ Y ω)‖ ≤ Real.exp (γ * D) := by
      filter_upwards [hpY, hΛb] with ω hy hl
      have hy' := abs_le.1 hy.2.2.1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.2 hl.2) (Real.exp_pos _).le)]
      have : Real.exp (-γ * rhoGamma m P γ Y ω) ≤ Real.exp (γ * D) :=
        Real.exp_le_exp.2 (by nlinarith)
      nlinarith [Real.exp_pos (-γ * rhoGamma m P γ Y ω), hl.1, hl.2]
    have e0 := condExp_stronglyMeasurable_mul_of_bound hm hk0 hintW _ hb0
    have e1 := condExp_stronglyMeasurable_mul_of_bound hm hk1 hintX _ hb1
    have e2 := condExp_stronglyMeasurable_mul_of_bound hm hk2 hintY _ hb2
    have i0 : Integrable ((fun ω => Real.exp (-γ *
        (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω))) *
        fun x => Real.exp (-γ * (Λ * X + (1 - Λ) * Y) x)) P :=
      hintW.bdd_mul (hk0.mono hm).aestronglyMeasurable hb0
    have i1 : Integrable ((fun ω => Λ ω * Real.exp (-γ * rhoGamma m P γ X ω)) *
        fun x => Real.exp (-γ * X x)) P :=
      hintX.bdd_mul (hk1.mono hm).aestronglyMeasurable hb1
    have i2 : Integrable ((fun ω => (1 - Λ ω) * Real.exp (-γ * rhoGamma m P γ Y ω)) *
        fun x => Real.exp (-γ * Y x)) P :=
      hintY.bdd_mul (hk2.mono hm).aestronglyMeasurable hb2
    have eadd := condExp_add (m := m) i1 i2
    have hmono := condExp_mono (m := m) i0 (i1.add i2) (by
      filter_upwards [hΛb] with ω hl
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
      have hc := (convexOn_exp.2 (Set.mem_univ (-γ * rhoGamma m P γ X ω + -γ * X ω))
        (Set.mem_univ (-γ * rhoGamma m P γ Y ω + -γ * Y ω)) hl.1 (sub_nonneg.2 hl.2)
        (by ring))
      simp only [smul_eq_mul] at hc
      calc Real.exp (-γ * (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω)) *
            Real.exp (-γ * (Λ ω * X ω + (1 - Λ ω) * Y ω))
          = Real.exp (Λ ω * (-γ * rhoGamma m P γ X ω + -γ * X ω) +
              (1 - Λ ω) * (-γ * rhoGamma m P γ Y ω + -γ * Y ω)) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := hc
        _ = _ := by rw [Real.exp_add, Real.exp_add]; ring)
    filter_upwards [e0, e1, e2, eadd, hmono, hpX, hpY, hpW, hΛb] with
      ω h0 h1 h2 hadd hle hx hy hw hl
    rw [h0, hadd, Pi.add_apply, h1, h2] at hle
    simp only [Pi.mul_apply] at hle
    have ex : Real.exp (-γ * rhoGamma m P γ X ω) * (P[fun x => Real.exp (-γ * X x) | m]) ω = 1 := by
      rw [← hx.2.2.2, ← Real.exp_add]; simp
    have ey : Real.exp (-γ * rhoGamma m P γ Y ω) * (P[fun x => Real.exp (-γ * Y x) | m]) ω = 1 := by
      rw [← hy.2.2.2, ← Real.exp_add]; simp
    rw [← hw.2.2.2, mul_assoc, ex, mul_assoc, ey, ← Real.exp_add] at hle
    have hle' : -γ * (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω) +
        γ * rhoGamma m P γ (Λ * X + (1 - Λ) * Y) ω ≤ 0 := by
      have : Real.exp (-γ * (Λ ω * rhoGamma m P γ X ω + (1 - Λ ω) * rhoGamma m P γ Y ω) +
        γ * rhoGamma m P γ (Λ * X + (1 - Λ) * Y) ω) ≤ Real.exp 0 := by
        rw [Real.exp_zero]; linarith
      exact Real.exp_le_exp.1 this
    simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply]
    nlinarith
  · filter_upwards with ω
    simp only [rhoGamma, Pi.zero_apply, mul_zero, Real.exp_zero, condExp_const hm, Real.log_one]


-- Source module: Solutions.EntropicDensity

open MeasureTheory Filter Topology Set
namespace CondConvexRisk.Entropic

@[fun_prop]
lemma density_measurable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (Q : PG m P) : Measurable (density m P Q) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma density_nonneg {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (Q : PG m P) (ω : Ω) : 0 ≤ density m P Q ω := ENNReal.toReal_nonneg

lemma density_integrable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (Q : PG m P) : Integrable (density m P Q) P := by
  letI : IsProbabilityMeasure Q.1 := Q.2.1
  exact Measure.integrable_toReal_rnDeriv

lemma integrable_Q_of_memLp {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (Q : PG m P) {f : Ω → ℝ} (hf : MemLp f ⊤ P) : Integrable f Q.1 := by
  letI : IsProbabilityMeasure Q.1 := Q.2.1
  obtain ⟨C, hC0, hC⟩ := aux_egcc_bound hf
  exact Integrable.of_bound (hf.1.mono_ac Q.2.2.1) C
    (Q.2.2.1.ae_le (hC.mono (fun ω hω => by simpa [Real.norm_eq_abs] using hω)))

/-- Change of measure for conditional expectations when the two measures
agree on the conditioning sigma-algebra. -/
lemma condExp_Q_density {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (Q : PG m P) {f : Ω → ℝ} (hf : Integrable f Q.1) :
    Q.1[f | m] =ᵐ[P] P[fun ω => density m P Q ω * f ω | m] := by
  letI : IsProbabilityMeasure Q.1 := Q.2.1
  have hdf : Integrable (fun ω => density m P Q ω * f ω) P :=
    (integrable_toReal_rnDeriv_mul_iff Q.2.2.1).2 hf
  have hqi : Integrable (Q.1[f | m]) P := by
    apply integrable_of_integrable_trim hm
    rw [← aux_cre_trim_eq hm Q]
    exact Integrable.trim hm integrable_condExp stronglyMeasurable_condExp
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hdf
    (fun s _ _ => hqi.integrableOn) ?_ stronglyMeasurable_condExp.aestronglyMeasurable
  intro s hs _
  calc
    ∫ ω in s, Q.1[f | m] ω ∂P = ∫ ω in s, Q.1[f | m] ω ∂P.trim hm :=
      setIntegral_trim hm stronglyMeasurable_condExp hs
    _ = ∫ ω in s, Q.1[f | m] ω ∂Q.1.trim hm := by rw [aux_cre_trim_eq hm Q]
    _ = ∫ ω in s, Q.1[f | m] ω ∂Q.1 := (setIntegral_trim hm stronglyMeasurable_condExp hs).symm
    _ = ∫ ω in s, f ω ∂Q.1 := setIntegral_condExp hm hf hs
    _ = ∫ ω in s, density m P Q ω * f ω ∂P :=
      (setIntegral_rnDeriv_smul Q.2.2.1 (hm s hs)).symm

lemma entropy_negative_integrable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (Q : PG m P) :
    Integrable (fun ω => max (-(density m P Q ω * Real.log (density m P Q ω))) 0) P := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  apply max_le _ (by norm_num)
  have h := Real.self_sub_one_le_mul_log (density_nonneg Q ω)
  linarith [density_nonneg Q ω]

lemma log_density_negative_integrable {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (Q : PG m P) :
    Integrable (fun ω => max (-Real.log (density m P Q ω)) 0) Q.1 := by
  letI : IsProbabilityMeasure Q.1 := Q.2.1
  apply (integrable_toReal_rnDeriv_mul_iff Q.2.2.1).1
  convert entropy_negative_integrable Q using 1
  funext ω
  change density m P Q ω * max (-Real.log (density m P Q ω)) 0 = _
  rw [mul_max_of_nonneg _ _ (density_nonneg Q ω), mul_zero, mul_neg]

lemma density_pos_Q {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (Q : PG m P) :
    ∀ᵐ ω ∂Q.1, 0 < density m P Q ω := by
  letI : IsProbabilityMeasure Q.1 := Q.2.1
  filter_upwards [Measure.rnDeriv_pos Q.2.2.1,
    Q.2.2.1.ae_le (Measure.rnDeriv_lt_top Q.1 P)] with ω hp ht
  exact ENNReal.toReal_pos hp.ne' ht.ne

lemma entropy_young (x u : ℝ) (hx : 0 ≤ x) :
    x * u + x - Real.exp u ≤ x * Real.log x := by
  rcases hx.eq_or_lt with h0 | hp
  · subst x; simp [Real.exp_nonneg]
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u - Real.log x)) hx
  have he : x * Real.exp (u - Real.log x) = Real.exp u := by
    rw [Real.exp_sub, Real.exp_log hp]
    field_simp
  rw [he] at h
  nlinarith

#print axioms condExp_Q_density
#print axioms entropy_negative_integrable
#print axioms log_density_negative_integrable
#print axioms entropy_young
end CondConvexRisk.Entropic


-- Source module: Solutions.EntropicLimits

open MeasureTheory Filter Topology Set
namespace CondConvexRisk.Entropic

/-- Conditional monotone convergence for nonnegative functions. -/
lemma condLExp_iSup {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (P.trim hm)]
    (f : ℕ → Ω → ENNReal) (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    (fun ω => ⨆ n, P⁻[f n | m] ω) =ᵐ[P] P⁻[fun ω => ⨆ n, f n ω | m] := by
  refine ae_eq_condLExp hm P _ (Measurable.iSup (fun n => measurable_condLExp _ _ _)) ?_
  intro s hs
  rw [lintegral_iSup_ae (μ := P.restrict s)
    (f := fun n ω => P⁻[f n | m] ω) (fun n => measurable_condLExp' m P (f n)) ?_]
  · simp_rw [setLIntegral_condLExp hm P _ hs]
    exact (lintegral_iSup hf hmono).symm
  · intro n
    exact ae_restrict_of_ae (condLExp_mono (Eventually.of_forall (hmono (Nat.le_succ n))))

lemma condLExp_tendsto_mono {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (hm : m ≤ mΩ) [SigmaFinite (P.trim hm)]
    (f : ℕ → Ω → ENNReal) (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    ∀ᵐ ω ∂P, Tendsto (fun n => P⁻[f n | m] ω) atTop
      (𝓝 (P⁻[fun ω => ⨆ n, f n ω | m] ω)) := by
  have ha : ∀ᵐ ω ∂P, Monotone (fun n => P⁻[f n | m] ω) := by
    have h : ∀ᵐ ω ∂P, ∀ n k : ℕ, P⁻[f n | m] ω ≤ P⁻[f (n + k) | m] ω :=
      ae_all_iff.2 (fun n => ae_all_iff.2 (fun k =>
      condLExp_mono (P := P) (mΩ := m) (Eventually.of_forall (hmono (Nat.le_add_right n k)))))
    filter_upwards [h] with ω hω
    intro i j hij
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact hω i k
  filter_upwards [ha, condLExp_iSup hm f hf hmono] with ω hω heq
  rw [← heq]
  exact tendsto_atTop_iSup hω

/-- Conditional extended expectations agree with ordinary conditional expectations
on integrable functions. -/
lemma condExpExt_eq_coe {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → ℝ} (hf : Integrable f P) :
    condExpExt m P f =ᵐ[P] fun ω => (P[f | m] ω : EReal) := by
  let fp : Ω → ℝ := fun ω => max (f ω) 0
  let fn : Ω → ℝ := fun ω => max (-f ω) 0
  have hp : Integrable fp P := hf.pos_part
  have hn : Integrable fn P := hf.neg.pos_part
  have hps := condLExp_ofReal m hp (Eventually.of_forall (fun ω => le_max_right _ _))
  have hns := condLExp_ofReal m hn (Eventually.of_forall (fun ω => le_max_right _ _))
  have he : (fun ω => fp ω - fn ω) = f := by funext ω; dsimp [fp, fn]; exact max_zero_sub_max_neg_zero_eq_self _
  have hs := condExp_sub hp hn m
  have hp0 := condExp_nonneg (μ := P) (m := m) (Eventually.of_forall (fun ω => le_max_right (f ω) 0))
  have hn0 := condExp_nonneg (μ := P) (m := m) (Eventually.of_forall (fun ω => le_max_right (-f ω) 0))
  have hpe : (fun ω => ENNReal.ofReal (fp ω)) = fun ω => ENNReal.ofReal (f ω) := by
    funext ω; simp [fp, ENNReal.ofReal_max]
  have hne : (fun ω => ENNReal.ofReal (fn ω)) = fun ω => ENNReal.ofReal (-f ω) := by
    funext ω; simp [fn, ENNReal.ofReal_max]
  rw [hpe] at hps
  rw [hne] at hns
  change P[fun ω => fp ω - fn ω | m] =ᵐ[P] _ at hs
  rw [he] at hs
  filter_upwards [hps, hns, hs, hp0, hn0] with ω hps hns hs hp0 hn0
  change P[f | m] ω = P[fp | m] ω - P[fn | m] ω at hs
  change 0 ≤ P[fp | m] ω at hp0
  change 0 ≤ P[fn | m] ω at hn0
  simp only [condExpExt]
  rw [hps, hns, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
    max_eq_left hp0, max_eq_left hn0, ← EReal.coe_sub, ← hs]

/-- An integrable lower bound remains a lower bound after taking extended
conditional expectation, even if the positive part has infinite expectation. -/
lemma coe_condExp_le_ext {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {f g : Ω → ℝ} (hf : AEMeasurable f P)
    (hfn : Integrable (fun ω => max (-f ω) 0) P) (hg : Integrable g P)
    (hgf : g ≤ᵐ[P] f) :
    (fun ω => (P[g | m] ω : EReal)) ≤ᵐ[P] condExpExt m P f := by
  let fp : Ω → ENNReal := fun ω => ENNReal.ofReal (f ω)
  let fn : Ω → ENNReal := fun ω => ENNReal.ofReal (-f ω)
  let gp : Ω → ENNReal := fun ω => ENNReal.ofReal (g ω)
  let gn : Ω → ENNReal := fun ω => ENNReal.ofReal (-g ω)
  have hcmp : gp + fn ≤ᵐ[P] fp + gn := by
    filter_upwards [hgf] with ω hω
    dsimp [fp, fn, gp, gn]
    have hr : max (g ω) 0 + max (-f ω) 0 ≤ max (f ω) 0 + max (-g ω) 0 := by
      have hf' := max_zero_sub_max_neg_zero_eq_self (f ω)
      have hg' := max_zero_sub_max_neg_zero_eq_self (g ω)
      linarith
    calc
      ENNReal.ofReal (g ω) + ENNReal.ofReal (-f ω) =
          ENNReal.ofReal (max (g ω) 0 + max (-f ω) 0) := by
        rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
        simp
      _ ≤ ENNReal.ofReal (max (f ω) 0 + max (-g ω) 0) := ENNReal.ofReal_le_ofReal hr
      _ = ENNReal.ofReal (f ω) + ENNReal.ofReal (-g ω) := by
        rw [ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
        simp
  have hce := condLExp_mono (mΩ := m) hcmp
  have hleft := condLExp_add_left (mΩ := m) fn hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hright := condLExp_add_left (mΩ := m) gn hf.ennreal_ofReal
  have hgp := condLExp_ofReal m (hg.pos_part)
    (Eventually.of_forall (fun ω => le_max_right (g ω) 0))
  have hgn := condLExp_ofReal m (hg.neg.pos_part)
    (Eventually.of_forall (fun ω => le_max_right (-g ω) 0))
  have hfn' := condLExp_ofReal m hfn
    (Eventually.of_forall (fun ω => le_max_right (-f ω) 0))
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero] at hgp hgn hfn'
  have hgp0 := condExp_nonneg (μ := P) (m := m)
    (Eventually.of_forall (fun ω => le_max_right (g ω) 0))
  have hgn0 := condExp_nonneg (μ := P) (m := m)
    (Eventually.of_forall (fun ω => le_max_right (-g ω) 0))
  have hfn0 := condExp_nonneg (μ := P) (m := m)
    (Eventually.of_forall (fun ω => le_max_right (-f ω) 0))
  have hgsub := condExp_sub (hg.pos_part)
    (hg.neg.pos_part) m
  have hsub : (fun ω => max (g ω) 0 - max (-g ω) 0) = g := by
    funext ω; exact max_zero_sub_max_neg_zero_eq_self _
  change P[fun ω => max (g ω) 0 - max (-g ω) 0 | m] =ᵐ[P] _ at hgsub
  rw [hsub] at hgsub
  simp only [Pi.neg_apply] at hgn hgsub
  filter_upwards [hce, hleft, hright, hgp, hgn, hfn', hgp0, hgn0, hfn0, hgsub]
    with ω hc hl hr hp hn hfn hp0 hn0 hfn0 hsub
  rw [hl, hr] at hc
  have hc' : (P⁻[gp | m] ω : EReal) + (P⁻[fn | m] ω : EReal) ≤
      (P⁻[fp | m] ω : EReal) + (P⁻[gn | m] ω : EReal) := by
    exact_mod_cast hc
  change 0 ≤ P[fun ω => max (g ω) 0 | m] ω at hp0
  change 0 ≤ P[fun ω => max (-g ω) 0 | m] ω at hn0
  change 0 ≤ P[fun ω => max (-f ω) 0 | m] ω at hfn0
  change P⁻[gp | m] ω = _ at hp
  change P⁻[gn | m] ω = _ at hn
  change P⁻[fn | m] ω = _ at hfn
  have ep : (P⁻[gp | m] ω : EReal) = (P[fun ω => max (g ω) 0 | m] ω : EReal) := by
    rw [hp, EReal.coe_ennreal_ofReal, max_eq_left hp0]
  have en : (P⁻[gn | m] ω : EReal) = (P[fun ω => max (-g ω) 0 | m] ω : EReal) := by
    rw [hn, EReal.coe_ennreal_ofReal, max_eq_left hn0]
  have ef : (P⁻[fn | m] ω : EReal) = (P[fun ω => max (-f ω) 0 | m] ω : EReal) := by
    rw [hfn, EReal.coe_ennreal_ofReal, max_eq_left hfn0]
  change P[g | m] ω = P[fun ω => max (g ω) 0 | m] ω -
    P[fun ω => max (-g ω) 0 | m] ω at hsub
  rw [ep, en, ef] at hc'
  have he : (P[g | m] ω : EReal) + (P[fun ω => max (-f ω) 0 | m] ω : EReal) +
      (P[fun ω => max (-g ω) 0 | m] ω : EReal) =
      (P[fun ω => max (g ω) 0 | m] ω : EReal) +
        (P[fun ω => max (-f ω) 0 | m] ω : EReal) := by
    rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
    congr 1; linarith
  have hc'' := (EReal.addLECancellable_coe (P[fun ω => max (-g ω) 0 | m] ω)).add_le_add_iff_right.1
    (he.symm ▸ hc')
  change (P[g | m] ω : EReal) ≤ (P⁻[fp | m] ω : EReal) - (P⁻[fn | m] ω : EReal)
  rw [ef]
  exact (EReal.le_sub_iff_add_le (a := (P[g | m] ω : EReal))
    (c := (P⁻[fp | m] ω : EReal))
    (b := (P[fun ω => max (-f ω) 0 | m] ω : EReal))
    (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2 hc''

#print axioms coe_condExp_le_ext
#print axioms condLExp_iSup
#print axioms condLExp_tendsto_mono
#print axioms condExpExt_eq_coe
end CondConvexRisk.Entropic


-- Source module: Solutions.EntropicUpper

open MeasureTheory Filter Topology Set
namespace CondConvexRisk.Entropic

lemma exp_condExp_properties {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) (Z : LInf P) :
    ∃ C : ℝ, 0 ≤ C ∧ Integrable (fun ω => Real.exp (Z.1 ω)) P ∧
      ∀ᵐ ω ∂P, |Z.1 ω| ≤ C ∧ 0 < P[fun x => Real.exp (Z.1 x) | m] ω ∧
        |Real.log (P[fun x => Real.exp (Z.1 x) | m] ω)| ≤ C := by
  obtain ⟨C, hC0, hi, ha⟩ := aux_egcc_props hm 1 (by norm_num) Z.2.neg
  refine ⟨C, hC0, ?_, ?_⟩
  · simpa using hi
  · filter_upwards [ha] with ω hω
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Pi.neg_apply, abs_neg] using hω.1
    · simpa only [Pi.neg_apply, neg_one_mul, neg_neg] using hω.2.1
    · simpa only [rhoGamma, inv_one, one_mul, Pi.neg_apply, neg_one_mul, neg_neg] using hω.2.2.1

/-- Conditional Gibbs inequality with extended-valued entropy. -/
lemma dvFamily_le_entropy {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) (Q : PG m P) (Z : LInf P) :
    dvFamily m P Q Z ≤ᵐ[P] condRelEntropy m P Q := by
  letI : IsProbabilityMeasure Q.1 := Q.2.1
  let φ := density m P Q
  let A : Ω → ℝ := P[fun ω => Real.exp (Z.1 ω) | m]
  let B : Ω → ℝ := fun ω => Real.log (A ω)
  let D : Ω → ℝ := fun ω => (A ω)⁻¹
  have hφ : Integrable φ P := density_integrable Q
  have hZi : Integrable Z.1 Q.1 := integrable_Q_of_memLp Q Z.2
  have hφZ : Integrable (fun ω => φ ω * Z.1 ω) P :=
    (integrable_toReal_rnDeriv_mul_iff Q.2.2.1).2 hZi
  obtain ⟨C, hC0, hExp, hprops⟩ := exp_condExp_properties hm Z
  have hBsm : StronglyMeasurable[m] B :=
    (Real.measurable_log.comp stronglyMeasurable_condExp.measurable).stronglyMeasurable
  have hDsm : StronglyMeasurable[m] D := by
    exact (measurable_inv.comp stronglyMeasurable_condExp.measurable).stronglyMeasurable
  have hφB : Integrable (fun ω => B ω * φ ω) P := hφ.bdd_mul
    (hBsm.mono hm).aestronglyMeasurable (hprops.mono (fun ω hω => by
      simpa [B, A, Real.norm_eq_abs] using hω.2.2))
  have hDb : ∀ᵐ ω ∂P, ‖D ω‖ ≤ Real.exp C := by
    filter_upwards [hprops] with ω hω
    dsimp [D, A]
    rw [abs_of_pos (inv_pos.2 hω.2.1),
      ← Real.exp_log hω.2.1, ← Real.exp_neg]
    apply Real.exp_le_exp.2
    linarith [(abs_le.1 hω.2.2).1]
  have hDexp : Integrable (fun ω => D ω * Real.exp (Z.1 ω)) P :=
    hExp.bdd_mul (hDsm.mono hm).aestronglyMeasurable hDb
  let g : Ω → ℝ := fun ω => φ ω * Z.1 ω - B ω * φ ω + φ ω - D ω * Real.exp (Z.1 ω)
  have hgi : Integrable g P := ((hφZ.sub hφB).add hφ).sub hDexp
  have hgEntropy : g ≤ᵐ[P] fun ω => φ ω * Real.log (φ ω) := by
    filter_upwards [hprops] with ω hω
    have hh := entropy_young (φ ω) (Z.1 ω - B ω) (density_nonneg Q ω)
    have he : Real.exp (Z.1 ω - B ω) = D ω * Real.exp (Z.1 ω) := by
      dsimp [B, D]
      rw [Real.exp_sub, Real.exp_log hω.2.1]
      ring
    rw [he] at hh
    dsimp [g]; nlinarith
  have hext := coe_condExp_le_ext (m := m)
    (f := fun ω => φ ω * Real.log (φ ω)) (by fun_prop)
    (entropy_negative_integrable Q) hgi hgEntropy
  have hceZ := condExp_Q_density hm Q hZi
  have hceB := condExp_mul_of_stronglyMeasurable_left (μ := P) hBsm hφB hφ
  have hceD := condExp_mul_of_stronglyMeasurable_left (μ := P) hDsm hDexp hExp
  have hmean := (condRelEntropy_eq_condExp_log_accepted hm Q).1
  have hceSub := condExp_sub hφZ hφB m
  have hceAdd := condExp_add (hφZ.sub hφB) hφ m
  have hceAll := condExp_sub ((hφZ.sub hφB).add hφ) hDexp m
  filter_upwards [hext, hceZ, hceB, hceD, hmean, hceSub, hceAdd, hceAll, hprops]
    with ω hh hZ hB hD hmean hsub hadd hall hp
  change (P[g | m] ω : EReal) ≤ condRelEntropy m P Q ω at hh
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.one_apply] at hsub hadd hall hB hD hmean
  change Q.1[Z.1 | m] ω = P[fun ω => φ ω * Z.1 ω | m] ω at hZ
  change P[φ | m] ω = 1 at hmean
  change P[fun ω => B ω * φ ω | m] ω = B ω * P[φ | m] ω at hB
  change P[fun ω => D ω * Real.exp (Z.1 ω) | m] ω = D ω * A ω at hD
  have hgCE : P[g | m] ω = Q.1[Z.1 | m] ω - B ω := by
    dsimp [g] at hall ⊢
    change P[g | m] ω = _ at hall
    rw [hall, hadd, hsub, ← hZ, hB, hD, hmean]
    dsimp [D, A, B]
    rw [inv_mul_cancel₀ hp.2.1.ne']
    ring
  rw [hgCE] at hh
  exact hh

#print axioms dvFamily_le_entropy
end CondConvexRisk.Entropic


-- Source module: Solutions.EntropicTruncation

open MeasureTheory Filter Topology Set
namespace CondConvexRisk.Entropic

noncomputable def clippedLog (n k : ℕ) (x : ℝ) : ℝ :=
  min (Real.log (max (Real.exp (-(k : ℝ))) x)) (n : ℝ)

lemma clippedLog_bounds (n k : ℕ) (x : ℝ) :
    -(k : ℝ) ≤ clippedLog n k x ∧ clippedLog n k x ≤ n := by
  constructor
  · apply le_min
    · calc
        -(k : ℝ) = Real.log (Real.exp (-(k : ℝ))) := (Real.log_exp _).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos _) (le_max_left _ _)
    · linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) n]
  · exact min_le_right _ _

lemma exp_clippedLog_le (n k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (clippedLog n k x) ≤ x + Real.exp (-(k : ℝ)) := by
  calc
    Real.exp (clippedLog n k x) ≤ Real.exp (Real.log (max (Real.exp (-(k : ℝ))) x)) :=
      Real.exp_le_exp.2 (min_le_left _ _)
    _ = max (Real.exp (-(k : ℝ))) x := Real.exp_log (lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _))
    _ ≤ x + Real.exp (-(k : ℝ)) := max_le (by linarith) (by linarith [Real.exp_pos (-(k : ℝ))])

lemma clippedLog_lower (n k : ℕ) (x : ℝ) (hx : 0 < x) :
    min (max (Real.log x) 0) (n : ℝ) - max (-Real.log x) 0 ≤ clippedLog n k x := by
  have hlog : Real.log x ≤ Real.log (max (Real.exp (-(k : ℝ))) x) :=
    Real.log_le_log hx (le_max_right _ _)
  by_cases hl : 0 ≤ Real.log x
  · rw [max_eq_left hl, max_eq_right (neg_nonpos.2 hl), sub_zero]
    exact min_le_min hlog le_rfl
  · have hl' : Real.log x ≤ 0 := le_of_not_ge hl
    rw [max_eq_right hl', min_eq_left (Nat.cast_nonneg n), max_eq_left (neg_nonneg.2 hl')]
    simp only [zero_sub, neg_neg]
    exact le_min hlog (hl'.trans (Nat.cast_nonneg n))

@[fun_prop]
lemma clippedLog_measurable (n k : ℕ) : Measurable (clippedLog n k) := by
  unfold clippedLog; fun_prop

lemma clippedLog_memLp {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (Q : PG m P) (n k : ℕ) :
    MemLp (fun ω => clippedLog n k (density m P Q ω)) ⊤ P := by
  apply memLp_top_of_bound ((clippedLog_measurable n k).comp (density_measurable Q)).aestronglyMeasurable (max (n : ℝ) (k : ℝ))
  filter_upwards [] with ω
  change |clippedLog n k (density m P Q ω)| ≤ max (n : ℝ) (k : ℝ)
  rw [abs_le]
  obtain ⟨hlo, hhi⟩ := clippedLog_bounds n k (density m P Q ω)
  constructor
  · linarith [le_max_right (n : ℝ) (k : ℝ)]
  · exact hhi.trans (le_max_left _ _)

lemma positive_log_clip_memLp {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (Q : PG m P) (n : ℕ) :
    MemLp (fun ω => min (max (Real.log (density m P Q ω)) 0) (n : ℝ)) ⊤ P := by
  apply memLp_top_of_bound (((Real.measurable_log.comp (density_measurable Q)).max measurable_const).min measurable_const).aestronglyMeasurable (n : ℝ)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) (Nat.cast_nonneg n))]
  exact min_le_right _ _

lemma Q_ae_le_to_P {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (Q : PG m P) {f g : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
    (hfg : f ≤ᵐ[Q.1] g) : f ≤ᵐ[P] g := by
  have hs : MeasurableSet[m] {ω | ¬ f ω ≤ g ω} := (measurableSet_le hf.measurable hg.measurable).compl
  rw [Filter.EventuallyLE, ae_iff] at hfg ⊢
  rw [← Q.2.2.2 _ hs]
  exact hfg

/-- The lower truncation error can be removed independently of the upper truncation. -/
lemma clipped_dv_lower {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) (Q : PG m P) (n k : ℕ) :
    (fun ω => ((Q.1[fun x => min (max (Real.log (density m P Q x)) 0) (n : ℝ) | m] ω -
      Q.1[fun x => max (-Real.log (density m P Q x)) 0 | m] ω -
      Real.log (1 + Real.exp (-(k : ℝ))) : ℝ) : EReal)) ≤ᵐ[P]
    dvFamily m P Q ⟨fun ω => clippedLog n k (density m P Q ω), clippedLog_memLp Q n k⟩ := by
  letI : IsProbabilityMeasure Q.1 := Q.2.1
  let Z : LInf P := ⟨fun ω => clippedLog n k (density m P Q ω), clippedLog_memLp Q n k⟩
  let f : Ω → ℝ := fun ω => min (max (Real.log (density m P Q ω)) 0) (n : ℝ)
  let g : Ω → ℝ := fun ω => max (-Real.log (density m P Q ω)) 0
  have hfi : Integrable f Q.1 := integrable_Q_of_memLp Q (positive_log_clip_memLp Q n)
  have hgi : Integrable g Q.1 := log_density_negative_integrable Q
  have hZi : Integrable Z.1 Q.1 := integrable_Q_of_memLp Q Z.2
  have hce : Q.1[f - g | m] ≤ᵐ[Q.1] Q.1[Z.1 | m] := by
    apply condExp_mono (hfi.sub hgi) hZi
    filter_upwards [density_pos_Q Q] with ω hω
    exact clippedLog_lower n k _ hω
  have hsub := condExp_sub hfi hgi m
  have hceP : Q.1[f | m] - Q.1[g | m] ≤ᵐ[P] Q.1[Z.1 | m] := by
    apply Q_ae_le_to_P Q (stronglyMeasurable_condExp.sub stronglyMeasurable_condExp)
      stronglyMeasurable_condExp
    filter_upwards [hce, hsub] with ω ha hb
    rw [hb] at ha
    exact ha
  have hφ : Integrable (density m P Q) P := density_integrable Q
  have hExpi : Integrable (fun ω => Real.exp (Z.1 ω)) P := by
    apply Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable Z.2.1) (Real.exp (n : ℝ))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (clippedLog_bounds n k _).2
  have hupper := condExp_mono (m := m) hExpi
    (hφ.add (integrable_const (Real.exp (-(k : ℝ)))))
    (Eventually.of_forall (fun ω => exp_clippedLog_le n k _ (density_nonneg Q ω)))
  have hadd := condExp_add hφ (integrable_const (Real.exp (-(k : ℝ)))) m
  have hmean := (condRelEntropy_eq_condExp_log_accepted hm Q).1
  have hlo := condExp_mono (m := m) (integrable_const (Real.exp (-(k : ℝ)))) hExpi
    (Eventually.of_forall (fun ω => Real.exp_le_exp.2 (clippedLog_bounds n k _).1))
  rw [condExp_const hm] at hlo
  filter_upwards [hceP, hupper, hadd, hmean, hlo] with ω hce hu ha hm' hl
  rw [ha] at hu
  simp only [Pi.add_apply, Pi.one_apply] at hu hm'
  rw [hm', condExp_const hm] at hu
  have hpos : 0 < P[fun x => Real.exp (Z.1 x) | m] ω := (Real.exp_pos _).trans_le hl
  have hlog := Real.log_le_log hpos hu
  change ((Q.1[f | m] ω - Q.1[g | m] ω - Real.log (1 + Real.exp (-(k : ℝ))) : ℝ) : EReal) ≤
    ((Q.1[Z.1 | m] ω - Real.log (P[fun x => Real.exp (Z.1 x) | m] ω) : ℝ) : EReal)
  apply EReal.coe_le_coe_iff.2
  change Q.1[f | m] ω - Q.1[g | m] ω ≤ Q.1[Z.1 | m] ω at hce
  linarith

#print axioms clipped_dv_lower
end CondConvexRisk.Entropic


-- Source module: Solutions.EntropicLower

open MeasureTheory Filter Topology Set
namespace CondConvexRisk.Entropic

lemma Q_ae_eq_to_P {Ω β : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace β] [MeasurableEq β] {P : Measure Ω} (Q : PG m P) {f g : Ω → β}
    (hf : Measurable[m] f) (hg : Measurable[m] g) (hfg : f =ᵐ[Q.1] g) : f =ᵐ[P] g := by
  have hs : MeasurableSet[m] {ω | ¬ f ω = g ω} := (measurableSet_eq_fun hf hg).compl
  rw [Filter.EventuallyEq, ae_iff] at hfg ⊢
  rw [← Q.2.2.2 _ hs]
  exact hfg

lemma log_error_tendsto :
    Tendsto (fun k : ℕ => Real.log (1 + Real.exp (-(k : ℝ)))) atTop (𝓝 0) := by
  have he : Tendsto (fun k : ℕ => Real.exp (-(k : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun k : ℕ => 1 + Real.exp (-(k : ℝ))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add he
  simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1

/-- Any a.s. upper bound of the bounded variational family bounds conditional entropy. -/
lemma entropy_le_dv_upper {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) (Q : PG m P)
    (W : Ω → EReal) (hW : ∀ Z : LInf P, dvFamily m P Q Z ≤ᵐ[P] W) :
    condRelEntropy m P Q ≤ᵐ[P] W := by
  letI : IsProbabilityMeasure Q.1 := Q.2.1
  let L : Ω → ℝ := fun ω => Real.log (density m P Q ω)
  let b : Ω → ℝ := fun ω => max (-L ω) 0
  let a : ℕ → Ω → ℝ := fun n ω => min (max (L ω) 0) (n : ℝ)
  let F : ℕ → Ω → ENNReal := fun n ω => ENNReal.ofReal (a n ω)
  have ha_meas : ∀ n, Measurable (a n) := by intro n; dsimp [a, L]; fun_prop
  have ha_int : ∀ n, Integrable (a n) Q.1 := fun n =>
    integrable_Q_of_memLp Q (positive_log_clip_memLp Q n)
  have hb_int : Integrable b Q.1 := log_density_negative_integrable Q
  have hmono : Monotone F := by
    intro i j hij ω
    apply ENNReal.ofReal_le_ofReal
    exact min_le_min le_rfl (Nat.cast_le.2 hij)
  have hsup : (fun ω => ⨆ n, F n ω) = fun ω => ENNReal.ofReal (L ω) := by
    funext ω
    apply le_antisymm
    · apply iSup_le
      intro n
      exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_eq (by simp)
    · obtain ⟨n, hn⟩ := exists_nat_ge (max (L ω) 0)
      apply le_iSup_of_le n
      dsimp [F, a]
      rw [min_eq_left hn]
      simp
  have hsupQ := condLExp_iSup hm (P := Q.1) F
    (fun n => (ha_meas n).ennreal_ofReal) hmono
  rw [hsup] at hsupQ
  have hsupP : (fun ω => ⨆ n, Q.1⁻[F n | m] ω) =ᵐ[P]
      Q.1⁻[fun ω => ENNReal.ofReal (L ω) | m] := by
    exact Q_ae_eq_to_P Q (Measurable.iSup (fun n => measurable_condLExp _ _ _))
      (measurable_condLExp _ _ _) hsupQ
  have ha0Q : ∀ n, 0 ≤ᵐ[Q.1] Q.1[a n | m] := fun n => condExp_nonneg
    (Eventually.of_forall (fun ω => le_min (le_max_right _ _) (Nat.cast_nonneg n)))
  have ha0P : ∀ n, 0 ≤ᵐ[P] Q.1[a n | m] := fun n =>
    Q_ae_le_to_P Q stronglyMeasurable_const stronglyMeasurable_condExp (ha0Q n)
  have hbridgeQ : ∀ n, Q.1⁻[F n | m] =ᵐ[Q.1] fun ω => ENNReal.ofReal (Q.1[a n | m] ω) :=
    fun n => condLExp_ofReal m (ha_int n)
      (Eventually.of_forall (fun ω => le_min (le_max_right _ _) (Nat.cast_nonneg n)))
  have hbridgeP : ∀ n, Q.1⁻[F n | m] =ᵐ[P] fun ω => ENNReal.ofReal (Q.1[a n | m] ω) :=
    fun n => Q_ae_eq_to_P Q (measurable_condLExp _ _ _)
      (stronglyMeasurable_condExp.measurable.ennreal_ofReal) (hbridgeQ n)
  have hbbridgeQ : Q.1⁻[fun ω => ENNReal.ofReal (-L ω) | m] =ᵐ[Q.1]
      fun ω => ENNReal.ofReal (Q.1[b | m] ω) := by
    have h := condLExp_ofReal m hb_int (Eventually.of_forall (fun ω => le_max_right (-L ω) 0))
    simpa [b, ENNReal.ofReal_max] using h
  have hbbridgeP : Q.1⁻[fun ω => ENNReal.ofReal (-L ω) | m] =ᵐ[P]
      fun ω => ENNReal.ofReal (Q.1[b | m] ω) :=
    Q_ae_eq_to_P Q (measurable_condLExp _ _ _)
      (stronglyMeasurable_condExp.measurable.ennreal_ofReal) hbbridgeQ
  have hb0P : 0 ≤ᵐ[P] Q.1[b | m] := Q_ae_le_to_P Q stronglyMeasurable_const
    stronglyMeasurable_condExp (condExp_nonneg (Eventually.of_forall (fun ω => le_max_right (-L ω) 0)))
  have hnk : ∀ n k : ℕ, (fun ω => ((Q.1[a n | m] ω - Q.1[b | m] ω -
      Real.log (1 + Real.exp (-(k : ℝ))) : ℝ) : EReal)) ≤ᵐ[P] W := by
    intro n k
    exact (clipped_dv_lower hm Q n k).trans
      (hW ⟨fun ω => clippedLog n k (density m P Q ω), clippedLog_memLp Q n k⟩)
  have hn : ∀ n, (fun ω => ((Q.1[a n | m] ω - Q.1[b | m] ω : ℝ) : EReal)) ≤ᵐ[P] W := by
    intro n
    filter_upwards [ae_all_iff.2 (hnk n)] with ω hω
    have ht : Tendsto (fun k : ℕ => ((Q.1[a n | m] ω - Q.1[b | m] ω -
        Real.log (1 + Real.exp (-(k : ℝ))) : ℝ) : EReal)) atTop
        (𝓝 ((Q.1[a n | m] ω - Q.1[b | m] ω : ℝ) : EReal)) := by
      exact EReal.tendsto_coe.2 (by simpa using tendsto_const_nhds.sub log_error_tendsto)
    exact le_of_tendsto ht (Eventually.of_forall hω)
  have hentropy := (condRelEntropy_eq_condExp_log_accepted hm Q).2
  filter_upwards [hentropy, hsupP, ae_all_iff.2 hbridgeP, ae_all_iff.2 ha0P,
    hbbridgeP, hb0P, ae_all_iff.2 hn] with ω he hs hbridge ha0 hb hb0 hn
  change ∀ n, 0 ≤ Q.1[a n | m] ω at ha0
  change 0 ≤ Q.1[b | m] ω at hb0
  let C : EReal := W ω + (Q.1[b | m] ω : EReal)
  have haC : ∀ n, (Q.1⁻[F n | m] ω : EReal) ≤ C := by
    intro n
    rw [hbridge n, EReal.coe_ennreal_ofReal, max_eq_left (ha0 n)]
    dsimp [C]
    have h := hn n
    rw [EReal.coe_sub] at h
    exact (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
      (.inl (EReal.coe_ne_top _))).1 h
  have hC0 : 0 ≤ C := (EReal.coe_ennreal_nonneg _).trans (haC 0)
  have hsupC : (Q.1⁻[fun ω => ENNReal.ofReal (L ω) | m] ω : EReal) ≤ C := by
    have hnn : ∀ n, Q.1⁻[F n | m] ω ≤ C.toENNReal := by
      intro n
      simpa using EReal.toENNReal_le_toENNReal (haC n)
    have hh : (⨆ n, Q.1⁻[F n | m] ω) ≤ C.toENNReal := iSup_le hnn
    rw [hs] at hh
    have hh' := EReal.coe_ennreal_le_coe_ennreal_iff.2 hh
    rw [EReal.coe_toENNReal hC0] at hh'
    exact hh'
  rw [he]
  change (Q.1⁻[fun ω => ENNReal.ofReal (L ω) | m] ω : EReal) -
    (Q.1⁻[fun ω => ENNReal.ofReal (-L ω) | m] ω : EReal) ≤ W ω
  rw [hb, EReal.coe_ennreal_ofReal, max_eq_left hb0]
  exact (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _))).2 hsupC

#print axioms entropy_le_dv_upper
end CondConvexRisk.Entropic


-- Source module: Solutions.EntropicDV

open MeasureTheory
namespace CondConvexRisk.Entropic

theorem conditional_donsker_varadhan_complete {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (Q : PG m P) :
    IsEssSup P (dvFamily m P Q) (condRelEntropy m P Q) := by
  refine ⟨?_, dvFamily_le_entropy hm Q, fun W _ hW => entropy_le_dv_upper hm Q W hW⟩
  unfold condRelEntropy condExpExt
  fun_prop

#print axioms conditional_donsker_varadhan_complete
end CondConvexRisk.Entropic


-- Source module: Solutions.EntropicTilt

open MeasureTheory Filter Topology Set
namespace CondConvexRisk.Entropic

/-- The bounded Gibbs tilt agrees with the reference measure on the conditioning
sigma-algebra and attains the entropy variational bound. -/
lemma exists_gibbs_tilt {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) (Z : LInf P) :
    ∃ Q : PG m P, condRelEntropy m P Q =ᵐ[P]
      fun ω => ((Q.1[Z.1 | m] ω - Real.log (P[fun x => Real.exp (Z.1 x) | m] ω) : ℝ) : EReal) := by
  let A : Ω → ℝ := P[fun ω => Real.exp (Z.1 ω) | m]
  let B : Ω → ℝ := fun ω => Real.log (A ω)
  let D : Ω → ℝ := fun ω => (A ω)⁻¹
  let f : Ω → ℝ := fun ω => D ω * Real.exp (Z.1 ω)
  obtain ⟨C, hC0, hExp, hprops⟩ := exp_condExp_properties hm Z
  have hBsm : StronglyMeasurable[m] B :=
    (Real.measurable_log.comp stronglyMeasurable_condExp.measurable).stronglyMeasurable
  have hDsm : StronglyMeasurable[m] D :=
    (measurable_inv.comp stronglyMeasurable_condExp.measurable).stronglyMeasurable
  have hDb : ∀ᵐ ω ∂P, ‖D ω‖ ≤ Real.exp C := by
    filter_upwards [hprops] with ω hω
    change |(A ω)⁻¹| ≤ Real.exp C
    rw [abs_of_pos (inv_pos.2 hω.2.1), ← Real.exp_log hω.2.1, ← Real.exp_neg]
    apply Real.exp_le_exp.2
    linarith [(abs_le.1 hω.2.2).1]
  have hfi : Integrable f P := hExp.bdd_mul (hDsm.mono hm).aestronglyMeasurable hDb
  have hfpos : ∀ᵐ ω ∂P, 0 < f ω := by
    filter_upwards [hprops] with ω hω
    exact mul_pos (inv_pos.2 hω.2.1) (Real.exp_pos _)
  have hce : P[f | m] =ᵐ[P] 1 := by
    have h := condExp_mul_of_stronglyMeasurable_left (μ := P) hDsm hfi hExp
    filter_upwards [h, hprops] with ω hω hp
    change P[f | m] ω = D ω * A ω at hω
    rw [hω]
    exact inv_mul_cancel₀ hp.2.1.ne'
  let q := P.withDensity (fun ω => ENNReal.ofReal (f ω))
  have hon : ∀ s, MeasurableSet[m] s → q s = P s := by
    intro s hs
    have hcle := condLExp_ofReal m hfi (hfpos.mono (fun ω hω => hω.le))
    have hcone : P⁻[fun ω => ENNReal.ofReal (f ω) | m] =ᵐ[P] 1 := by
      filter_upwards [hcle, hce] with ω h1 h2
      rw [h1, h2]
      simp
    calc
      q s = ∫⁻ ω in s, ENNReal.ofReal (f ω) ∂P := withDensity_apply _ (hm s hs)
      _ = ∫⁻ ω in s, P⁻[fun ω => ENNReal.ofReal (f ω) | m] ω ∂P :=
        (setLIntegral_condLExp hm P _ hs).symm
      _ = ∫⁻ ω in s, (1 : ENNReal) ∂P := lintegral_congr_ae (ae_restrict_of_ae hcone)
      _ = P s := by simp
  have hqprob : IsProbabilityMeasure q := ⟨by rw [hon univ MeasurableSet.univ, measure_univ]⟩
  let Q : PG m P := ⟨q, hqprob, withDensity_absolutelyContinuous _ _, hon⟩
  letI : IsProbabilityMeasure Q.1 := hqprob
  have hdensity : density m P Q =ᵐ[P] f := by
    have h := Measure.rnDeriv_withDensity₀ P hfi.1.aemeasurable.ennreal_ofReal
    filter_upwards [h, hfpos] with ω hω hp
    change (q.rnDeriv P ω).toReal = f ω
    rw [hω, ENNReal.toReal_ofReal hp.le]
  have hlog : (fun ω => Real.log (density m P Q ω)) =ᵐ[P] Z.1 - B := by
    filter_upwards [hdensity, hprops] with ω hφ hp
    rw [hφ]
    dsimp [f, D, B]
    rw [Real.log_mul (inv_ne_zero hp.2.1.ne') (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
    ring
  have hBtop : MemLp B ⊤ P := memLp_top_of_bound (hBsm.mono hm).aestronglyMeasurable C
    (hprops.mono (fun ω hω => by simpa [B, A, Real.norm_eq_abs] using hω.2.2))
  have hZi : Integrable Z.1 Q.1 := integrable_Q_of_memLp Q Z.2
  have hBi : Integrable B Q.1 := integrable_Q_of_memLp Q hBtop
  have hlogQ : (fun ω => Real.log (density m P Q ω)) =ᵐ[Q.1] Z.1 - B := Q.2.2.1.ae_le hlog
  have hlogi : Integrable (fun ω => Real.log (density m P Q ω)) Q.1 :=
    (hZi.sub hBi).congr (Filter.EventuallyEq.symm hlogQ)
  have hext := condExpExt_eq_coe (m := m) hlogi
  have hextP := Q_ae_eq_to_P Q (by unfold condExpExt; fun_prop)
    (by fun_prop) hext
  have hlogCEQ := (condExp_congr_ae (m := m) hlogQ).trans (condExp_sub hZi hBi m)
  rw [condExp_of_stronglyMeasurable hm hBsm hBi] at hlogCEQ
  have hlogCEP := aux_mpdv_QP Q stronglyMeasurable_condExp
    (stronglyMeasurable_condExp.sub hBsm) hlogCEQ
  refine ⟨Q, ?_⟩
  have he := (condRelEntropy_eq_condExp_log_accepted hm Q).2
  filter_upwards [he, hextP, hlogCEP] with ω h1 h2 h3
  rw [h1, h2, h3]
  rfl

#print axioms exists_gibbs_tilt
end CondConvexRisk.Entropic


-- Source module: Solutions.EntropicRepresentation

open MeasureTheory Filter
namespace CondConvexRisk.Entropic

lemma entropic_family_le {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) (γ : ℝ) (hγ : 0 < γ)
    (X : Ω → ℝ) (hX : MemLp X ⊤ P) (Q : PG m P) :
    entropicReprFamily m P γ X Q ≤ᵐ[P] fun ω => (rhoGamma m P γ X ω : EReal) := by
  have hmin := (minimalPenalty_rhoGamma_eq_dv_accepted hm γ hγ Q
    (condRelEntropy m P Q)).1 (conditional_donsker_varadhan_complete hm Q)
  have hp := hmin.2.1 ⟨X, hX⟩
  filter_upwards [hp] with ω hω
  change ((-Q.1[X | m] ω - rhoGamma m P γ X ω : ℝ) : EReal) ≤
    ((γ⁻¹ : ℝ) : EReal) * condRelEntropy m P Q ω at hω
  rw [EReal.coe_sub] at hω
  have hh := (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _))
    (.inl (EReal.coe_ne_top _))).1 hω
  change ((-Q.1[X | m] ω : ℝ) : EReal) - ((γ⁻¹ : ℝ) : EReal) *
    condRelEntropy m P Q ω ≤ (rhoGamma m P γ X ω : EReal)
  apply (EReal.sub_le_iff_le_add (.inr (EReal.coe_ne_top _))
    (.inr (EReal.coe_ne_bot _))).2
  simpa only [add_comm] using hh

lemma entropic_family_attains {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ) (γ : ℝ) (hγ : 0 < γ)
    (X : Ω → ℝ) (hX : MemLp X ⊤ P) :
    ∃ Q : PG m P, entropicReprFamily m P γ X Q =ᵐ[P]
      fun ω => (rhoGamma m P γ X ω : EReal) := by
  let Z : LInf P := ⟨fun ω => -γ * X ω, hX.const_mul (-γ)⟩
  obtain ⟨Q, hQ⟩ := exists_gibbs_tilt hm Z
  have hce : Q.1[Z.1 | m] =ᵐ[P] fun ω => -γ * Q.1[X | m] ω := by
    apply aux_mpdv_QP Q stronglyMeasurable_condExp (stronglyMeasurable_condExp.const_mul (-γ))
    exact condExp_smul (-γ) X m
  refine ⟨Q, ?_⟩
  filter_upwards [hQ, hce] with ω hH hCE
  simp only [entropicReprFamily]
  rw [hH, hCE, ← EReal.coe_mul, ← EReal.coe_sub]
  unfold rhoGamma
  congr 1
  dsimp [Z]
  field_simp
  <;> ring

 theorem entropic_representation_complete {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) :
    (∀ X : Ω → ℝ, MemLp X ⊤ P →
      IsEssSup P (entropicReprFamily m P γ X) (fun ω => ((rhoGamma m P γ X ω : ℝ) : EReal))) ∧
    IsMinimalPenalty m P (rhoGamma m P γ)
      (fun Q ω => ((γ⁻¹ : ℝ) : EReal) * condRelEntropy m P Q ω) := by
  constructor
  · intro X hX
    refine ⟨?_, entropic_family_le hm γ hγ X hX, ?_⟩
    · exact (aux_egcc_sm m P γ X).measurable.mono hm le_rfl |>.aemeasurable.coe_real_ereal
    · intro W hW hupper
      obtain ⟨Q, hQ⟩ := entropic_family_attains hm γ hγ X hX
      exact hQ.symm.le.trans (hupper Q)
  · intro Q
    exact (minimalPenalty_rhoGamma_eq_dv_accepted hm γ hγ Q (condRelEntropy m P Q)).1
      (conditional_donsker_varadhan_complete hm Q)

#print axioms entropic_representation_complete
end CondConvexRisk.Entropic

open MeasureTheory CondConvexRisk.Entropic

theorem solution {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) :
    (∀ X : Ω → ℝ, MemLp X ⊤ P →
      IsEssSup P (entropicReprFamily m P γ X) (fun ω => ((rhoGamma m P γ X ω : ℝ) : EReal))) ∧
    IsMinimalPenalty m P (rhoGamma m P γ)
      (fun Q ω => ((γ⁻¹ : ℝ) : EReal) * condRelEntropy m P Q ω) :=
  CondConvexRisk.Entropic.entropic_representation_complete hm γ hγ

#check solution
#print axioms solution
