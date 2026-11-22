-- Prove2me | solution 1 for ChanceStateCtrl.AlmostSure.theorem_3_9_existence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:07:55.320874+00:00
-- url     : https://prove2.me/submissions/dd71fbb0-3268-47c6-b33d-bcc3fd4ede7b

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace ChanceStateCtrl.AlmostSure.Thm39Aux

section IndicatorProjection

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Multiplication by the indicator of a measurable set `A` as a continuous linear map on `L∞`. -/
noncomputable def indCLM (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    Lp X ⊤ P →L[ℝ] Lp X ⊤ P :=
  LinearMap.mkContinuous
    { toFun := fun y => ((Lp.memLp y).indicator hA).toLp (A.indicator y)
      map_add' := fun y₁ y₂ => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (y₁ + y₂)).indicator hA).coeFn_toLp,
          ((Lp.memLp y₁).indicator hA).coeFn_toLp,
          ((Lp.memLp y₂).indicator hA).coeFn_toLp,
          Lp.coeFn_add y₁ y₂,
          Lp.coeFn_add (((Lp.memLp y₁).indicator hA).toLp (A.indicator y₁))
            (((Lp.memLp y₂).indicator hA).toLp (A.indicator y₂))] with ω h12 h1 h2 hadd1 hadd2
        rw [h12, hadd2, Pi.add_apply, h1, h2]
        by_cases hω : ω ∈ A
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω, hadd1,
            Pi.add_apply]
        · simp [Set.indicator_of_notMem hω]
      map_smul' := fun c y => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • y)).indicator hA).coeFn_toLp,
          ((Lp.memLp y).indicator hA).coeFn_toLp,
          Lp.coeFn_smul c y,
          Lp.coeFn_smul c (((Lp.memLp y).indicator hA).toLp (A.indicator y))] with ω hcy hy hs1 hs2
        rw [hcy, RingHom.id_apply, hs2, Pi.smul_apply, hy]
        by_cases hω : ω ∈ A
        · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hs1, Pi.smul_apply]
        · simp [Set.indicator_of_notMem hω] }
    1
    (fun y => by
      rw [one_mul]
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_def, Lp.norm_def]
      apply ENNReal.toReal_mono (Lp.eLpNorm_lt_top y).ne
      rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
      calc eLpNormEssSup (((Lp.memLp y).indicator hA).toLp (A.indicator y)) P
          = eLpNormEssSup (A.indicator y) P :=
            eLpNormEssSup_congr_ae (((Lp.memLp y).indicator hA).coeFn_toLp)
        _ ≤ eLpNormEssSup y P := by
            apply eLpNormEssSup_mono_enorm_ae
            exact Eventually.of_forall fun ω => by
              by_cases hω : ω ∈ A
              · simp [Set.indicator_of_mem hω]
              · simp [Set.indicator_of_notMem hω])

lemma indCLM_ae (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) (y : Lp X ⊤ P) :
    ∀ᵐ ω ∂P, indCLM P hA y ω = A.indicator y ω :=
  ((Lp.memLp y).indicator hA).coeFn_toLp

lemma norm_indCLM_le (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    ‖indCLM (X := X) P hA‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma norm_indCLM_apply_le (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) (y : Lp X ⊤ P) :
    ‖indCLM P hA y‖ ≤ ‖y‖ := by
  calc ‖indCLM P hA y‖ ≤ ‖indCLM (X := X) P hA‖ * ‖y‖ := (indCLM P hA).le_opNorm y
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (norm_indCLM_le P hA) (norm_nonneg y)
    _ = ‖y‖ := one_mul _

lemma indCLM_congr (P : Measure Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A = B) :
    indCLM (X := X) P hA = indCLM P hB := by
  subst h; rfl

lemma indCLM_empty (P : Measure Ω) :
    indCLM (X := X) P MeasurableSet.empty = 0 := by
  ext1 y
  apply Lp.ext
  filter_upwards [indCLM_ae P MeasurableSet.empty y, Lp.coeFn_zero X ⊤ P] with ω h1 h2
  change (indCLM P MeasurableSet.empty y) ω = (0 : Lp X ⊤ P) ω
  rw [h1, h2]
  simp

lemma indCLM_univ (P : Measure Ω) :
    indCLM (X := X) P MeasurableSet.univ = ContinuousLinearMap.id ℝ (Lp X ⊤ P) := by
  ext1 y
  apply Lp.ext
  filter_upwards [indCLM_ae P MeasurableSet.univ y] with ω h1
  rw [h1]
  simp

lemma indCLM_comp (P : Measure Ω) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (indCLM (X := X) P hA).comp (indCLM P hB) = indCLM P (hA.inter hB) := by
  ext1 y
  apply Lp.ext
  filter_upwards [indCLM_ae P hA (indCLM P hB y), indCLM_ae P hB y,
    indCLM_ae P (hA.inter hB) y] with ω h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, h1, h3]
  by_cases hωA : ω ∈ A
  · by_cases hωB : ω ∈ B
    · simp [Set.indicator_of_mem hωA, Set.indicator_of_mem hωB,
        Set.indicator_of_mem (Set.mem_inter hωA hωB), h2]
    · simp [Set.indicator_of_mem hωA, Set.indicator_of_notMem hωB,
        Set.indicator_of_notMem (fun h : ω ∈ A ∩ B => hωB h.2), h2]
  · simp [Set.indicator_of_notMem hωA,
      Set.indicator_of_notMem (fun h : ω ∈ A ∩ B => hωA h.1)]

lemma indCLM_union_disjoint (P : Measure Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    indCLM (X := X) P (hA.union hB) = indCLM P hA + indCLM P hB := by
  ext1 y
  apply Lp.ext
  filter_upwards [indCLM_ae P (hA.union hB) y, indCLM_ae P hA y, indCLM_ae P hB y,
    Lp.coeFn_add (indCLM P hA y) (indCLM P hB y)] with ω hAB' hA' hB' hadd
  change (indCLM P (hA.union hB) y) ω = (indCLM P hA y + indCLM P hB y) ω
  rw [hadd, Pi.add_apply, hAB', hA', hB']
  exact congr_fun (Set.indicator_union_of_disjoint hAB y) ω

lemma indCLM_add_compl (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    indCLM (X := X) P hA + indCLM P hA.compl = ContinuousLinearMap.id ℝ (Lp X ⊤ P) := by
  rw [← indCLM_union_disjoint P hA hA.compl disjoint_compl_right,
    indCLM_congr P (hA.union hA.compl) MeasurableSet.univ (Set.union_compl_self A),
    indCLM_univ]

lemma indCLM_diff (P : Measure Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    indCLM (X := X) P hB - indCLM P hA = indCLM P (hB.diff hA) := by
  have h1 := indCLM_union_disjoint (X := X) P hA (hB.diff hA) disjoint_sdiff_self_right
  rw [indCLM_congr P (hA.union (hB.diff hA)) hB (Set.union_sdiff_cancel hAB)] at h1
  rw [h1, add_sub_cancel_left]

lemma indCLM_eq_zero_of_measure_zero (P : Measure Ω) {A : Set Ω}
    (hA : MeasurableSet A) (h0 : P A = 0) :
    indCLM (X := X) P hA = 0 := by
  ext1 y
  apply Lp.ext
  have hae : ∀ᵐ ω ∂P, ω ∉ A := measure_eq_zero_iff_ae_notMem.mp h0
  filter_upwards [indCLM_ae P hA y, Lp.coeFn_zero X ⊤ P, hae] with ω h1 h2 hnot
  change (indCLM P hA y) ω = (0 : Lp X ⊤ P) ω
  rw [h1, h2, Set.indicator_of_notMem hnot, Pi.zero_apply]

lemma indCLM_eq_zero_of_ae_zero (P : Measure Ω) {A : Set Ω}
    (hA : MeasurableSet A) (y : Lp X ⊤ P) (hy : ∀ᵐ ω ∂P, ω ∈ A → y ω = 0) :
    indCLM P hA y = 0 := by
  apply Lp.ext
  filter_upwards [indCLM_ae P hA y, Lp.coeFn_zero X ⊤ P, hy] with ω h1 h2 h3
  rw [h1, h2, Pi.zero_apply]
  by_cases hω : ω ∈ A
  · simp [Set.indicator_of_mem hω, h3 hω]
  · simp [Set.indicator_of_notMem hω]

lemma norm_indCLM_add_disjoint (P : Measure Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B)
    (y₁ y₂ : Lp X ⊤ P) :
    ‖indCLM P hA y₁ + indCLM P hB y₂‖ ≤ max ‖y₁‖ ‖y₂‖ := by
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def]
  have hfin1 : eLpNorm y₁ ⊤ P ≠ ⊤ := (Lp.eLpNorm_lt_top y₁).ne
  have hfin2 : eLpNorm y₂ ⊤ P ≠ ⊤ := (Lp.eLpNorm_lt_top y₂).ne
  have hmax_fin : max (eLpNorm y₁ ⊤ P) (eLpNorm y₂ ⊤ P) ≠ ⊤ := max_ne_top hfin1 hfin2
  rw [← ENNReal.toReal_max hfin1 hfin2]
  apply ENNReal.toReal_mono hmax_fin
  rw [eLpNorm_exponent_top, eLpNorm_exponent_top, eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [Lp.coeFn_add (indCLM P hA y₁) (indCLM P hB y₂),
    indCLM_ae P hA y₁, indCLM_ae P hB y₂,
    ae_le_eLpNormEssSup (f := fun ω => y₁ ω) (μ := P),
    ae_le_eLpNormEssSup (f := fun ω => y₂ ω) (μ := P)] with ω hadd h1 h2 hb1 hb2
  rw [hadd, Pi.add_apply, h1, h2]
  by_cases hωA : ω ∈ A
  · have hωB : ω ∉ B := Set.disjoint_left.mp hAB hωA
    simp only [Set.indicator_of_mem hωA, Set.indicator_of_notMem hωB, add_zero]
    exact le_trans hb1 (le_max_left _ _)
  · by_cases hωB : ω ∈ B
    · simp only [Set.indicator_of_notMem hωA, Set.indicator_of_mem hωB, zero_add]
      exact le_trans hb2 (le_max_right _ _)
    · simp only [Set.indicator_of_notMem hωA, Set.indicator_of_notMem hωB, add_zero, enorm_zero]
      exact bot_le

omit [NormedSpace ℝ X] in
lemma norm_Lp_const_le (P : Measure Ω) [IsFiniteMeasure P] (x : X) :
    ‖Lp.const ⊤ P x‖ ≤ ‖x‖ := by
  have h := Lp.norm_const_le (p := (⊤ : ℝ≥0∞)) (μ := P) (c := x)
  simpa using h

omit [NormedSpace ℝ X] in
lemma coeFn_finset_sum {ι : Type*} (P : Measure Ω) (s : Finset ι) (f : ι → Lp X ⊤ P) :
    (⇑(∑ i ∈ s, f i) : Ω → X) =ᵐ[P] fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero X ⊤ P] with ω hω
    simpa using hω
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with ω hadd hih
    rw [hadd, Pi.add_apply, hih, Finset.sum_insert ha]

end IndicatorProjection

section VariationContent

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The variation content `ν(A) = ‖v ∘ P_A‖` of a functional `v ∈ (L∞_P(Ω, X))*`. -/
noncomputable def nu (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    (A : Set Ω) (hA : MeasurableSet A) : ℝ :=
  ‖v.comp (indCLM P hA)‖

lemma nu_congr (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A = B) :
    nu P v A hA = nu P v B hB := by
  subst h; rfl

lemma nu_nonneg (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {A : Set Ω} (hA : MeasurableSet A) :
    0 ≤ nu P v A hA :=
  norm_nonneg _

lemma nu_le_norm (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {A : Set Ω} (hA : MeasurableSet A) :
    nu P v A hA ≤ ‖v‖ := by
  calc ‖v.comp (indCLM P hA)‖
      ≤ ‖v‖ * ‖indCLM (X := X) P hA‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left (norm_indCLM_le P hA) (norm_nonneg v)
    _ = ‖v‖ := mul_one _

lemma nu_empty (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P)) :
    nu P v ∅ MeasurableSet.empty = 0 := by
  simp [nu, indCLM_empty]

lemma nu_univ (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P)) :
    nu P v Set.univ MeasurableSet.univ = ‖v‖ := by
  simp [nu, indCLM_univ]

lemma nu_eq_zero_of_measure_zero (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {A : Set Ω} (hA : MeasurableSet A) (h0 : P A = 0) :
    nu P v A hA = 0 := by
  simp [nu, indCLM_eq_zero_of_measure_zero P hA h0]

lemma exists_dual_apply_gt {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (w : StrongDual ℝ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : E, ‖y‖ ≤ 1 ∧ ‖w‖ - ε < w y := by
  by_cases hw : ‖w‖ = 0
  · refine ⟨0, by simp, ?_⟩
    simp [hw, hε]
  · have hw_pos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    have hlt : max 0 (‖w‖ - ε) < ‖w‖ := max_lt hw_pos (sub_lt_self _ hε)
    have hnot : ¬ ∀ y : E, ‖w y‖ ≤ max 0 (‖w‖ - ε) * ‖y‖ := by
      intro hall
      have hle : ‖w‖ ≤ max 0 (‖w‖ - ε) :=
        ContinuousLinearMap.opNorm_le_bound w (le_max_left _ _) hall
      linarith
    push Not at hnot
    obtain ⟨y₀, hy₀⟩ := hnot
    have hy₀_ne : ‖y₀‖ ≠ 0 := by
      intro h0
      have h1 : ‖w y₀‖ ≤ ‖w‖ * ‖y₀‖ := w.le_opNorm y₀
      rw [h0, mul_zero] at h1 hy₀
      linarith [norm_nonneg (w y₀)]
    have hy₀_pos : 0 < ‖y₀‖ := lt_of_le_of_ne (norm_nonneg y₀) (Ne.symm hy₀_ne)
    set y₁ : E := (‖y₀‖⁻¹) • y₀
    have hy₁_norm : ‖y₁‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hy₀_pos.le), inv_mul_cancel₀ hy₀_ne]
    have hwy₁ : ‖w‖ - ε < |w y₁| := by
      have h2 : max 0 (‖w‖ - ε) < ‖w y₁‖ := by
        rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hy₀_pos.le),
          inv_mul_eq_div, lt_div_iff₀ hy₀_pos]
        exact hy₀
      rw [Real.norm_eq_abs] at h2
      exact lt_of_le_of_lt (le_max_right _ _) h2
    by_cases hsign : 0 ≤ w y₁
    · refine ⟨y₁, hy₁_norm.le, ?_⟩
      rwa [abs_of_nonneg hsign] at hwy₁
    · refine ⟨-y₁, by simp [hy₁_norm], ?_⟩
      rw [map_neg]
      rw [abs_of_neg (not_le.mp hsign)] at hwy₁
      exact hwy₁

lemma nu_union_disjoint (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    nu P v (A ∪ B) (hA.union hB) = nu P v A hA + nu P v B hB := by
  apply le_antisymm
  · unfold nu
    rw [indCLM_union_disjoint P hA hB hAB, ContinuousLinearMap.comp_add]
    exact norm_add_le _ _
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨y₁, hy₁_norm, hy₁⟩ := exists_dual_apply_gt (v.comp (indCLM P hA)) hε2
    obtain ⟨y₂, hy₂_norm, hy₂⟩ := exists_dual_apply_gt (v.comp (indCLM P hB)) hε2
    set y : Lp X ⊤ P := indCLM P hA y₁ + indCLM P hB y₂
    have hy_norm : ‖y‖ ≤ 1 :=
      le_trans (norm_indCLM_add_disjoint P hA hB hAB y₁ y₂) (max_le hy₁_norm hy₂_norm)
    have hPy : indCLM P (hA.union hB) y = y := by
      have h1 : indCLM P (hA.union hB) (indCLM P hA y₁) = indCLM P hA y₁ := by
        have hc := congr_arg (fun T => T y₁) (indCLM_comp (X := X) P (hA.union hB) hA)
        simp only [ContinuousLinearMap.comp_apply] at hc
        rw [hc, indCLM_congr P ((hA.union hB).inter hA) hA Set.union_inter_cancel_left]
      have h2 : indCLM P (hA.union hB) (indCLM P hB y₂) = indCLM P hB y₂ := by
        have hc := congr_arg (fun T => T y₂) (indCLM_comp (X := X) P (hA.union hB) hB)
        simp only [ContinuousLinearMap.comp_apply] at hc
        rw [hc, indCLM_congr P ((hA.union hB).inter hB) hB Set.union_inter_cancel_right]
      rw [map_add, h1, h2]
    have hvy : v (indCLM P (hA.union hB) y) ≤ nu P v (A ∪ B) (hA.union hB) := by
      calc v (indCLM P (hA.union hB) y)
          ≤ ‖(v.comp (indCLM P (hA.union hB))) y‖ := le_abs_self _
        _ ≤ ‖v.comp (indCLM P (hA.union hB))‖ * ‖y‖ := (v.comp _).le_opNorm y
        _ ≤ ‖v.comp (indCLM P (hA.union hB))‖ * 1 :=
            mul_le_mul_of_nonneg_left hy_norm (norm_nonneg _)
        _ = nu P v (A ∪ B) (hA.union hB) := mul_one _
    rw [hPy, map_add] at hvy
    simp only [ContinuousLinearMap.comp_apply] at hy₁ hy₂
    unfold nu at *
    linarith

lemma nu_mono (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    nu P v A hA ≤ nu P v B hB := by
  have h1 := nu_union_disjoint P v hA (hB.diff hA) disjoint_sdiff_self_right
  rw [nu_congr P v (hA.union (hB.diff hA)) hB (Set.union_sdiff_cancel hAB)] at h1
  linarith [nu_nonneg P v (hB.diff hA)]

lemma nu_diff (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    nu P v (B \ A) (hB.diff hA) = nu P v B hB - nu P v A hA := by
  have h1 := nu_union_disjoint P v hA (hB.diff hA) disjoint_sdiff_self_right
  rw [nu_congr P v (hA.union (hB.diff hA)) hB (Set.union_sdiff_cancel hAB)] at h1
  linarith

end VariationContent

section DecompositionPart

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A decreasing sequence of measurable sets whose `P`-measures tend to `0`. -/
def Admissible (P : Measure Ω) (F : ℕ → Set Ω) : Prop :=
  (∀ n, MeasurableSet (F n)) ∧ (∀ n, F (n + 1) ⊆ F n) ∧
    Tendsto (fun n => P (F n)) atTop (𝓝 0)

/-- The limiting variation `lim_{n→∞} ν(F_n)` of a decreasing measurable sequence. -/
noncomputable def nuSeqLim (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet (F n)) : ℝ :=
  ⨅ n, nu P v (F n) (hF n)

lemma antitone_nu_of_admissible (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {F : ℕ → Set Ω} (hF : Admissible P F) :
    Antitone (fun n => nu P v (F n) (hF.1 n)) :=
  antitone_nat_of_succ_le fun n => nu_mono P v (hF.1 (n + 1)) (hF.1 n) (hF.2.1 n)

lemma tendsto_nu_of_admissible (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {F : ℕ → Set Ω} (hF : Admissible P F) :
    Tendsto (fun n => nu P v (F n) (hF.1 n)) atTop (𝓝 (nuSeqLim P v F hF.1)) :=
  tendsto_atTop_ciInf (antitone_nu_of_admissible P v hF) ⟨0, by rintro _ ⟨n, rfl⟩; exact nu_nonneg P v _⟩

lemma nuSeqLim_le (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P))
    {F : ℕ → Set Ω} (hF : Admissible P F) (n : ℕ) :
    nuSeqLim P v F hF.1 ≤ nu P v (F n) (hF.1 n) :=
  ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact nu_nonneg P v _⟩ n

/-- Existence of an admissible sequence `G` maximizing `lim_{n→∞} ν(F_n)`. -/
lemma exists_maximizing_admissible (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P)) :
    ∃ (G : ℕ → Set Ω) (hG : Admissible P G),
      ∀ (F : ℕ → Set Ω) (hF : Admissible P F),
        nuSeqLim P v F hF.1 ≤ nuSeqLim P v G hG.1 := by
  let S : Set ℝ := {r | ∃ (F : ℕ → Set Ω) (hF : Admissible P F), r = nuSeqLim P v F hF.1}
  have hS_ne : S.Nonempty := by
    refine ⟨0, fun _ => ∅, ⟨fun _ => .empty, fun _ => subset_rfl, ?_⟩, ?_⟩
    · simp
    · simp [nuSeqLim, nu_empty]
  have hS_bdd : BddAbove S := by
    refine ⟨‖v‖, ?_⟩
    rintro r ⟨F, hF, rfl⟩
    exact le_trans (nuSeqLim_le P v hF 0) (nu_le_norm P v (hF.1 0))
  set M : ℝ := sSup S
  have happrox : ∀ k : ℕ, ∃ (F : ℕ → Set Ω) (hF : Admissible P F),
      M - 1 / ((k : ℝ) + 1) < nuSeqLim P v F hF.1 := by
    intro k
    have hlt : M - 1 / ((k : ℝ) + 1) < M := by
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, ⟨F, hF, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hS_ne hlt
    exact ⟨F, hF, hr⟩
  choose F hF hF_gt using happrox
  have hsmall : ∀ k m : ℕ, ∃ N : ℕ, P (F k N) ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + m + 2) := by
    intro k m
    have hpos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ (k + m + 2) :=
      ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) _
    have hev := (hF k).2.2.eventually (gt_mem_nhds hpos)
    obtain ⟨N, hN⟩ := hev.exists
    exact ⟨N, hN.le⟩
  choose rawIdx hrawIdx using hsmall
  let idx : ℕ → ℕ → ℕ := fun k => Nat.rec (rawIdx k 0) (fun m prev => max prev (rawIdx k (m + 1)))
  have hidx_mono : ∀ k, Monotone (idx k) := fun k =>
    monotone_nat_of_le_succ fun m => le_max_left _ _
  have hidx_ge : ∀ k m, rawIdx k m ≤ idx k m := by
    intro k m
    cases m with
    | zero => exact le_rfl
    | succ m => exact le_max_right _ _
  let F' : ℕ → ℕ → Set Ω := fun k m => F k (idx k m)
  have hF'_meas : ∀ k m, MeasurableSet (F' k m) := fun k m => (hF k).1 (idx k m)
  have hF'_dec : ∀ k m, F' k (m + 1) ⊆ F' k m := fun k m =>
    antitone_nat_of_succ_le (hF k).2.1 (hidx_mono k (Nat.le_succ m))
  have hF'_prob : ∀ k m, P (F' k m) ≤ (2 : ℝ≥0∞)⁻¹ ^ (k + m + 2) := fun k m =>
    le_trans (measure_mono (antitone_nat_of_succ_le (hF k).2.1 (hidx_ge k m))) (hrawIdx k m)
  let G : ℕ → Set Ω := fun m => ⋃ k : ℕ, F' k m
  have hG_meas : ∀ m, MeasurableSet (G m) := fun m => MeasurableSet.iUnion (fun k => hF'_meas k m)
  have hG_dec : ∀ m, G (m + 1) ⊆ G m := fun m => Set.iUnion_mono (fun k => hF'_dec k m)
  have hG_prob_le : ∀ m, P (G m) ≤ (2 : ℝ≥0∞)⁻¹ ^ (m + 1) := by
    intro m
    calc P (⋃ k : ℕ, F' k m)
        ≤ ∑' k : ℕ, P (F' k m) := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + m + 2) := ENNReal.tsum_le_tsum (fun k => hF'_prob k m)
      _ = ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (m + 2) * (2 : ℝ≥0∞)⁻¹ ^ k := by
          congr 1; ext k; rw [← pow_add]; congr 1; omega
      _ = (2 : ℝ≥0∞)⁻¹ ^ (m + 2) * ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k := ENNReal.tsum_mul_left
      _ = (2 : ℝ≥0∞)⁻¹ ^ (m + 2) * 2 := by
          rw [ENNReal.tsum_geometric]
          have hhalf : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) := by
            rw [one_div, ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat]
          have hsub : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
            rw [← ENNReal.ofReal_one, hhalf, ← ENNReal.ofReal_sub _ (by norm_num)]
            norm_num
          rw [hsub, inv_inv]
      _ = (2 : ℝ≥0∞)⁻¹ ^ (m + 1) := by
          rw [pow_succ, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  have hG_tendsto : Tendsto (fun m => P (G m)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun m : ℕ => (2 : ℝ≥0∞)⁻¹ ^ (m + 1)) atTop (𝓝 0) := by
      have h0 := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0∞)⁻¹)
        (by rw [ENNReal.inv_lt_one]; norm_num)
      exact h0.comp (tendsto_add_atTop_nat 1)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
      (fun _ => bot_le) hG_prob_le
  have hG : Admissible P G := ⟨hG_meas, hG_dec, hG_tendsto⟩
  have hM_le_G : M ≤ nuSeqLim P v G hG.1 := by
    have hle_k : ∀ k : ℕ, M - 1 / ((k : ℝ) + 1) ≤ nuSeqLim P v G hG.1 := by
      intro k
      refine le_ciInf fun m => ?_
      have hsub : F' k m ⊆ G m := Set.subset_iUnion (fun k => F' k m) k
      calc M - 1 / ((k : ℝ) + 1)
          ≤ nuSeqLim P v (F k) (hF k).1 := (hF_gt k).le
        _ ≤ nu P v (F' k m) (hF'_meas k m) := nuSeqLim_le P v (hF k) (idx k m)
        _ ≤ nu P v (G m) (hG.1 m) := nu_mono P v (hF'_meas k m) (hG.1 m) hsub
    have hlim : Tendsto (fun k : ℕ => M - 1 / ((k : ℝ) + 1)) atTop (𝓝 M) := by
      simpa [sub_zero] using (tendsto_const_nhds (x := M)).sub tendsto_one_div_add_atTop_nhds_zero_nat
    exact le_of_tendsto hlim (Eventually.of_forall hle_k)
  refine ⟨G, hG, fun F₀ hF₀ => ?_⟩
  exact le_trans (le_csSup hS_bdd ⟨F₀, hF₀, rfl⟩) hM_le_G

/-- Operator-norm decomposition of `v` into a countably-additive part `va` and a singular part `vs`
with `‖v‖ = ‖va‖ + ‖vs‖`. -/
lemma decomp_exists (P : Measure Ω) (v : StrongDual ℝ (Lp X ⊤ P)) :
    ∃ va vs : StrongDual ℝ (Lp X ⊤ P),
      IsSingular P vs ∧ v = va + vs ∧ ‖v‖ = ‖va‖ + ‖vs‖ ∧
      ∀ (H : ℕ → Set Ω) (hH : Admissible P H),
        Tendsto (fun n => nu P va (H n) (hH.1 n)) atTop (𝓝 0) := by
  obtain ⟨G, hG, hG_max⟩ := exists_maximizing_admissible P v
  set M : ℝ := nuSeqLim P v G hG.1
  have hG_lim : Tendsto (fun m => nu P v (G m) (hG.1 m)) atTop (𝓝 M) :=
    tendsto_nu_of_admissible P v hG
  let seq : ℕ → StrongDual ℝ (Lp X ⊤ P) := fun m => v.comp (indCLM P (hG.1 m))
  have hseq_cauchy : CauchySeq seq := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hG_lim) (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist_le : ∀ a b, a ≤ b → N ≤ a → dist (seq a) (seq b) < ε := by
      intro a b hab haN
      have hsub : G b ⊆ G a := antitone_nat_of_succ_le hG.2.1 hab
      have hdiff : seq a - seq b = v.comp (indCLM P ((hG.1 a).diff (hG.1 b))) := by
        simp only [seq, ← ContinuousLinearMap.comp_sub, indCLM_diff P (hG.1 b) (hG.1 a) hsub]
      rw [dist_eq_norm, hdiff]
      change nu P v (G a \ G b) ((hG.1 a).diff (hG.1 b)) < ε
      rw [nu_diff P v (hG.1 b) (hG.1 a) hsub]
      have ha := hN a haN
      have hb := hN b (le_trans haN hab)
      rw [Real.dist_eq] at ha hb
      have ha' := (abs_lt.mp ha).2
      have hb' := (abs_lt.mp hb).1
      linarith
    rcases le_total m n with hmn | hnm
    · exact hdist_le m n hmn hm
    · rw [dist_comm]
      exact hdist_le n m hnm hn
  obtain ⟨vs, hvs_lim⟩ := cauchySeq_tendsto_of_complete hseq_cauchy
  set va : StrongDual ℝ (Lp X ⊤ P) := v - vs
  have hva_lim : Tendsto (fun m => v.comp (indCLM P (hG.1 m).compl)) atTop (𝓝 va) := by
    have heq : (fun m => v.comp (indCLM P (hG.1 m).compl)) = fun m => v - seq m := by
      ext1 m
      have h1 : v.comp (indCLM P (hG.1 m) + indCLM P (hG.1 m).compl) = v := by
        rw [indCLM_add_compl P (hG.1 m), ContinuousLinearMap.comp_id]
      rw [ContinuousLinearMap.comp_add] at h1
      exact eq_sub_of_add_eq' h1
    rw [heq]
    exact tendsto_const_nhds.sub hvs_lim
  have hsplit : v = va + vs := (sub_add_cancel v vs).symm
  have hnorm : ‖v‖ = ‖va‖ + ‖vs‖ := by
    have h1 : Tendsto (fun m => nu P v (G m) (hG.1 m)) atTop (𝓝 ‖vs‖) := hvs_lim.norm
    have h2 : Tendsto (fun m => nu P v (G m)ᶜ (hG.1 m).compl) atTop (𝓝 ‖va‖) := hva_lim.norm
    have h3 : Tendsto (fun m => nu P v (G m)ᶜ (hG.1 m).compl + nu P v (G m) (hG.1 m))
        atTop (𝓝 (‖va‖ + ‖vs‖)) := h2.add h1
    have hconst : ∀ m, nu P v (G m)ᶜ (hG.1 m).compl + nu P v (G m) (hG.1 m) = ‖v‖ := by
      intro m
      rw [← nu_union_disjoint P v (hG.1 m).compl (hG.1 m) disjoint_compl_left,
        nu_congr P v ((hG.1 m).compl.union (hG.1 m)) MeasurableSet.univ (Set.compl_union_self (G m)),
        nu_univ]
    simp_rw [hconst] at h3
    exact tendsto_nhds_unique tendsto_const_nhds h3
  have hsing : IsSingular P vs := by
    refine ⟨G, hG.1, hG.2.1, hG.2.2, fun y ⟨N, hy⟩ => ?_⟩
    have heval : Tendsto (fun m => seq m y) atTop (𝓝 (vs y)) :=
      (ContinuousLinearMap.apply ℝ ℝ y).continuous.tendsto vs |>.comp hvs_lim
    have hev0 : ∀ᶠ m in atTop, seq m y = 0 := by
      filter_upwards [eventually_ge_atTop N] with m hm
      have hsub : G m ⊆ G N := antitone_nat_of_succ_le hG.2.1 hm
      have h0 : indCLM P (hG.1 m) y = 0 := indCLM_eq_zero_of_ae_zero P (hG.1 m) y <| by
        filter_upwards [hy] with ω hω hmem
        exact hω (hsub hmem)
      simp [seq, h0]
    have hzero : Tendsto (fun m => seq m y) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hev0.mono fun _ h => h.symm)
    exact tendsto_nhds_unique heval hzero
  have hnu_va_lim : ∀ (A : Set Ω) (hA : MeasurableSet A),
      Tendsto (fun m => nu P v (A ∩ (G m)ᶜ) (hA.inter (hG.1 m).compl))
        atTop (𝓝 (nu P va A hA)) := by
    intro A hA
    have hcomp_lim : Tendsto (fun m => (v.comp (indCLM P (hG.1 m).compl)).comp (indCLM P hA))
        atTop (𝓝 (va.comp (indCLM P hA))) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hva_lim) ε hε
      refine ⟨N, fun m hm => ?_⟩
      rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
      calc ‖(v.comp (indCLM P (hG.1 m).compl) - va).comp (indCLM P hA)‖
          ≤ ‖v.comp (indCLM P (hG.1 m).compl) - va‖ * ‖indCLM (X := X) P hA‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖v.comp (indCLM P (hG.1 m).compl) - va‖ * 1 :=
            mul_le_mul_of_nonneg_left (norm_indCLM_le P hA) (norm_nonneg _)
        _ = dist (v.comp (indCLM P (hG.1 m).compl)) va := by rw [mul_one, dist_eq_norm]
        _ < ε := hN m hm
    have heq : (fun m => ‖(v.comp (indCLM P (hG.1 m).compl)).comp (indCLM P hA)‖) =
        fun m => nu P v (A ∩ (G m)ᶜ) (hA.inter (hG.1 m).compl) := by
      ext1 m
      unfold nu
      rw [ContinuousLinearMap.comp_assoc, indCLM_comp P (hG.1 m).compl hA,
        indCLM_congr P ((hG.1 m).compl.inter hA) (hA.inter (hG.1 m).compl) (Set.inter_comm _ _)]
    rw [← heq]
    exact hcomp_lim.norm
  have hva_adm : ∀ (H : ℕ → Set Ω) (hH : Admissible P H),
      Tendsto (fun n => nu P va (H n) (hH.1 n)) atTop (𝓝 0) := by
    intro H hH
    let K : ℕ → Set Ω := fun n => G n ∪ H n
    have hK_meas : ∀ n, MeasurableSet (K n) := fun n => (hG.1 n).union (hH.1 n)
    have hK_dec : ∀ n, K (n + 1) ⊆ K n := fun n => Set.union_subset_union (hG.2.1 n) (hH.2.1 n)
    have hK_prob : Tendsto (fun n => P (K n)) atTop (𝓝 0) := by
      have hsum : Tendsto (fun n => P (G n) + P (H n)) atTop (𝓝 (0 + 0)) := hG.2.2.add hH.2.2
      rw [add_zero] at hsum
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun _ => bot_le) (fun n => measure_union_le (G n) (H n))
    have hK : Admissible P K := ⟨hK_meas, hK_dec, hK_prob⟩
    have hK_le_M : nuSeqLim P v K hK.1 ≤ M := hG_max K hK
    have hK_lim : Tendsto (fun n => nu P v (K n) (hK.1 n)) atTop (𝓝 (nuSeqLim P v K hK.1)) :=
      tendsto_nu_of_admissible P v hK
    have hbound : ∀ n, nu P va (H n) (hH.1 n) ≤ nu P v (K n) (hK.1 n) - M := by
      intro n
      have hstep : ∀ᶠ m in atTop, nu P v (H n ∩ (G m)ᶜ) ((hH.1 n).inter (hG.1 m).compl) ≤
          nu P v (K n) (hK.1 n) - nu P v (G m) (hG.1 m) := by
        filter_upwards [eventually_ge_atTop n] with m hmn
        have hGm_sub : G m ⊆ G n := antitone_nat_of_succ_le hG.2.1 hmn
        have hdisj : Disjoint (G m) (H n ∩ (G m)ᶜ) :=
          Disjoint.mono_right Set.inter_subset_right disjoint_compl_right
        have hsub : G m ∪ (H n ∩ (G m)ᶜ) ⊆ K n :=
          Set.union_subset (hGm_sub.trans Set.subset_union_left)
            (Set.inter_subset_left.trans Set.subset_union_right)
        have hle := nu_mono P v ((hG.1 m).union ((hH.1 n).inter (hG.1 m).compl)) (hK.1 n) hsub
        rw [nu_union_disjoint P v (hG.1 m) ((hH.1 n).inter (hG.1 m).compl) hdisj] at hle
        linarith
      have hlim_rhs : Tendsto (fun m => nu P v (K n) (hK.1 n) - nu P v (G m) (hG.1 m))
          atTop (𝓝 (nu P v (K n) (hK.1 n) - M)) :=
        tendsto_const_nhds.sub hG_lim
      exact le_of_tendsto_of_tendsto (hnu_va_lim (H n) (hH.1 n)) hlim_rhs hstep
    have hbound' : ∀ n, nu P va (H n) (hH.1 n) ≤ nu P v (K n) (hK.1 n) - nuSeqLim P v K hK.1 :=
      fun n => le_trans (hbound n) (by linarith)
    have htop : Tendsto (fun n => nu P v (K n) (hK.1 n) - nuSeqLim P v K hK.1) atTop (𝓝 0) := by
      simpa [sub_self] using hK_lim.sub (tendsto_const_nhds (x := nuSeqLim P v K hK.1))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop
      (fun n => nu_nonneg P va (hH.1 n)) hbound'
  exact ⟨va, vs, hsing, hsplit, hnorm, hva_adm⟩

end DecompositionPart

section MeasureConstruction

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Build a finite measure from a nonnegative finitely additive set function that is continuous
from above at `∅`. -/
noncomputable def measureOfContent (φ : ∀ s : Set Ω, MeasurableSet s → ℝ)
    (h0 : ∀ s hs, 0 ≤ φ s hs)
    (hempty : φ ∅ MeasurableSet.empty = 0)
    (hadd : ∀ s t hs ht, Disjoint s t → φ (s ∪ t) (hs.union ht) = φ s hs + φ t ht)
    (hcont : ∀ (H : ℕ → Set Ω) (hH : ∀ n, MeasurableSet (H n)),
      (∀ n, H (n + 1) ⊆ H n) → (⋂ n, H n = ∅) →
      Tendsto (fun n => φ (H n) (hH n)) atTop (𝓝 0)) : Measure Ω :=
  Measure.ofMeasurable (fun s hs => ENNReal.ofReal (φ s hs))
    (by simp [hempty])
    (by
      intro f hf hdisj
      have hφ_congr : ∀ {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B),
          A = B → φ A hA = φ B hB := by
        rintro A _ hA hB rfl; rfl
      let U : Set Ω := ⋃ i, f i
      have hU : MeasurableSet U := MeasurableSet.iUnion hf
      let B : ℕ → Set Ω := fun n => ⋃ i ∈ Finset.range n, f i
      have hB : ∀ n, MeasurableSet (B n) := fun n =>
        Finset.measurableSet_biUnion _ (fun i _ => hf i)
      have hB_sum : ∀ n, φ (B n) (hB n) = ∑ i ∈ Finset.range n, φ (f i) (hf i) := by
        intro n
        induction n with
        | zero =>
          have hB0 : B 0 = ∅ := by simp [B]
          simp only [Finset.range_zero, Finset.sum_empty]
          rw [hφ_congr (hB 0) MeasurableSet.empty hB0, hempty]
        | succ n ih =>
          have hBsucc : B (n + 1) = B n ∪ f n := by
            ext ω
            simp only [B, Set.mem_iUnion, Finset.mem_range, Set.mem_union]
            constructor
            · rintro ⟨i, hi, hω⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
              · exact Or.inl ⟨i, hlt, hω⟩
              · exact Or.inr hω
            · rintro (⟨i, hi, hω⟩ | hω)
              · exact ⟨i, Nat.lt_succ_of_lt hi, hω⟩
              · exact ⟨n, Nat.lt_succ_self n, hω⟩
          have hdisj_n : Disjoint (B n) (f n) := by
            rw [Set.disjoint_left]
            intro ω hωB hωn
            simp only [B, Set.mem_iUnion, Finset.mem_range] at hωB
            obtain ⟨i, hi, hωi⟩ := hωB
            exact Set.disjoint_left.mp (hdisj (Nat.ne_of_lt hi)) hωi hωn
          rw [hφ_congr (hB (n + 1)) ((hB n).union (hf n)) hBsucc,
            hadd (B n) (f n) (hB n) (hf n) hdisj_n, ih, Finset.sum_range_succ]
      let R : ℕ → Set Ω := fun n => U \ B n
      have hR : ∀ n, MeasurableSet (R n) := fun n => hU.diff (hB n)
      have hR_dec : ∀ n, R (n + 1) ⊆ R n := by
        intro n ω ⟨hωU, hωnot⟩
        refine ⟨hωU, fun hωB => hωnot ?_⟩
        simp only [B, Set.mem_iUnion, Finset.mem_range] at hωB ⊢
        obtain ⟨i, hi, hωi⟩ := hωB
        exact ⟨i, Nat.lt_succ_of_lt hi, hωi⟩
      have hR_inter : ⋂ n, R n = ∅ := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
        intro hall
        have hωU : ω ∈ U := (hall 0).1
        obtain ⟨k, hωk⟩ := Set.mem_iUnion.mp hωU
        have hωBk : ω ∈ B (k + 1) := by
          simp only [B, Set.mem_iUnion, Finset.mem_range]
          exact ⟨k, Nat.lt_succ_self k, hωk⟩
        exact (hall (k + 1)).2 hωBk
      have hsum_eq : ∀ n, ∑ i ∈ Finset.range n, φ (f i) (hf i) = φ U hU - φ (R n) (hR n) := by
        intro n
        have hBsub : B n ⊆ U := by
          intro ω hω
          simp only [B, Set.mem_iUnion, Finset.mem_range] at hω
          obtain ⟨i, _, hωi⟩ := hω
          exact Set.mem_iUnion.mpr ⟨i, hωi⟩
        have h1 := hadd (B n) (R n) (hB n) (hR n) disjoint_sdiff_self_right
        rw [hφ_congr ((hB n).union (hR n)) hU (Set.union_sdiff_cancel hBsub), hB_sum n] at h1
        linarith
      have hlim_real : Tendsto (fun n => ∑ i ∈ Finset.range n, φ (f i) (hf i))
          atTop (𝓝 (φ U hU)) := by
        simp_rw [hsum_eq]
        simpa using tendsto_const_nhds.sub (hcont R hR hR_dec hR_inter)
      have hlim_enn : Tendsto (fun n => ∑ i ∈ Finset.range n, ENNReal.ofReal (φ (f i) (hf i)))
          atTop (𝓝 (ENNReal.ofReal (φ U hU))) := by
        have h1 := (ENNReal.continuous_ofReal.tendsto (φ U hU)).comp hlim_real
        refine h1.congr fun n => ?_
        exact ENNReal.ofReal_sum_of_nonneg (fun i _ => h0 (f i) (hf i))
      exact tendsto_nhds_unique hlim_enn (ENNReal.tendsto_nat_tsum _))

lemma measureOfContent_apply (φ : ∀ s : Set Ω, MeasurableSet s → ℝ)
    (h0 : ∀ s hs, 0 ≤ φ s hs)
    (hempty : φ ∅ MeasurableSet.empty = 0)
    (hadd : ∀ s t hs ht, Disjoint s t → φ (s ∪ t) (hs.union ht) = φ s hs + φ t ht)
    (hcont : ∀ (H : ℕ → Set Ω) (hH : ∀ n, MeasurableSet (H n)),
      (∀ n, H (n + 1) ⊆ H n) → (⋂ n, H n = ∅) →
      Tendsto (fun n => φ (H n) (hH n)) atTop (𝓝 0))
    (s : Set Ω) (hs : MeasurableSet s) :
    measureOfContent φ h0 hempty hadd hcont s = ENNReal.ofReal (φ s hs) :=
  Measure.ofMeasurable_apply s hs

lemma ae_nonneg_of_forall_setIntegral_nonneg {P : Measure Ω} [IsFiniteMeasure P]
    {h : Ω → ℝ} (hm : Measurable h) (hint : Integrable h P)
    (hnonneg : ∀ A, MeasurableSet A → 0 ≤ ∫ ω in A, h ω ∂P) :
    ∀ᵐ ω ∂P, 0 ≤ h ω := by
  have hnull_n : ∀ n : ℕ, P {ω | h ω ≤ -(1 / ((n : ℝ) + 1))} = 0 := by
    intro n
    set E : Set Ω := {ω | h ω ≤ -(1 / ((n : ℝ) + 1))}
    have hE : MeasurableSet E := measurableSet_le hm measurable_const
    have h1 : 0 ≤ ∫ ω in E, h ω ∂P := hnonneg E hE
    have h2 : ∫ ω in E, h ω ∂P ≤ ∫ _ in E, -(1 / ((n : ℝ) + 1)) ∂P := by
      refine setIntegral_mono_on hint.integrableOn (integrableOn_const (measure_ne_top P E)) hE ?_
      intro ω hω
      exact hω
    rw [setIntegral_const, smul_eq_mul] at h2
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hPreal : P.real E ≤ 0 := by nlinarith
    have hPreal0 : P.real E = 0 := le_antisymm hPreal ENNReal.toReal_nonneg
    exact (ENNReal.toReal_eq_zero_iff (P E)).mp hPreal0 |>.resolve_right (measure_ne_top P E)
  have hsub : {ω | h ω < 0} ⊆ ⋃ n : ℕ, {ω | h ω ≤ -(1 / ((n : ℝ) + 1))} := by
    intro ω hω
    have hω' : h ω < 0 := hω
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hω')
    exact Set.mem_iUnion.mpr ⟨n, by change h ω ≤ -(1 / ((n : ℝ) + 1)); linarith⟩
  have hnull : P {ω | h ω < 0} = 0 :=
    measure_mono_null hsub (measure_iUnion_null hnull_n)
  have hae : ∀ᵐ ω ∂P, ω ∉ {ω | h ω < 0} := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with ω hω
  exact not_lt.mp hω

lemma measurable_lam_simple {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (lam : Ω → StrongDual ℝ X) (hm : ∀ x : X, Measurable fun ω => lam ω x)
    (s : SimpleFunc Ω X) :
    Measurable fun ω => lam ω (s ω) := by
  have : (fun ω => lam ω (s ω)) =
      fun ω => ∑ c ∈ s.range, (s ⁻¹' {c}).indicator (fun ω => lam ω c) ω := by
    funext ω
    rw [Finset.sum_eq_single (s ω)]
    · simp [Set.indicator_of_mem]
    · intro c _ hc
      rw [Set.indicator_of_notMem]
      simpa [eq_comm] using hc
    · intro h; exact absurd (s.mem_range_self ω) h
  rw [this]
  refine Finset.measurable_sum _ fun c _ => ?_
  exact (hm c).indicator (s.measurableSet_fiber c)

lemma aesm_lam {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : Measure Ω) (lam : Ω → StrongDual ℝ X)
    (hm : ∀ x : X, Measurable fun ω => lam ω x) (y : Ω → X) (hy : AEStronglyMeasurable y P) :
    AEStronglyMeasurable (fun ω => lam ω (y ω)) P := by
  have hsm := hy.stronglyMeasurable_mk
  have h1 : Measurable fun ω => lam ω (hy.mk y ω) := by
    refine measurable_of_tendsto_metrizable (f := fun n ω => lam ω (hsm.approx n ω))
      (fun n => measurable_lam_simple lam hm _) ?_
    rw [tendsto_pi_nhds]
    intro ω
    exact ((lam ω).continuous.tendsto _).comp (hsm.tendsto_approx ω)
  refine ⟨_, h1.stronglyMeasurable, ?_⟩
  filter_upwards [hy.ae_eq_mk] with ω hω
  rw [hω]

lemma integrable_lam {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : Measure Ω) (lam : Ω → StrongDual ℝ X)
    (hlam : lam ∈ Lambda1 X P) (y : Lp X ⊤ P) :
    Integrable (fun ω => lam ω (y ω)) P := by
  refine ⟨aesm_lam P lam hlam.1 y (Lp.aestronglyMeasurable y), ?_⟩
  have hfin : eLpNormEssSup y P ≠ ⊤ := by
    have := Lp.eLpNorm_lt_top y
    rw [eLpNorm_exponent_top] at this
    exact this.ne
  unfold HasFiniteIntegral
  calc ∫⁻ ω, ‖lam ω (y ω)‖ₑ ∂P ≤ ∫⁻ ω, ‖lam ω‖ₑ * eLpNormEssSup y P ∂P := by
        apply lintegral_mono_ae
        filter_upwards [ae_le_eLpNormEssSup (f := fun ω => y ω) (μ := P)] with ω hω
        exact (lam ω).le_opENorm_of_le hω
    _ = (∫⁻ ω, ‖lam ω‖ₑ ∂P) * eLpNormEssSup y P := lintegral_mul_const' _ _ hfin
    _ < ⊤ := ENNReal.mul_lt_top hlam.2 hfin.lt_top

end MeasureConstruction

section RepresentationPart

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [TopologicalSpace.SeparableSpace X]

/-- Every countably-additive functional `va ∈ (L∞_P(Ω, X))*` (in the sense that `ν_va(H_n) → 0`
on all admissible sequences) is absolutely continuous (`IsAbsCont P va`). -/
lemma isAbsCont_of_vanish_admissible (P : Measure Ω) [IsProbabilityMeasure P]
    (va : StrongDual ℝ (Lp X ⊤ P))
    (hva_adm : ∀ (H : ℕ → Set Ω) (hH : Admissible P H),
      Tendsto (fun n => nu P va (H n) (hH.1 n)) atTop (𝓝 0)) :
    IsAbsCont P va := by
  classical
  -- Helper: decreasing sequence with empty intersection is Admissible since P is finite
  have hadm_of_inter : ∀ (H : ℕ → Set Ω) (hH : ∀ n, MeasurableSet (H n)),
      (∀ n, H (n + 1) ⊆ H n) → (⋂ n, H n = ∅) → Admissible P H := by
    intro H hH hdec hinter
    refine ⟨hH, hdec, ?_⟩
    have hlim := tendsto_measure_iInter_atTop (μ := P) (fun n => (hH n).nullMeasurableSet)
      (antitone_nat_of_succ_le hdec) ⟨0, measure_ne_top P (H 0)⟩
    rwa [hinter, measure_empty] at hlim
  -- Step 1: Total variation measure μ from nu P va
  let μ : Measure Ω := measureOfContent (fun A hA => nu P va A hA)
    (fun A hA => nu_nonneg P va hA)
    (nu_empty P va)
    (fun A B hA hB hAB => nu_union_disjoint P va hA hB hAB)
    (fun H hH hdec hinter => hva_adm H (hadm_of_inter H hH hdec hinter))
  have hμ_apply : ∀ A (hA : MeasurableSet A), μ A = ENNReal.ofReal (nu P va A hA) :=
    measureOfContent_apply _ _ _ _ _
  have : IsFiniteMeasure μ := ⟨by rw [hμ_apply _ .univ]; exact ENNReal.ofReal_lt_top⟩
  have hμ_ac : μ ≪ P := Measure.AbsolutelyContinuous.mk fun A hA hPA => by
    rw [hμ_apply A hA, nu_eq_zero_of_measure_zero P va hA hPA, ENNReal.ofReal_zero]
  let g : Ω → ℝ := fun ω => (μ.rnDeriv P ω).toReal
  have hg_meas : Measurable g := (Measure.measurable_rnDeriv μ P).ennreal_toReal
  have hg_nonneg : ∀ ω, 0 ≤ g ω := fun _ => ENNReal.toReal_nonneg
  have hg_int : Integrable g P := Measure.integrable_toReal_rnDeriv
  have hg_setInt : ∀ A (hA : MeasurableSet A), ∫ ω in A, g ω ∂P = nu P va A hA := by
    intro A hA
    rw [Measure.setIntegral_toReal_rnDeriv hμ_ac, Measure.real, hμ_apply A hA,
      ENNReal.toReal_ofReal (nu_nonneg P va hA)]
  -- Step 2: For each x : X, build positive measure λ_x and Radon-Nikodym density f x
  let φ : X → ∀ A : Set Ω, MeasurableSet A → ℝ := fun x A hA =>
    ‖x‖ * nu P va A hA + va (indCLM P hA (Lp.const ⊤ P x))
  have hφ_bound : ∀ x A (hA : MeasurableSet A),
      |va (indCLM P hA (Lp.const ⊤ P x))| ≤ ‖x‖ * nu P va A hA := by
    intro x A hA
    calc |va (indCLM P hA (Lp.const ⊤ P x))|
        = ‖(va.comp (indCLM P hA)) (Lp.const ⊤ P x)‖ := rfl
      _ ≤ ‖va.comp (indCLM P hA)‖ * ‖Lp.const ⊤ P x‖ := (va.comp _).le_opNorm _
      _ ≤ nu P va A hA * ‖x‖ :=
          mul_le_mul_of_nonneg_left (norm_Lp_const_le P x) (nu_nonneg P va hA)
      _ = ‖x‖ * nu P va A hA := mul_comm _ _
  have hφ_nonneg : ∀ x A (hA : MeasurableSet A), 0 ≤ φ x A hA := by
    intro x A hA
    have h := (abs_le.mp (hφ_bound x A hA)).1
    dsimp only [φ]
    linarith
  have hφ_empty : ∀ x, φ x ∅ MeasurableSet.empty = 0 := by
    intro x
    simp [φ, nu_empty, indCLM_empty]
  have hφ_add : ∀ x A B (hA : MeasurableSet A) (hB : MeasurableSet B), Disjoint A B →
      φ x (A ∪ B) (hA.union hB) = φ x A hA + φ x B hB := by
    intro x A B hA hB hAB
    dsimp only [φ]
    rw [nu_union_disjoint P va hA hB hAB, indCLM_union_disjoint P hA hB hAB]
    change ‖x‖ * (nu P va A hA + nu P va B hB) +
        va (indCLM P hA (Lp.const ⊤ P x) + indCLM P hB (Lp.const ⊤ P x)) = _
    rw [map_add]
    ring
  have hφ_cont : ∀ x (H : ℕ → Set Ω) (hH : ∀ n, MeasurableSet (H n)),
      (∀ n, H (n + 1) ⊆ H n) → (⋂ n, H n = ∅) →
      Tendsto (fun n => φ x (H n) (hH n)) atTop (𝓝 0) := by
    intro x H hH hdec hinter
    have hlim := hva_adm H (hadm_of_inter H hH hdec hinter)
    have htop : Tendsto (fun n => 2 * ‖x‖ * nu P va (H n) (hH n)) atTop (𝓝 0) := by
      simpa using hlim.const_mul (2 * ‖x‖)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop
      (fun n => hφ_nonneg x (H n) (hH n)) (fun n => ?_)
    have h := (abs_le.mp (hφ_bound x (H n) (hH n))).2
    dsimp only [φ]
    linarith
  let lamMeas : X → Measure Ω := fun x =>
    measureOfContent (φ x) (hφ_nonneg x) (hφ_empty x) (hφ_add x) (hφ_cont x)
  have hlamMeas_apply : ∀ x A (hA : MeasurableSet A),
      lamMeas x A = ENNReal.ofReal (φ x A hA) :=
    fun x => measureOfContent_apply (φ x) _ _ _ _
  have hlamMeas_fin : ∀ x, IsFiniteMeasure (lamMeas x) := fun x =>
    ⟨by rw [hlamMeas_apply x _ .univ]; exact ENNReal.ofReal_lt_top⟩
  have hlamMeas_ac : ∀ x, lamMeas x ≪ P := fun x =>
    Measure.AbsolutelyContinuous.mk fun A hA hPA => by
      rw [hlamMeas_apply x A hA]
      have h0 : φ x A hA = 0 := by
        simp [φ, nu_eq_zero_of_measure_zero P va hA hPA,
          indCLM_eq_zero_of_measure_zero P hA hPA]
      rw [h0, ENNReal.ofReal_zero]
  let f : X → Ω → ℝ := fun x ω => ((lamMeas x).rnDeriv P ω).toReal - ‖x‖ * g ω
  have hf_meas : ∀ x, Measurable (f x) := fun x =>
    (Measure.measurable_rnDeriv (lamMeas x) P).ennreal_toReal.sub (measurable_const.mul hg_meas)
  have hf_int : ∀ x, Integrable (f x) P := fun x => by
    have := hlamMeas_fin x
    exact Measure.integrable_toReal_rnDeriv.sub (hg_int.const_mul ‖x‖)
  have hf_setInt : ∀ x A (hA : MeasurableSet A),
      ∫ ω in A, f x ω ∂P = va (indCLM P hA (Lp.const ⊤ P x)) := by
    intro x A hA
    have := hlamMeas_fin x
    have h1 : IntegrableOn (fun ω => ((lamMeas x).rnDeriv P ω).toReal) A P :=
      Measure.integrable_toReal_rnDeriv.integrableOn
    have h2 : IntegrableOn (fun ω => ‖x‖ * g ω) A P :=
      (hg_int.const_mul ‖x‖).integrableOn
    dsimp only [f]
    rw [integral_sub h1 h2, integral_const_mul, hg_setInt A hA,
      Measure.setIntegral_toReal_rnDeriv (hlamMeas_ac x), Measure.real,
      hlamMeas_apply x A hA, ENNReal.toReal_ofReal (hφ_nonneg x A hA)]
    dsimp only [φ]
    ring
  have hf_ae_bound : ∀ x, ∀ᵐ ω ∂P, |f x ω| ≤ g ω * ‖x‖ := by
    intro x
    have hupper : ∀ᵐ ω ∂P, 0 ≤ g ω * ‖x‖ - f x ω := by
      refine ae_nonneg_of_forall_setIntegral_nonneg
        ((hg_meas.mul measurable_const).sub (hf_meas x))
        ((hg_int.mul_const ‖x‖).sub (hf_int x)) fun A hA => ?_
      rw [integral_sub (hg_int.mul_const ‖x‖).integrableOn (hf_int x).integrableOn,
        integral_mul_const, hg_setInt A hA, hf_setInt x A hA]
      have h := (abs_le.mp (hφ_bound x A hA)).2
      linarith
    have hlower : ∀ᵐ ω ∂P, 0 ≤ g ω * ‖x‖ + f x ω := by
      refine ae_nonneg_of_forall_setIntegral_nonneg
        ((hg_meas.mul measurable_const).add (hf_meas x))
        ((hg_int.mul_const ‖x‖).add (hf_int x)) fun A hA => ?_
      rw [integral_add (hg_int.mul_const ‖x‖).integrableOn (hf_int x).integrableOn,
        integral_mul_const, hg_setInt A hA, hf_setInt x A hA]
      have h := (abs_le.mp (hφ_bound x A hA)).1
      linarith
    filter_upwards [hupper, hlower] with ω h1 h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- Step 3: Countable dense ℚ-linear subset D ⊆ X
  obtain ⟨S, hS_count, hS_dense⟩ := TopologicalSpace.exists_countable_dense X
  have : Countable S := hS_count.to_subtype
  let qSpanFun : (S →₀ ℚ) → X := fun c => c.sum fun s q => (q : ℝ) • (s : X)
  let D : Set X := Set.range qSpanFun
  have hS_sub_D : S ⊆ D := by
    intro x hx
    refine ⟨Finsupp.single ⟨x, hx⟩ (1 : ℚ), ?_⟩
    simp [qSpanFun]
  have hD_dense : Dense D := hS_dense.mono hS_sub_D
  have hD_count : D.Countable := Set.countable_range qSpanFun
  have : Countable D := hD_count.to_subtype
  have hD_add : ∀ {x y : X}, x ∈ D → y ∈ D → x + y ∈ D := by
    rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
    refine ⟨c₁ + c₂, ?_⟩
    dsimp only [qSpanFun]
    rw [Finsupp.sum_add_index (fun _ => by simp) (fun s q₁ q₂ => by simp [add_smul])]
  have hD_smul : ∀ (q : ℚ) {x : X}, x ∈ D → (q : ℝ) • x ∈ D := by
    rintro q _ ⟨c, rfl⟩
    refine ⟨q • c, ?_⟩
    dsimp only [qSpanFun]
    rw [Finsupp.sum_of_support_subset (q • c) (Finsupp.support_smul (b := q) (g := c)) _
      (fun _ _ => by simp)]
    rw [Finsupp.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Rat.cast_mul, mul_smul]
  have hD_sub : ∀ {x y : X}, x ∈ D → y ∈ D → x - y ∈ D := by
    intro x y hx hy
    rw [sub_eq_add_neg, show -y = ((-1 : ℚ) : ℝ) • y by simp]
    exact hD_add hx (hD_smul (-1 : ℚ) hy)
  -- Step 4: Countable union of null measurable exception sets
  have hf_add_ae : ∀ x₁ x₂ : X, ∀ᵐ ω ∂P, f (x₁ + x₂) ω = f x₁ ω + f x₂ ω := by
    intro x₁ x₂
    refine Integrable.ae_eq_of_forall_setIntegral_eq (f (x₁ + x₂)) (fun ω => f x₁ ω + f x₂ ω)
      (hf_int (x₁ + x₂)) ((hf_int x₁).add (hf_int x₂)) fun A hA _ => ?_
    rw [integral_add (hf_int x₁).integrableOn (hf_int x₂).integrableOn,
      hf_setInt (x₁ + x₂) A hA, hf_setInt x₁ A hA, hf_setInt x₂ A hA,
      map_add (Lp.const ⊤ P), map_add, map_add]
  have hf_smul_ae : ∀ (q : ℚ) (x : X), ∀ᵐ ω ∂P, f ((q : ℝ) • x) ω = (q : ℝ) * f x ω := by
    intro q x
    refine Integrable.ae_eq_of_forall_setIntegral_eq (f ((q : ℝ) • x)) (fun ω => (q : ℝ) * f x ω)
      (hf_int ((q : ℝ) • x)) ((hf_int x).const_mul (q : ℝ)) fun A hA _ => ?_
    rw [integral_const_mul, hf_setInt ((q : ℝ) • x) A hA, hf_setInt x A hA]
    have hconst : Lp.const ⊤ P ((q : ℝ) • x) = (q : ℝ) • Lp.const ⊤ P x :=
      (Lp.constₗ ⊤ P ℝ).map_smul (q : ℝ) x
    rw [hconst, map_smul, map_smul, smul_eq_mul]
  let E_add : D × D → Set Ω := fun p => {ω | f (p.1.1 + p.2.1) ω ≠ f p.1.1 ω + f p.2.1 ω}
  let E_smul : ℚ × D → Set Ω := fun p => {ω | f ((p.1 : ℝ) • p.2.1) ω ≠ (p.1 : ℝ) * f p.2.1 ω}
  let E_bd : D → Set Ω := fun d => {ω | g ω * ‖d.1‖ < |f d.1 ω|}
  let N : Set Ω := (⋃ p : D × D, E_add p) ∪ (⋃ p : ℚ × D, E_smul p) ∪ (⋃ d : D, E_bd d)
  have hN_meas : MeasurableSet N := by
    refine ((MeasurableSet.iUnion fun p => ?_).union (MeasurableSet.iUnion fun p => ?_)).union
      (MeasurableSet.iUnion fun d => ?_)
    · exact (measurableSet_eq_fun (hf_meas _) ((hf_meas _).add (hf_meas _))).compl
    · exact (measurableSet_eq_fun (hf_meas _) (measurable_const.mul (hf_meas _))).compl
    · exact measurableSet_lt (hg_meas.mul measurable_const) (hf_meas _).abs
  have hN_null : P N = 0 := by
    refine measure_union_null (measure_union_null ?_ ?_) ?_
    · refine measure_iUnion_null fun p => ?_
      exact measure_mono_null (fun ω h => h) (ae_iff.mp (hf_add_ae p.1.1 p.2.1))
    · refine measure_iUnion_null fun p => ?_
      exact measure_mono_null (fun ω h => h) (ae_iff.mp (hf_smul_ae p.1 p.2.1))
    · refine measure_iUnion_null fun d => ?_
      have h := ae_iff.mp (hf_ae_bound d.1)
      refine measure_mono_null (fun ω hω => ?_) h
      exact not_le.mpr hω
  -- Step 5: Construct xs : Ω → StrongDual ℝ X by continuous extension from D
  have hgood_add : ∀ ω ∉ N, ∀ d₁ d₂ : D, f (d₁.1 + d₂.1) ω = f d₁.1 ω + f d₂.1 ω := by
    intro ω hω d₁ d₂
    by_contra hne
    exact hω (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨(d₁, d₂), hne⟩)))
  have hgood_smul : ∀ ω ∉ N, ∀ (q : ℚ) (d : D), f ((q : ℝ) • d.1) ω = (q : ℝ) * f d.1 ω := by
    intro ω hω q d
    by_contra hne
    exact hω (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨(q, d), hne⟩)))
  have hgood_bd : ∀ ω ∉ N, ∀ d : D, |f d.1 ω| ≤ g ω * ‖d.1‖ := by
    intro ω hω d
    by_contra hgt
    exact hω (Or.inr (Set.mem_iUnion.mpr ⟨d, not_le.mp hgt⟩))
  have hgood_sub : ∀ ω ∉ N, ∀ d₁ d₂ : D, f d₁.1 ω - f d₂.1 ω = f (d₁.1 - d₂.1) ω := by
    intro ω hω d₁ d₂
    have h1 := hgood_add ω hω d₂ ⟨d₁.1 - d₂.1, hD_sub d₁.2 d₂.2⟩
    have h2 : d₂.1 + (d₁.1 - d₂.1) = d₁.1 := add_sub_cancel d₂.1 d₁.1
    rw [h2] at h1
    linarith
  have hL_uc : ∀ ω ∉ N, UniformContinuous (fun d : D => f d.1 ω) := by
    intro ω hω
    have hlip : LipschitzWith (Real.toNNReal (g ω)) (fun d : D => f d.1 ω) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro d₁ d₂
      rw [Real.dist_eq, hgood_sub ω hω d₁ d₂, Real.coe_toNNReal _ (hg_nonneg ω)]
      exact le_trans (hgood_bd ω hω ⟨d₁.1 - d₂.1, hD_sub d₁.2 d₂.2⟩)
        (by rw [Subtype.dist_eq, dist_eq_norm])
    exact hlip.uniformContinuous
  let extFun : Ω → X → ℝ := fun ω =>
    if ω ∈ N then 0 else hD_dense.extend (fun d : D => f d.1 ω)
  have hextFun_cont : ∀ ω, Continuous (extFun ω) := by
    intro ω
    dsimp only [extFun]
    split_ifs with hω
    · exact continuous_const
    · exact (hD_dense.uniformContinuous_extend (hL_uc ω hω)).continuous
  have hextFun_on_D : ∀ ω ∉ N, ∀ d : D, extFun ω d.1 = f d.1 ω := by
    intro ω hω d
    dsimp only [extFun]
    rw [if_neg hω]
    exact hD_dense.extend_of_ind (hL_uc ω hω) d
  have hD_ind : ∀ {Q : X → Prop}, IsClosed {x | Q x} → (∀ d ∈ D, Q d) → ∀ x, Q x :=
    fun hcl hsub x => (hD_dense.closure_eq ▸ closure_minimal hsub hcl) (Set.mem_univ x)
  have hextFun_add : ∀ ω (x y : X), extFun ω (x + y) = extFun ω x + extFun ω y := by
    intro ω x y
    by_cases hω : ω ∈ N
    · simp [extFun, hω]
    · have hstep1 : ∀ (d₁ : D) (y : X), extFun ω (d₁.1 + y) = extFun ω d₁.1 + extFun ω y := by
        intro d₁
        refine hD_ind
          (isClosed_eq ((hextFun_cont ω).comp (continuous_const.add continuous_id))
            (continuous_const.add (hextFun_cont ω))) ?_
        intro d₂ hd₂
        change extFun ω (d₁.1 + d₂) = extFun ω d₁.1 + extFun ω d₂
        rw [hextFun_on_D ω hω ⟨d₁.1 + d₂, hD_add d₁.2 hd₂⟩,
          hextFun_on_D ω hω d₁, hextFun_on_D ω hω ⟨d₂, hd₂⟩]
        exact hgood_add ω hω d₁ ⟨d₂, hd₂⟩
      refine hD_ind
        (isClosed_eq ((hextFun_cont ω).comp (continuous_id.add continuous_const))
          ((hextFun_cont ω).add continuous_const)) ?_ x
      intro d₁ hd₁
      exact hstep1 ⟨d₁, hd₁⟩ y
  have hextFun_smul : ∀ ω (c : ℝ) (x : X), extFun ω (c • x) = c * extFun ω x := by
    intro ω c x
    by_cases hω : ω ∈ N
    · simp [extFun, hω]
    · have hstep1 : ∀ (d : D) (c : ℝ), extFun ω (c • d.1) = c * extFun ω d.1 := by
        intro d c
        refine Rat.denseRange_cast.induction_on c
          (isClosed_eq ((hextFun_cont ω).comp (continuous_id.smul continuous_const))
            (continuous_id.mul continuous_const)) ?_
        intro q
        change extFun ω ((q : ℝ) • d.1) = (q : ℝ) * extFun ω d.1
        rw [hextFun_on_D ω hω ⟨(q : ℝ) • d.1, hD_smul q d.2⟩, hextFun_on_D ω hω d]
        exact hgood_smul ω hω q d
      refine hD_ind
        (isClosed_eq ((hextFun_cont ω).comp (continuous_const.smul continuous_id))
          (continuous_const.mul (hextFun_cont ω))) ?_ x
      intro d hd
      exact hstep1 ⟨d, hd⟩ c
  have hextFun_bd : ∀ ω (x : X), ‖extFun ω x‖ ≤ g ω * ‖x‖ := by
    intro ω x
    by_cases hω : ω ∈ N
    · simp only [extFun, if_pos hω, Pi.zero_apply, norm_zero]
      exact mul_nonneg (hg_nonneg ω) (norm_nonneg x)
    · refine hD_ind
        (isClosed_le (hextFun_cont ω).norm (continuous_const.mul continuous_norm)) ?_ x
      intro d hd
      change |extFun ω d| ≤ g ω * ‖d‖
      rw [hextFun_on_D ω hω ⟨d, hd⟩]
      exact hgood_bd ω hω ⟨d, hd⟩
  let xs : Ω → StrongDual ℝ X := fun ω =>
    LinearMap.mkContinuous
      { toFun := extFun ω
        map_add' := hextFun_add ω
        map_smul' := fun c x => by simpa [smul_eq_mul] using hextFun_smul ω c x }
      (g ω)
      (hextFun_bd ω)
  have hxs_apply : ∀ ω x, xs ω x = extFun ω x := fun _ _ => rfl
  have hxs_norm_le : ∀ ω, ‖xs ω‖ ≤ g ω := fun ω =>
    LinearMap.mkContinuous_norm_le _ (hg_nonneg ω) (hextFun_bd ω)
  -- Step 6: Verify xs ∈ Lambda1 X P
  have hxs_wmeas : ∀ x : X, Measurable fun ω => xs ω x := by
    intro x
    have hex_seq : ∀ k : ℕ, ∃ d : D, dist d.1 x < 1 / ((k : ℝ) + 1) := by
      intro k
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hmem : x ∈ closure (D : Set X) := by rw [hD_dense.closure_eq]; exact Set.mem_univ x
      obtain ⟨y, hyD, hdist⟩ := Metric.mem_closure_iff.mp hmem (1 / ((k : ℝ) + 1)) hpos
      exact ⟨⟨y, hyD⟩, by rwa [dist_comm]⟩
    choose seqD hseqD using hex_seq
    have hseq_lim : Tendsto (fun k => (seqD k).1) atTop (𝓝 x) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
      refine ⟨K, fun k hk => ?_⟩
      have hk_le : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
      exact lt_trans (hseqD k) (lt_of_le_of_lt hk_le hK)
    refine measurable_of_tendsto_metrizable (f := fun k ω => Nᶜ.indicator (f (seqD k).1) ω)
      (fun k => (hf_meas (seqD k).1).indicator hN_meas.compl) ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ N
    · have h0 : (fun k => Nᶜ.indicator (f (seqD k).1) ω) = fun _ => (0 : ℝ) := by
        ext k; exact Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω) _
      rw [h0, hxs_apply]
      simp only [extFun, if_pos hω, Pi.zero_apply]
      exact tendsto_const_nhds
    · have heq : (fun k => Nᶜ.indicator (f (seqD k).1) ω) = fun k => xs ω (seqD k).1 := by
        ext k
        rw [Set.indicator_of_mem (Set.mem_compl hω), hxs_apply, hextFun_on_D ω hω (seqD k)]
      rw [heq]
      exact ((xs ω).continuous.tendsto x).comp hseq_lim
  have hxs_lint : ∫⁻ ω, ‖xs ω‖ₑ ∂P < ⊤ := by
    have hmono : ∀ ω, ‖xs ω‖ₑ ≤ μ.rnDeriv P ω := by
      intro ω
      calc ‖xs ω‖ₑ = ENNReal.ofReal ‖xs ω‖ := (ofReal_norm (xs ω)).symm
        _ ≤ ENNReal.ofReal (g ω) := ENNReal.ofReal_le_ofReal (hxs_norm_le ω)
        _ ≤ μ.rnDeriv P ω := ENNReal.ofReal_toReal_le
    calc ∫⁻ ω, ‖xs ω‖ₑ ∂P ≤ ∫⁻ ω, μ.rnDeriv P ω ∂P := lintegral_mono hmono
      _ ≤ μ Set.univ := Measure.lintegral_rnDeriv_le
      _ < ⊤ := measure_lt_top μ Set.univ
  have hxs_mem : xs ∈ Lambda1 X P := ⟨hxs_wmeas, hxs_lint⟩
  -- Step 7: Representation identity on indicators of constants, then all y ∈ Lp X ⊤ P
  have hrep_ind_D : ∀ (d : D) (A : Set Ω) (hA : MeasurableSet A),
      va (indCLM P hA (Lp.const ⊤ P d.1)) = ∫ ω in A, xs ω d.1 ∂P := by
    intro d A hA
    rw [← hf_setInt d.1 A hA]
    apply setIntegral_congr_ae hA
    have hae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.mp hN_null
    filter_upwards [hae] with ω hω _
    rw [hxs_apply, hextFun_on_D ω hω d]
  have hrep_ind : ∀ (x : X) (A : Set Ω) (hA : MeasurableSet A),
      va (indCLM P hA (Lp.const ⊤ P x)) = ∫ ω in A, xs ω x ∂P := by
    intro x A hA
    have hex_seq : ∀ k : ℕ, ∃ d : D, dist d.1 x < 1 / ((k : ℝ) + 1) := by
      intro k
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hmem : x ∈ closure (D : Set X) := by rw [hD_dense.closure_eq]; exact Set.mem_univ x
      obtain ⟨y, hyD, hdist⟩ := Metric.mem_closure_iff.mp hmem (1 / ((k : ℝ) + 1)) hpos
      exact ⟨⟨y, hyD⟩, by rwa [dist_comm]⟩
    choose seqD hseqD using hex_seq
    have hseq_lim : Tendsto (fun k => (seqD k).1) atTop (𝓝 x) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
      refine ⟨K, fun k hk => ?_⟩
      have hk_le : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
      exact lt_trans (hseqD k) (lt_of_le_of_lt hk_le hK)
    have hlhs : Tendsto (fun k => va (indCLM P hA (Lp.const ⊤ P (seqD k).1)))
        atTop (𝓝 (va (indCLM P hA (Lp.const ⊤ P x)))) := by
      have hcont : Continuous (fun z : X => va (indCLM P hA (Lp.constL ⊤ P ℝ z))) :=
        va.continuous.comp ((indCLM P hA).continuous.comp (Lp.constL ⊤ P ℝ).continuous)
      exact (hcont.tendsto x).comp hseq_lim
    have hrhs : Tendsto (fun k => ∫ ω in A, xs ω (seqD k).1 ∂P)
        atTop (𝓝 (∫ ω in A, xs ω x ∂P)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hC_nonneg : 0 ≤ ∫ ω in A, g ω ∂P :=
        setIntegral_nonneg hA (fun ω _ => hg_nonneg ω)
      have hδ : 0 < ε / (∫ ω in A, g ω ∂P + 1) := div_pos hε (by linarith)
      obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hseq_lim) _ hδ
      refine ⟨K, fun k hk => ?_⟩
      have hint_k : IntegrableOn (fun ω => xs ω (seqD k).1) A P := by
        refine (integrable_lam P xs hxs_mem (Lp.const ⊤ P (seqD k).1)).congr ?_ |>.integrableOn
        filter_upwards [Lp.coeFn_const ⊤ P (seqD k).1] with ω hω
        rw [hω]; rfl
      have hint_x : IntegrableOn (fun ω => xs ω x) A P := by
        refine (integrable_lam P xs hxs_mem (Lp.const ⊤ P x)).congr ?_ |>.integrableOn
        filter_upwards [Lp.coeFn_const ⊤ P x] with ω hω
        rw [hω]; rfl
      rw [Real.dist_eq, ← integral_sub hint_k hint_x]
      have hsub_eq : (fun ω => xs ω (seqD k).1 - xs ω x) = fun ω => xs ω ((seqD k).1 - x) := by
        ext ω; exact (map_sub (xs ω) _ _).symm
      rw [hsub_eq]
      calc |∫ ω in A, xs ω ((seqD k).1 - x) ∂P|
          ≤ ∫ ω in A, ‖xs ω ((seqD k).1 - x)‖ ∂P := by
            simpa only [Real.norm_eq_abs] using
              norm_integral_le_integral_norm (fun ω => xs ω ((seqD k).1 - x))
        _ ≤ ∫ ω in A, g ω * ‖(seqD k).1 - x‖ ∂P := by
            refine setIntegral_mono_on (hint_k.sub hint_x |>.congr (Eventually.of_forall fun ω => by
                exact (map_sub (xs ω) _ _).symm) |>.norm)
              (hg_int.mul_const _).integrableOn hA fun ω _ => ?_
            calc ‖xs ω ((seqD k).1 - x)‖
                ≤ ‖xs ω‖ * ‖(seqD k).1 - x‖ := (xs ω).le_opNorm _
              _ ≤ g ω * ‖(seqD k).1 - x‖ :=
                  mul_le_mul_of_nonneg_right (hxs_norm_le ω) (norm_nonneg _)
        _ = (∫ ω in A, g ω ∂P) * dist (seqD k).1 x := by
            rw [integral_mul_const, dist_eq_norm]
        _ ≤ (∫ ω in A, g ω ∂P) * (ε / (∫ ω in A, g ω ∂P + 1)) :=
            mul_le_mul_of_nonneg_left (hK k hk).le hC_nonneg
        _ < ε := by
            have hden : 0 < ∫ ω in A, g ω ∂P + 1 := by linarith
            rw [mul_div_assoc', div_lt_iff₀ hden]
            nlinarith
    have heq : (fun k => va (indCLM P hA (Lp.const ⊤ P (seqD k).1))) =
        fun k => ∫ ω in A, xs ω (seqD k).1 ∂P := by
      ext k; exact hrep_ind_D (seqD k) A hA
    rw [heq] at hlhs
    exact tendsto_nhds_unique hlhs hrhs
  have hrep_ind_full : ∀ (x : X) (A : Set Ω) (hA : MeasurableSet A),
      va (indCLM P hA (Lp.const ⊤ P x)) =
        ∫ ω, xs ω (indCLM P hA (Lp.const ⊤ P x) ω) ∂P := by
    intro x A hA
    rw [hrep_ind x A hA, ← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [indCLM_ae P hA (Lp.const ⊤ P x), Lp.coeFn_const ⊤ P x] with ω h1 h2
    rw [h1]
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, h2]; rfl
    · simp [Set.indicator_of_notMem hω]
  -- Step 8: Extend representation to arbitrary y ∈ Lp X ⊤ P via countable disjoint partition
  refine ⟨xs, hxs_mem, fun y => ?_⟩
  have : Nonempty X := ⟨0⟩
  obtain ⟨c, hc_dense⟩ := TopologicalSpace.exists_dense_seq X
  have hIy_diff : ∀ ε > 0, |va y - ∫ ω, xs ω (y ω) ∂P| ≤ (‖va‖ + nu P va Set.univ .univ) * ε := by
    intro ε hε
    let hy := Lp.aestronglyMeasurable y
    let y₀ : Ω → X := hy.mk y
    have hy₀_sm : StronglyMeasurable y₀ := hy.stronglyMeasurable_mk
    have hy₀_ae : y =ᵐ[P] y₀ := hy.ae_eq_mk
    let B : ℕ → Set Ω := fun k => {ω | dist (y₀ ω) (c k) < ε}
    have hB_meas : ∀ k, MeasurableSet (B k) := fun k =>
      measurableSet_lt
        ((continuous_id.dist continuous_const).comp_stronglyMeasurable hy₀_sm).measurable
        measurable_const
    have hB_cover : ⋃ k, B k = Set.univ := by
      ext ω
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true, B, Set.mem_ofPred_eq]
      exact Metric.denseRange_iff.mp hc_dense (y₀ ω) ε hε
    let A : ℕ → Set Ω := disjointed B
    have hA_meas : ∀ k, MeasurableSet (A k) := MeasurableSet.disjointed hB_meas
    have hA_disj : Pairwise (Function.onFun Disjoint A) := disjoint_disjointed B
    have hA_cover : ⋃ k, A k = Set.univ := by rw [iUnion_disjointed, hB_cover]
    have hA_sub : ∀ k, A k ⊆ B k := fun k => disjointed_subset B k
    let U : ℕ → Set Ω := fun N => ⋃ k ∈ Finset.range N, A k
    let T : ℕ → Set Ω := fun N => (U N)ᶜ
    have hU_meas : ∀ N, MeasurableSet (U N) := fun N =>
      Finset.measurableSet_biUnion _ (fun k _ => hA_meas k)
    have hT_meas : ∀ N, MeasurableSet (T N) := fun N => (hU_meas N).compl
    have hT_dec : ∀ N, T (N + 1) ⊆ T N := by
      intro N ω hω hU
      apply hω
      simp only [U, Set.mem_iUnion, Finset.mem_range] at hU ⊢
      obtain ⟨k, hk, hωk⟩ := hU
      exact ⟨k, Nat.lt_succ_of_lt hk, hωk⟩
    have hT_inter : ⋂ N, T N = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
      intro hall
      have hmem : ω ∈ ⋃ k, A k := by rw [hA_cover]; exact Set.mem_univ ω
      obtain ⟨k, hωk⟩ := Set.mem_iUnion.mp hmem
      have hUk : ω ∈ U (k + 1) := by
        simp only [U, Set.mem_iUnion, Finset.mem_range]
        exact ⟨k, Nat.lt_succ_self k, hωk⟩
      exact hall (k + 1) hUk
    have hT_lim : Tendsto (fun N => nu P va (T N) (hT_meas N)) atTop (𝓝 0) :=
      hva_adm T (hadm_of_inter T hT_meas hT_dec hT_inter)
    -- Define finite simple approximations s N
    let s : ℕ → Lp X ⊤ P := fun N =>
      ∑ k ∈ Finset.range N, indCLM P (hA_meas k) (Lp.const ⊤ P (c k))
    have hs_rep : ∀ N, va (s N) = ∫ ω, xs ω (s N ω) ∂P := by
      intro N
      dsimp only [s]
      rw [map_sum]
      have h1 : ∑ k ∈ Finset.range N, va (indCLM P (hA_meas k) (Lp.const ⊤ P (c k))) =
          ∑ k ∈ Finset.range N, ∫ ω, xs ω (indCLM P (hA_meas k) (Lp.const ⊤ P (c k)) ω) ∂P :=
        Finset.sum_congr rfl (fun k _ => hrep_ind_full (c k) (A k) (hA_meas k))
      rw [h1, ← integral_finsetSum _ (fun k _ => integrable_lam P xs hxs_mem _)]
      apply integral_congr_ae
      filter_upwards [coeFn_finset_sum P (Finset.range N)
        (fun k => indCLM P (hA_meas k) (Lp.const ⊤ P (c k)))] with ω hω
      rw [hω, map_sum]
    have hstep_N : ∀ N, |va y - ∫ ω, xs ω (y ω) ∂P| ≤
        (‖va‖ + nu P va Set.univ .univ) * ε + 2 * ‖y‖ * nu P va (T N) (hT_meas N) := by
      intro N
      have hs_ae : ∀ᵐ ω ∂P, s N ω =
          ∑ k ∈ Finset.range N, (A k).indicator (fun _ => c k) ω := by
        have h1 : ∀ k ∈ Finset.range N,
            ∀ᵐ ω ∂P, indCLM P (hA_meas k) (Lp.const ⊤ P (c k)) ω =
              (A k).indicator (fun _ => c k) ω := by
          intro k _
          filter_upwards [indCLM_ae P (hA_meas k) (Lp.const ⊤ P (c k)),
            Lp.coeFn_const ⊤ P (c k)] with ω ha hb
          rw [ha]
          by_cases hω : ω ∈ A k
          · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, hb]; rfl
          · simp [Set.indicator_of_notMem hω]
        have hall : ∀ᵐ ω ∂P, ∀ k ∈ Finset.range N,
            indCLM P (hA_meas k) (Lp.const ⊤ P (c k)) ω = (A k).indicator (fun _ => c k) ω :=
          (ae_ball_iff (Finset.countable_toSet _)).mpr h1
        filter_upwards [coeFn_finset_sum P (Finset.range N)
          (fun k => indCLM P (hA_meas k) (Lp.const ⊤ P (c k))), hall] with ω hω1 hω2
        change (⇑(∑ k ∈ Finset.range N, indCLM P (hA_meas k) (Lp.const ⊤ P (c k))) ω) = _
        rw [hω1]
        exact Finset.sum_congr rfl hω2
      -- s N vanishes on T N
      have hs_zero_T : indCLM P (hT_meas N) (s N) = 0 := by
        apply indCLM_eq_zero_of_ae_zero
        filter_upwards [hs_ae] with ω hω hmemT
        rw [hω]
        refine Finset.sum_eq_zero fun k hk => ?_
        have hnotA : ω ∉ A k := fun hωk => hmemT (Set.mem_iUnion₂.mpr ⟨k, hk, hωk⟩)
        exact Set.indicator_of_notMem hnotA _
      -- Split y - s N = P_{U N}(y - s N) + P_{T N} y
      have hdecomp : y - s N = indCLM P (hU_meas N) (y - s N) + indCLM P (hT_meas N) y := by
        have h1 := congr_arg (fun L => L (y - s N)) (indCLM_add_compl (X := X) P (hU_meas N))
        change indCLM P (hU_meas N) (y - s N) + indCLM P (hT_meas N) (y - s N) = y - s N at h1
        rw [map_sub (indCLM P (hT_meas N)), hs_zero_T, sub_zero] at h1
        exact h1.symm
      -- Norm bound on U N: ‖P_{U N}(y - s N)‖ ≤ ε
      have hnorm_U : ‖indCLM P (hU_meas N) (y - s N)‖ ≤ ε := by
        rw [Lp.norm_def]
        have hle_enn : eLpNorm (indCLM P (hU_meas N) (y - s N)) ⊤ P ≤ ENNReal.ofReal ε := by
          rw [eLpNorm_exponent_top]
          apply eLpNormEssSup_le_of_ae_enorm_bound
          filter_upwards [indCLM_ae P (hU_meas N) (y - s N), Lp.coeFn_sub y (s N),
            hy₀_ae, hs_ae] with ω h1 h2 h3 h4
          rw [h1]
          by_cases hωU : ω ∈ U N
          · rw [Set.indicator_of_mem hωU, h2, Pi.sub_apply, h3, h4]
            simp only [U, Set.mem_iUnion, Finset.mem_range] at hωU
            obtain ⟨k, hk, hωk⟩ := hωU
            have hsum_k : ∑ j ∈ Finset.range N, (A j).indicator (fun _ => c j) ω = c k := by
              rw [Finset.sum_eq_single k]
              · exact Set.indicator_of_mem hωk _
              · intro j _ hjk
                have hnotj : ω ∉ A j := Set.disjoint_left.mp (hA_disj hjk.symm) hωk
                exact Set.indicator_of_notMem hnotj _
              · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
            rw [hsum_k]
            have hdist : ‖y₀ ω - c k‖ < ε := by
              rw [← dist_eq_norm]
              exact hA_sub k hωk
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal hdist.le
          · simp [Set.indicator_of_notMem hωU]
        calc (eLpNorm (indCLM P (hU_meas N) (y - s N)) ⊤ P).toReal
            ≤ (ENNReal.ofReal ε).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle_enn
          _ = ε := ENNReal.toReal_ofReal hε.le
      -- Bound |va y - va (s N)|
      have hva_diff : |va y - va (s N)| ≤ ‖va‖ * ε + ‖y‖ * nu P va (T N) (hT_meas N) := by
        rw [← map_sub, hdecomp, map_add]
        have h1 : |va (indCLM P (hU_meas N) (y - s N))| ≤ ‖va‖ * ε := by
          calc ‖va (indCLM P (hU_meas N) (y - s N))‖
              ≤ ‖va‖ * ‖indCLM P (hU_meas N) (y - s N)‖ := va.le_opNorm _
            _ ≤ ‖va‖ * ε := mul_le_mul_of_nonneg_left hnorm_U (norm_nonneg va)
        have h2 : |va (indCLM P (hT_meas N) y)| ≤ ‖y‖ * nu P va (T N) (hT_meas N) := by
          calc ‖(va.comp (indCLM P (hT_meas N))) y‖
              ≤ nu P va (T N) (hT_meas N) * ‖y‖ := (va.comp _).le_opNorm y
            _ = ‖y‖ * nu P va (T N) (hT_meas N) := mul_comm _ _
        exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
      -- Bound |∫ xs (y) - ∫ xs (s N)|
      have hI_diff : |∫ ω, xs ω (y ω) ∂P - ∫ ω, xs ω (s N ω) ∂P| ≤
          nu P va Set.univ .univ * ε + ‖y‖ * nu P va (T N) (hT_meas N) := by
        have hint_y := integrable_lam P xs hxs_mem y
        have hint_s := integrable_lam P xs hxs_mem (s N)
        have hint_U := integrable_lam P xs hxs_mem (indCLM P (hU_meas N) (y - s N))
        have hint_T := integrable_lam P xs hxs_mem (indCLM P (hT_meas N) y)
        have hsub_int : ∫ ω, xs ω (y ω) ∂P - ∫ ω, xs ω (s N ω) ∂P =
            ∫ ω, xs ω (indCLM P (hU_meas N) (y - s N) ω) ∂P +
            ∫ ω, xs ω (indCLM P (hT_meas N) y ω) ∂P := by
          rw [← integral_sub hint_y hint_s, ← integral_add hint_U hint_T]
          apply integral_congr_ae
          have hsub_ae := Lp.coeFn_sub y (s N)
          have hadd_ae := Lp.coeFn_add (indCLM P (hU_meas N) (y - s N)) (indCLM P (hT_meas N) y)
          have hdec_eq : (⇑(y - s N) : Ω → X) =
              ⇑(indCLM P (hU_meas N) (y - s N) + indCLM P (hT_meas N) y) :=
            congrArg (fun z : Lp X ⊤ P => (z : Ω → X)) hdecomp
          filter_upwards [hsub_ae, hadd_ae] with ω h1 h2
          rw [← map_sub (xs ω), ← Pi.sub_apply, ← h1, hdec_eq, h2, Pi.add_apply, map_add]
        rw [hsub_int]
        have hI_U : |∫ ω, xs ω (indCLM P (hU_meas N) (y - s N) ω) ∂P| ≤
            nu P va Set.univ .univ * ε := by
          calc |∫ ω, xs ω (indCLM P (hU_meas N) (y - s N) ω) ∂P|
              ≤ ∫ ω, ‖xs ω (indCLM P (hU_meas N) (y - s N) ω)‖ ∂P := by
                simpa only [Real.norm_eq_abs] using
                  norm_integral_le_integral_norm
                    (fun ω => xs ω (indCLM P (hU_meas N) (y - s N) ω))
            _ ≤ ∫ ω, g ω * ε ∂P := by
                refine integral_mono_ae hint_U.norm (hg_int.mul_const ε) ?_
                have hle_ess : ∀ᵐ ω ∂P, ‖indCLM P (hU_meas N) (y - s N) ω‖ ≤ ε := by
                  have h1 := ae_le_eLpNormEssSup
                    (f := fun ω => indCLM P (hU_meas N) (y - s N) ω) (μ := P)
                  filter_upwards [h1] with ω hω
                  have hfin : eLpNorm (indCLM P (hU_meas N) (y - s N)) ⊤ P ≠ ⊤ :=
                    (Lp.eLpNorm_lt_top _).ne
                  rw [← eLpNorm_exponent_top] at hω
                  have h2 := ENNReal.toReal_mono hfin hω
                  rw [← Lp.norm_def] at h2
                  exact le_trans (by simpa using h2) hnorm_U
                filter_upwards [hle_ess] with ω hω
                calc ‖xs ω (indCLM P (hU_meas N) (y - s N) ω)‖
                    ≤ ‖xs ω‖ * ‖indCLM P (hU_meas N) (y - s N) ω‖ := (xs ω).le_opNorm _
                  _ ≤ g ω * ε := mul_le_mul (hxs_norm_le ω) hω (norm_nonneg _) (hg_nonneg ω)
            _ = (∫ ω, g ω ∂P) * ε := integral_mul_const _ _
            _ = (∫ ω in Set.univ, g ω ∂P) * ε := by rw [Measure.restrict_univ]
            _ = nu P va Set.univ .univ * ε := by rw [hg_setInt Set.univ .univ]
        have hI_T : |∫ ω, xs ω (indCLM P (hT_meas N) y ω) ∂P| ≤
            ‖y‖ * nu P va (T N) (hT_meas N) := by
          have hT_eq : ∫ ω, xs ω (indCLM P (hT_meas N) y ω) ∂P =
              ∫ ω in T N, xs ω (y ω) ∂P := by
            rw [← integral_indicator (hT_meas N)]
            apply integral_congr_ae
            filter_upwards [indCLM_ae P (hT_meas N) y] with ω hω
            rw [hω]
            by_cases hmem : ω ∈ T N
            · simp [Set.indicator_of_mem hmem]
            · simp [Set.indicator_of_notMem hmem]
          rw [hT_eq]
          calc |∫ ω in T N, xs ω (y ω) ∂P|
              ≤ ∫ ω in T N, ‖xs ω (y ω)‖ ∂P := by
                simpa only [Real.norm_eq_abs] using
                  norm_integral_le_integral_norm (fun ω => xs ω (y ω))
            _ ≤ ∫ ω in T N, g ω * ‖y‖ ∂P := by
                refine setIntegral_mono_ae_restrict hint_y.integrableOn.norm
                  (hg_int.mul_const ‖y‖).integrableOn ?_
                have hle_y : ∀ᵐ ω ∂P, ‖y ω‖ ≤ ‖y‖ := by
                  filter_upwards [ae_le_eLpNormEssSup (f := fun ω => y ω) (μ := P)] with ω hω
                  rw [← eLpNorm_exponent_top] at hω
                  have h2 := ENNReal.toReal_mono (Lp.eLpNorm_lt_top y).ne hω
                  rw [← Lp.norm_def] at h2
                  simpa using h2
                have hle_y' : ∀ᵐ ω ∂P.restrict (T N), ‖y ω‖ ≤ ‖y‖ :=
                  ae_restrict_of_ae hle_y
                filter_upwards [hle_y'] with ω hω
                calc ‖xs ω (y ω)‖
                    ≤ ‖xs ω‖ * ‖y ω‖ := (xs ω).le_opNorm _
                  _ ≤ g ω * ‖y‖ := mul_le_mul (hxs_norm_le ω) hω (norm_nonneg _) (hg_nonneg ω)
            _ = (∫ ω in T N, g ω ∂P) * ‖y‖ := integral_mul_const _ _
            _ = ‖y‖ * nu P va (T N) (hT_meas N) := by rw [hg_setInt (T N) (hT_meas N), mul_comm]
        exact le_trans (abs_add_le _ _) (add_le_add hI_U hI_T)
      have htri : |va y - ∫ ω, xs ω (y ω) ∂P| ≤
          |va y - va (s N)| + |∫ ω, xs ω (y ω) ∂P - ∫ ω, xs ω (s N ω) ∂P| := by
        have : va y - ∫ ω, xs ω (y ω) ∂P =
            (va y - va (s N)) - (∫ ω, xs ω (y ω) ∂P - ∫ ω, xs ω (s N ω) ∂P) := by
          rw [hs_rep N]; ring
        rw [this]
        exact abs_sub _ _
      linarith
    have hlim_rhs : Tendsto
        (fun N => (‖va‖ + nu P va Set.univ .univ) * ε + 2 * ‖y‖ * nu P va (T N) (hT_meas N))
        atTop (𝓝 ((‖va‖ + nu P va Set.univ .univ) * ε)) := by
      simpa using tendsto_const_nhds.add (hT_lim.const_mul (2 * ‖y‖))
    exact ge_of_tendsto hlim_rhs (Eventually.of_forall hstep_N)
  have hzero : |va y - ∫ ω, xs ω (y ω) ∂P| ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    rw [zero_add]
    set C : ℝ := ‖va‖ + nu P va Set.univ .univ
    have hC : 0 ≤ C := add_nonneg (norm_nonneg va) (nu_nonneg P va .univ)
    have hε : 0 < δ / (C + 1) := div_pos hδ (by linarith)
    calc |va y - ∫ ω, xs ω (y ω) ∂P|
        ≤ C * (δ / (C + 1)) := hIy_diff _ hε
      _ ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hzero)

end RepresentationPart

end ChanceStateCtrl.AlmostSure.Thm39Aux

open ChanceStateCtrl.AlmostSure ChanceStateCtrl.AlmostSure.Thm39Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] (v : StrongDual ℝ (Lp X ⊤ P)) :
    ∃ va vs : StrongDual ℝ (Lp X ⊤ P), IsAbsCont P va ∧ IsSingular P vs ∧ v = va + vs ∧
        ‖v‖ = ‖va‖ + ‖vs‖ := by
  obtain ⟨va, vs, hsing, hsplit, hnorm, hva_adm⟩ := decomp_exists P v
  exact ⟨va, vs, isAbsCont_of_vanish_admissible P va hva_adm, hsing, hsplit, hnorm⟩
