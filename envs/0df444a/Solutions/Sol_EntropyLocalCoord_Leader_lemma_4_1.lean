-- Prove2me | solution 1 for EntropyLocalCoord.Leader.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:34.833073+00:00
-- url     : https://prove2.me/submissions/ae771576-98e3-4292-94da-dfcfad4c991d

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model
import Definitions.Def_EntropyLocalCoord_Leader_Information

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace EntropyLocalCoord.Dev.CDF

open EntropyLocalCoord.Leader

section General

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSingletonClass β]
  (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → β)

lemma condProb_nonneg_le {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hX : Measurable[mΩ] X) (b : β) :
    ∀ᵐ ω ∂P, 0 ≤ condProb m P X b ω ∧ condProb m P X b ω ≤ 1 := by
  have hint : Integrable ((X ⁻¹' {b}).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator (hX (measurableSet_singleton b))
  have h0 : 0 ≤ᵐ[P] P[(X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) | m] :=
    condExp_nonneg (Filter.Eventually.of_forall (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω))
  have h1 : P[(X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[P] P[(fun _ => (1 : ℝ)) | m] :=
    condExp_mono hint (integrable_const _)
      (Filter.Eventually.of_forall (fun ω => Set.indicator_le_self' (fun _ _ => zero_le_one) ω))
  rw [condExp_const hm] at h1
  filter_upwards [h0, h1] with ω a b
  exact ⟨a, b⟩

lemma condProb_of_not_mem_range (m : MeasurableSpace Ω) (b : β) (hb : b ∉ Set.range X) :
    condProb m P X b = 0 := by
  have : X ⁻¹' {b} = ∅ := by
    ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact fun h => hb ⟨ω, h⟩
  unfold condProb
  rw [this, Set.indicator_empty]
  exact condExp_zero

lemma integrable_negMulLog_condProb {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hX : Measurable[mΩ] X)
    (b : β) : Integrable (fun ω => Real.negMulLog (condProb m P X b ω)) P := by
  have hsm : AEStronglyMeasurable[mΩ] (condProb m P X b) P :=
    (stronglyMeasurable_condExp (m := m) (f := (X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)))
      (μ := P)).mono hm |>.aestronglyMeasurable
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (Real.continuous_negMulLog.comp_aestronglyMeasurable hsm) ?_
  filter_upwards [condProb_nonneg_le P X hm hX b] with ω ⟨h0, h1⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg h0 h1)]
  have := Real.negMulLog_le_one_sub_self h0
  linarith

/-- `H(X | m) · log 2` as a finite sum of integrals (for finite-valued measurable `X`). -/
lemma condEntropy_mul_log (hfin : (Set.range X).Finite) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hX : Measurable[mΩ] X) :
    condEntropy m P X * Real.log 2 =
      ∑ b ∈ hfin.toFinset, ∫ ω, Real.negMulLog (condProb m P X b ω) ∂P := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold condEntropy
  rw [div_mul_cancel₀ _ hlog, ← integral_finsetSum]
  · congr 1
    ext ω
    apply finsum_eq_sum_of_support_subset
    intro b hb
    simp only [Function.mem_support] at hb
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
    by_contra h
    apply hb
    simp [condProb_of_not_mem_range P X m b h]
  · intro b _
    exact integrable_negMulLog_condProb P X hm hX b

/-- Trivial σ-algebra: conditional entropy is the entropy. -/
theorem condEntropy_bot (hX : Measurable[mΩ] X) :
    condEntropy ⊥ P X = entropy P X := by
  unfold condEntropy entropy
  congr 1
  have h : ∀ b, condProb ⊥ P X b = fun _ => P.real (X ⁻¹' {b}) := by
    intro b
    unfold condProb
    rw [condExp_bot]
    funext ω
    rw [integral_indicator_const _ (hX (measurableSet_singleton b))]
    simp
  simp_rw [h]
  simp

/-- If `X` is `m`-measurable then `H(X | m) = 0`. -/
theorem condEntropy_of_measurable (hfin : (Set.range X).Finite) {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) (hXm : Measurable[m] X) : condEntropy m P X = 0 := by
  have hX : Measurable[mΩ] X := hXm.mono hm le_rfl
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have := condEntropy_mul_log P X hfin hm hX
  have h0 : ∀ b ∈ hfin.toFinset, ∫ ω, Real.negMulLog (condProb m P X b ω) ∂P = 0 := by
    intro b _
    have hind : condProb m P X b = (X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) := by
      unfold condProb
      refine condExp_of_stronglyMeasurable hm ?_ ?_
      · exact (measurable_const.indicator (hXm (measurableSet_singleton b))).stronglyMeasurable
      · exact (integrable_const (1 : ℝ)).indicator (hX (measurableSet_singleton b))
    rw [hind]
    have : ∀ ω, Real.negMulLog ((X ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) ω) = 0 := by
      intro ω
      by_cases h : ω ∈ X ⁻¹' {b} <;> simp [h]
    simp [this]
  rw [Finset.sum_eq_zero h0] at this
  exact (mul_eq_zero.mp this).resolve_right hlog

end General

section Prefix

variable {Ω : Type*} {k : ℕ} {α : Fin k → Type*} [∀ l, MeasurableSpace (α l)]
  (Z : ∀ l, Ω → α l)

lemma sourceSigma_mono {T T' : Finset (Fin k)} (h : T ⊆ T') : sourceSigma Z T ≤ sourceSigma Z T' :=
  iSup_mono' (fun j => ⟨j, iSup_mono' (fun hj => ⟨h hj, le_rfl⟩)⟩)

lemma sourceSigma_le {mΩ : MeasurableSpace Ω} (hZ : ∀ l, Measurable (Z l)) (T : Finset (Fin k)) :
    sourceSigma Z T ≤ mΩ :=
  iSup₂_le (fun l _ => (hZ l).comap_le)

lemma prefixSigma_mono {j j' : ℕ} (h : j ≤ j') : prefixSigma Z j ≤ prefixSigma Z j' :=
  sourceSigma_mono Z (fun l hl => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢; omega)

lemma prefixSigma_zero : prefixSigma Z 0 = ⊥ := by
  simp [prefixSigma, sourceSigma]

lemma prefixSigma_k : prefixSigma Z k = sourceSigma Z Finset.univ := by
  have : (Finset.univ.filter (fun l : Fin k => (l : ℕ) < k)) = Finset.univ := by
    ext l; simp
  simp only [prefixSigma, this]

end Prefix

section Main

variable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSingletonClass β]
  {k : ℕ} {α : Fin k → Type*} [∀ l, MeasurableSpace (α l)]
  (P : Measure Ω) [IsProbabilityMeasure P] (Z : ∀ l, Ω → α l) (hZ : ∀ l, Measurable (Z l))
  (X : Ω → β)

end Main

end EntropyLocalCoord.Dev.CDF

end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory

namespace EntropyLocalCoord.Dev.Lem41

open EntropyLocalCoord.Leader EntropyLocalCoord.Dev.CDF

/-- The entropy gap `N a + N b - N (a+b)`. -/
noncomputable def dd (a b : ℝ) : ℝ := Real.negMulLog a + Real.negMulLog b - Real.negMulLog (a + b)

lemma dd_continuous : Continuous (fun p : ℝ × ℝ => dd p.1 p.2) := by
  unfold dd
  have := Real.continuous_negMulLog
  fun_prop

lemma dd_smul (t a b : ℝ) : dd (t * a) (t * b) = t * dd a b := by
  unfold dd
  have h : t * a + t * b = t * (a + b) := by ring
  rw [h, Real.negMulLog_mul, Real.negMulLog_mul, Real.negMulLog_mul]
  ring

lemma dd_persp (a b : ℝ) (hs : 0 < a + b) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    dd a b = (a + b) * (Real.negMulLog (a / (a + b)) + Real.negMulLog (b / (a + b))) := by
  have hs' : a + b ≠ 0 := hs.ne'
  have h1 : Real.negMulLog a = (a / (a + b)) * Real.negMulLog (a + b)
      + (a + b) * Real.negMulLog (a / (a + b)) := by
    rw [← Real.negMulLog_mul]; congr 1; field_simp
  have h2 : Real.negMulLog b = (b / (a + b)) * Real.negMulLog (a + b)
      + (a + b) * Real.negMulLog (b / (a + b)) := by
    rw [← Real.negMulLog_mul]; congr 1; field_simp
  unfold dd
  have h3 : a / (a + b) + b / (a + b) = 1 := by field_simp
  have h4 : (a / (a + b)) * Real.negMulLog (a + b) + (b / (a + b)) * Real.negMulLog (a + b)
      = Real.negMulLog (a + b) := by
    rw [← add_mul, h3, one_mul]
  linarith

lemma dd_super (a1 b1 a2 b2 : ℝ) (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1) (ha2 : 0 ≤ a2) (hb2 : 0 ≤ b2) :
    dd a1 b1 + dd a2 b2 ≤ dd (a1 + a2) (b1 + b2) := by
  rcases (add_nonneg ha1 hb1).eq_or_lt with h1 | h1
  · have : a1 = 0 := by linarith
    have : b1 = 0 := by linarith
    subst_vars; simp [dd]
  rcases (add_nonneg ha2 hb2).eq_or_lt with h2 | h2
  · have : a2 = 0 := by linarith
    have : b2 = 0 := by linarith
    subst_vars; simp [dd]
  set s1 := a1 + b1 with hs1
  set s2 := a2 + b2 with hs2
  have hS : 0 < s1 + s2 := by linarith
  have hSS : (a1 + a2) + (b1 + b2) = s1 + s2 := by rw [hs1, hs2]; ring
  have key : ∀ x1 x2 : ℝ, 0 ≤ x1 → 0 ≤ x2 → s1 * Real.negMulLog (x1 / s1)
      + s2 * Real.negMulLog (x2 / s2) ≤ (s1 + s2) * Real.negMulLog ((x1 + x2) / (s1 + s2)) := by
    intro x1 x2 hx1 hx2
    have hc := Real.concaveOn_negMulLog.2 (Set.mem_Ici.2 (div_nonneg hx1 h1.le))
      (Set.mem_Ici.2 (div_nonneg hx2 h2.le))
      (div_nonneg h1.le hS.le) (div_nonneg h2.le hS.le) (by field_simp)
    simp only [smul_eq_mul] at hc
    have e : s1 / (s1 + s2) * (x1 / s1) + s2 / (s1 + s2) * (x2 / s2) = (x1 + x2) / (s1 + s2) := by
      field_simp
    rw [e] at hc
    have := mul_le_mul_of_nonneg_left hc hS.le
    have e2 : (s1 + s2) * (s1 / (s1 + s2) * Real.negMulLog (x1 / s1)
        + s2 / (s1 + s2) * Real.negMulLog (x2 / s2))
        = s1 * Real.negMulLog (x1 / s1) + s2 * Real.negMulLog (x2 / s2) := by
      field_simp
    linarith
  rw [dd_persp a1 b1 h1 ha1 hb1, dd_persp a2 b2 h2 ha2 hb2,
    dd_persp (a1 + a2) (b1 + b2) (by linarith) (by linarith) (by linarith), hSS]
  have ka := key a1 a2 ha1 ha2
  have kb := key b1 b2 hb1 hb2
  nlinarith [ka, kb]

lemma dd_concave : ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) (fun p : ℝ × ℝ => dd p.1 p.2) := by
  refine ⟨(convex_Ici 0).prod (convex_Ici 0), ?_⟩
  rintro ⟨a1, b1⟩ ⟨ha1, hb1⟩ ⟨a2, b2⟩ ⟨ha2, hb2⟩ l m hl hm hlm
  simp only [Set.mem_Ici] at ha1 hb1 ha2 hb2
  simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk]
  rw [← dd_smul l a1 b1, ← dd_smul m a2 b2]
  exact dd_super _ _ _ _ (mul_nonneg hl ha1) (mul_nonneg hl hb1) (mul_nonneg hm ha2) (mul_nonneg hm hb2)


section Jensen

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

lemma pair_jensen {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (g1 g2 : Ω → ℝ)
    (h1 : Integrable g1 P) (h2 : Integrable g2 P) (hnn : ∀ᵐ ω ∂P, 0 ≤ g1 ω ∧ 0 ≤ g2 ω)
    (hd : Integrable (fun ω => dd (g1 ω) (g2 ω)) P)
    (hd2 : Integrable (fun ω => dd (P[g1 | m] ω) (P[g2 | m] ω)) P) :
    ∫ ω, dd (g1 ω) (g2 ω) ∂P ≤ ∫ ω, dd (P[g1 | m] ω) (P[g2 | m] ω) ∂P := by
  set f : Ω → ℝ × ℝ := fun ω => (g1 ω, g2 ω) with hf
  have hfint : Integrable f P := h1.prodMk h2
  have hj := dd_concave.condExp_map_le hm
    (dd_continuous.upperSemicontinuous.upperSemicontinuousOn _) (f := f)
    (by filter_upwards [hnn] with ω h; exact ⟨h.1, h.2⟩) (isClosed_Ici.prod isClosed_Ici)
    hfint hd
  have e1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp_condExp_comm (m := m) hfint
  have e2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp_condExp_comm (m := m) hfint
  have hfst : (ContinuousLinearMap.fst ℝ ℝ ℝ) ∘ f = g1 := rfl
  have hsnd : (ContinuousLinearMap.snd ℝ ℝ ℝ) ∘ f = g2 := rfl
  rw [hfst] at e1
  rw [hsnd] at e2
  calc ∫ ω, dd (g1 ω) (g2 ω) ∂P = ∫ ω, (P[(fun ω => dd (g1 ω) (g2 ω)) | m]) ω ∂P :=
        (integral_condExp hm).symm
    _ ≤ ∫ ω, dd (P[g1 | m] ω) (P[g2 | m] ω) ∂P := by
        refine integral_mono_ae integrable_condExp hd2 ?_
        filter_upwards [hj, e1, e2] with ω hω a b
        simp only [Function.comp] at hω a b
        rw [← a, ← b]
        exact hω

end Jensen


section Gap

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- `H(X | m) · log 2` as a sum over any finset containing the range. -/
lemma condEntropy_mul_log_of_finset {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    (X : Ω → β) (T : Finset β) (hT : ∀ ω, X ω ∈ T) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hX : Measurable[mΩ] X) :
    condEntropy m P X * Real.log 2 = ∑ b ∈ T, ∫ ω, Real.negMulLog (condProb m P X b ω) ∂P := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold condEntropy
  rw [div_mul_cancel₀ _ hlog, ← integral_finsetSum]
  · congr 1
    ext ω
    apply finsum_eq_sum_of_support_subset
    intro b hb
    simp only [Function.mem_support] at hb
    simp only [Finset.mem_coe]
    by_contra h
    apply hb
    have : b ∉ Set.range X := fun ⟨ω', hω'⟩ => h (hω' ▸ hT ω')
    simp [condProb_of_not_mem_range P X m b this]
  · intro b _
    exact integrable_negMulLog_condProb P X hm hX b

variable (X Y : Ω → ℝ) (hXv : ∀ ω, X ω = 1 ∨ X ω = -1) (hYv : ∀ ω, Y ω = 1 ∨ Y ω = -1)
  (hXm : Measurable X) (hYm : Measurable Y)

/-- The pair `(X, Y)`. -/
def Wp : Ω → ℝ × ℝ := fun ω => (X ω, Y ω)

include hXv hYv hXm hYm

lemma Wp_measurable : Measurable (Wp X Y) := hXm.prodMk hYm

lemma Wp_mem (ω : Ω) : Wp X Y ω ∈ ({(1, 1), (1, -1), (-1, 1), (-1, -1)} : Finset (ℝ × ℝ)) := by
  rcases hXv ω with h | h <;> rcases hYv ω with h' | h' <;> simp [Wp, h, h']

lemma Wp_range_finite : (Set.range (Wp X Y)).Finite := by
  refine (Finset.finite_toSet {(1, 1), (1, -1), (-1, 1), (-1, -1)}).subset ?_
  rintro _ ⟨ω, rfl⟩
  exact Wp_mem X Y hXv hYv hXm hYm ω

lemma X_range_finite : (Set.range X).Finite := by
  refine (Finset.finite_toSet ({1, -1} : Finset ℝ)).subset ?_
  rintro _ ⟨ω, rfl⟩
  rcases hXv ω with h | h <;> simp [h]

/-- conditional probability of `X = x` splits along `Y`. -/
lemma condProb_X_split {m : MeasurableSpace Ω} (x : ℝ) :
    condProb m P X x =ᵐ[P] fun ω => condProb m P (Wp X Y) (x, 1) ω + condProb m P (Wp X Y) (x, -1) ω := by
  have hint : ∀ c : ℝ × ℝ, Integrable ((Wp X Y ⁻¹' {c}).indicator (fun _ => (1 : ℝ))) P := by
    intro c
    exact (integrable_const (1 : ℝ)).indicator ((Wp_measurable X Y hXv hYv hXm hYm) (measurableSet_singleton c))
  have e : (X ⁻¹' {x}).indicator (fun _ => (1 : ℝ)) =
      (Wp X Y ⁻¹' {(x, 1)}).indicator (fun _ => (1 : ℝ)) +
      (Wp X Y ⁻¹' {(x, -1)}).indicator (fun _ => (1 : ℝ)) := by
    ext ω
    simp only [Pi.add_apply, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff, Wp,
      Prod.mk.injEq]
    rcases hYv ω with h | h <;> by_cases hx : X ω = x <;> simp [h, hx] <;> norm_num
  unfold condProb
  rw [e]
  exact condExp_add (hint _) (hint _) _


lemma int_negMulLog_W {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (c : ℝ × ℝ) :
    Integrable (fun ω => Real.negMulLog (condProb m P (Wp X Y) c ω)) P :=
  integrable_negMulLog_condProb P (Wp X Y) hm (Wp_measurable X Y hXv hYv hXm hYm) c

lemma int_negMulLog_sum {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (x : ℝ) :
    Integrable (fun ω => Real.negMulLog (condProb m P (Wp X Y) (x, 1) ω +
      condProb m P (Wp X Y) (x, -1) ω)) P := by
  have := integrable_negMulLog_condProb P X hm hXm x
  refine this.congr ?_
  filter_upwards [condProb_X_split P X Y hXv hYv hXm hYm (m := m) x] with ω h
  simp [h]

lemma int_dd {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (x : ℝ) :
    Integrable (fun ω => dd (condProb m P (Wp X Y) (x, 1) ω) (condProb m P (Wp X Y) (x, -1) ω)) P :=
  ((int_negMulLog_W P X Y hXv hYv hXm hYm hm (x, 1)).add
    (int_negMulLog_W P X Y hXv hYv hXm hYm hm (x, -1))).sub
    (int_negMulLog_sum P X Y hXv hYv hXm hYm hm x)

/-- The gap `(H(W | m) - H(X | m)) log 2` as a sum of integrals of `dd`. -/
lemma gap_formula {m : MeasurableSpace Ω} (hm : m ≤ mΩ) :
    (condEntropy m P (Wp X Y) - condEntropy m P X) * Real.log 2 =
      ∑ x ∈ ({1, -1} : Finset ℝ),
        ∫ ω, dd (condProb m P (Wp X Y) (x, 1) ω) (condProb m P (Wp X Y) (x, -1) ω) ∂P := by
  rw [sub_mul, condEntropy_mul_log_of_finset P (Wp X Y) _ (Wp_mem X Y hXv hYv hXm hYm) hm
      (Wp_measurable X Y hXv hYv hXm hYm),
    condEntropy_mul_log_of_finset P X {1, -1} (by
      intro ω; rcases hXv ω with h | h <;> simp [h]) hm hXm]
  have hx : ∀ x : ℝ, ∫ ω, Real.negMulLog (condProb m P X x ω) ∂P =
      ∫ ω, Real.negMulLog (condProb m P (Wp X Y) (x, 1) ω +
        condProb m P (Wp X Y) (x, -1) ω) ∂P := by
    intro x
    refine integral_congr_ae ?_
    filter_upwards [condProb_X_split P X Y hXv hYv hXm hYm (m := m) x] with ω h
    simp [h]
  have hd : ∀ x : ℝ, ∫ ω, dd (condProb m P (Wp X Y) (x, 1) ω) (condProb m P (Wp X Y) (x, -1) ω) ∂P
      = ∫ ω, Real.negMulLog (condProb m P (Wp X Y) (x, 1) ω) ∂P
        + ∫ ω, Real.negMulLog (condProb m P (Wp X Y) (x, -1) ω) ∂P
        - ∫ ω, Real.negMulLog (condProb m P (Wp X Y) (x, 1) ω +
          condProb m P (Wp X Y) (x, -1) ω) ∂P := by
    intro x
    unfold dd
    have h1 := int_negMulLog_W P X Y hXv hYv hXm hYm hm (x, 1)
    have h2 := int_negMulLog_W P X Y hXv hYv hXm hYm hm (x, -1)
    have hA : Integrable (fun ω => Real.negMulLog (condProb m P (Wp X Y) (x, 1) ω) +
        Real.negMulLog (condProb m P (Wp X Y) (x, -1) ω)) P := h1.add h2
    rw [integral_sub hA (int_negMulLog_sum P X Y hXv hYv hXm hYm hm x), integral_add h1 h2]
  simp only [hx, hd]
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_singleton]
  simp only [Finset.sum_pair (show (1 : ℝ) ≠ -1 by norm_num)]
  ring


lemma gap_anti {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ mΩ) :
    condEntropy m₂ P (Wp X Y) - condEntropy m₂ P X ≤
      condEntropy m₁ P (Wp X Y) - condEntropy m₁ P X := by
  have h1 : m₁ ≤ mΩ := h12.trans h2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine le_of_mul_le_mul_right ?_ hlog
  rw [gap_formula P X Y hXv hYv hXm hYm h1, gap_formula P X Y hXv hYv hXm hYm h2]
  refine Finset.sum_le_sum (fun x _ => ?_)
  have hWm := Wp_measurable X Y hXv hYv hXm hYm
  have hcc : ∀ c : ℝ × ℝ, P[condProb m₂ P (Wp X Y) c | m₁] =ᵐ[P] condProb m₁ P (Wp X Y) c :=
    fun c => condExp_condExp_of_le h12 h2
  have hJ := pair_jensen P (m := m₁) h1 (condProb m₂ P (Wp X Y) (x, 1))
    (condProb m₂ P (Wp X Y) (x, -1)) integrable_condExp integrable_condExp
    (by filter_upwards [condProb_nonneg_le P (Wp X Y) h2 hWm (x, 1),
          condProb_nonneg_le P (Wp X Y) h2 hWm (x, -1)] with ω a b
        exact ⟨a.1, b.1⟩)
    (int_dd P X Y hXv hYv hXm hYm h2 x)
    (by refine (int_dd P X Y hXv hYv hXm hYm h1 x).congr ?_
        filter_upwards [hcc (x, 1), hcc (x, -1)] with ω a b
        simp [a, b])
  refine hJ.trans (le_of_eq (integral_congr_ae ?_))
  filter_upwards [hcc (x, 1), hcc (x, -1)] with ω a b
  simp [a, b]


lemma condProb_swap (m : MeasurableSpace Ω) (c : ℝ × ℝ) :
    condProb m P (Wp Y X) c = condProb m P (Wp X Y) c.swap := by
  unfold condProb
  have : Wp Y X ⁻¹' {c} = Wp X Y ⁻¹' {c.swap} := by
    ext ω; simp [Wp, Prod.ext_iff, and_comm]
  rw [this]

lemma condEntropy_swap (m : MeasurableSpace Ω) :
    condEntropy m P (Wp Y X) = condEntropy m P (Wp X Y) := by
  unfold condEntropy
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  simp only [condProb_swap P X Y hXv hYv hXm hYm m]
  exact finsum_comp_equiv (Equiv.prodComm ℝ ℝ) (f := fun c => Real.negMulLog (condProb m P (Wp X Y) c ω))

end Gap


section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  {k : ℕ} {α : Fin k → Type*} [∀ l, MeasurableSpace (α l)]
  (Z : ∀ l, Ω → α l) (hZ : ∀ l, Measurable (Z l))
  (X Y : Ω → ℝ) (hXv : ∀ ω, X ω = 1 ∨ X ω = -1) (hYv : ∀ ω, Y ω = 1 ∨ Y ω = -1)
  (hXm : Measurable X) (hYm : Measurable Y)
  (hXf : Measurable[sourceSigma Z Finset.univ] X) (hYf : Measurable[sourceSigma Z Finset.univ] Y)

lemma infoMeasure_eq {β : Type*} (A : Ω → β) (j : Fin k) :
    infoMeasure P Z A j = condEntropy (prefixSigma Z j) P A -
      condEntropy (prefixSigma Z ((j : ℕ) + 1)) P A := by
  unfold infoMeasure infoCDF mutualInfo
  ring

include hZ hXv hYv hXm hYm in
lemma df_gap_nonneg (j : Fin k) :
    0 ≤ infoMeasure P Z (Wp X Y) j - infoMeasure P Z X j := by
  have := gap_anti P X Y hXv hYv hXm hYm (prefixSigma_mono Z (Nat.le_succ (j : ℕ)))
    (sourceSigma_le Z hZ _)
  rw [infoMeasure_eq, infoMeasure_eq]
  linarith

include hZ hXv hYv hXm hYm hXf hYf in
lemma df_gap_sum :
    ∑ j : Fin k, (infoMeasure P Z (Wp X Y) j - infoMeasure P Z X j) =
      entropy P (Wp X Y) - entropy P X := by
  set g : ℕ → ℝ := fun j => condEntropy (prefixSigma Z j) P (Wp X Y) -
    condEntropy (prefixSigma Z j) P X with hg
  have h1 : ∀ j : Fin k, infoMeasure P Z (Wp X Y) j - infoMeasure P Z X j =
      g (j : ℕ) - g ((j : ℕ) + 1) := by
    intro j; rw [infoMeasure_eq, infoMeasure_eq]; simp only [hg]; ring
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => g i - g (i + 1)) k, Finset.sum_range_sub']
  have hW : Measurable[sourceSigma Z Finset.univ] (Wp X Y) := hXf.prodMk hYf
  have e0 : g 0 = entropy P (Wp X Y) - entropy P X := by
    simp only [hg, prefixSigma_zero]
    rw [condEntropy_bot P _ (Wp_measurable X Y hXv hYv hXm hYm), condEntropy_bot P X hXm]
  have ek : g k = 0 := by
    simp only [hg, prefixSigma_k]
    rw [condEntropy_of_measurable P _ (Wp_range_finite X Y hXv hYv hXm hYm) (sourceSigma_le Z hZ _) hW,
      condEntropy_of_measurable P X (X_range_finite X Y hXv hYv hXm hYm) (sourceSigma_le Z hZ _) hXf]
    ring
  rw [e0, ek]; ring

include hXv hYv hXm hYm in
lemma infoMeasure_swap (j : Fin k) :
    infoMeasure P Z (Wp Y X) j = infoMeasure P Z (Wp X Y) j := by
  rw [infoMeasure_eq, infoMeasure_eq, condEntropy_swap P X Y hXv hYv hXm hYm,
    condEntropy_swap P X Y hXv hYv hXm hYm]


end Main

section Entropy

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
  (X Y : Ω → ℝ) (hXv : ∀ ω, X ω = 1 ∨ X ω = -1) (hYv : ∀ ω, Y ω = 1 ∨ Y ω = -1)
  (hXm : Measurable X) (hYm : Measurable Y)

lemma real_union_eq (S A B : Set Ω) (hS : S = A ∪ B) (hd : Disjoint A B) (hB : MeasurableSet B) :
    P.real S = P.real A + P.real B := by
  rw [hS]; exact measureReal_union hd hB

include hXv hYv hXm hYm in
lemma entropy_gap (hX : P.real {ω | X ω = 1} = 1 / 2) (hY : P.real {ω | Y ω = 1} = 1 / 2) :
    entropy P (Wp X Y) - entropy P X = h (P.real {ω | X ω ≠ Y ω}) := by
  have hWm := Wp_measurable X Y hXv hYv hXm hYm
  have mW : ∀ c : ℝ × ℝ, MeasurableSet (Wp X Y ⁻¹' {c}) := fun c => hWm (measurableSet_singleton c)
  set u := P.real (Wp X Y ⁻¹' {((1 : ℝ), (1 : ℝ))}) with hu
  set v := P.real (Wp X Y ⁻¹' {((1 : ℝ), (-1 : ℝ))}) with hv
  set s := P.real (Wp X Y ⁻¹' {((-1 : ℝ), (1 : ℝ))}) with hs
  set t := P.real (Wp X Y ⁻¹' {((-1 : ℝ), (-1 : ℝ))}) with ht
  have hX1 : MeasurableSet {ω | X ω = 1} := hXm (measurableSet_singleton 1)
  have E1 : P.real {ω | X ω = 1} = u + v := by
    refine real_union_eq P _ _ _ ?_ ?_ (mW _)
    · ext ω; rcases hYv ω with h | h <;> simp [Wp, h] <;> intros <;> first | assumption | (exfalso; norm_num at *)
    · rw [Set.disjoint_left]; intro ω a b; simp [Wp] at a b; rw [a.2] at b; norm_num at b
  have E2 : P.real {ω | Y ω = 1} = u + s := by
    refine real_union_eq P _ _ _ ?_ ?_ (mW _)
    · ext ω; rcases hXv ω with h | h <;> simp [Wp, h]
    · rw [Set.disjoint_left]; intro ω a b; simp [Wp] at a b; rw [a.1] at b; norm_num at b
  have E3 : P.real {ω | X ω ≠ Y ω} = v + s := by
    refine real_union_eq P _ _ _ ?_ ?_ (mW _)
    · ext ω; rcases hXv ω with h | h <;> rcases hYv ω with h' | h' <;> simp [Wp, h, h'] <;> norm_num
    · rw [Set.disjoint_left]; intro ω a b; simp [Wp] at a b; rw [a.1] at b; norm_num at b
  have E4 : P.real {ω | X ω = -1} = s + t := by
    refine real_union_eq P _ _ _ ?_ ?_ (mW _)
    · ext ω; rcases hYv ω with h | h <;> simp [Wp, h] <;> intros <;> first | assumption | (exfalso; norm_num at *)
    · rw [Set.disjoint_left]; intro ω a b; simp [Wp] at a b; rw [a.2] at b; norm_num at b
  have E5 : P.real {ω | X ω = -1} = 1 / 2 := by
    have : {ω | X ω = -1} = {ω | X ω = 1}ᶜ := by
      ext ω; rcases hXv ω with h | h <;> simp [h] <;> norm_num
    rw [this, probReal_compl_eq_one_sub hX1, hX]; norm_num
  have hvs : v = s := by linarith
  have htu : t = u := by linarith
  have huv : u + v = 1 / 2 := by linarith
  have hp : P.real {ω | X ω ≠ Y ω} = 2 * v := by rw [E3]; linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN2 : Real.negMulLog 2 = -2 * Real.log 2 := by simp [Real.negMulLog]
  have hNh : Real.negMulLog (1 / 2) = (1 / 2) * Real.log 2 := by
    simp [Real.negMulLog, Real.log_inv]
  -- entropy of W
  have eW : entropy P (Wp X Y) = (Real.negMulLog u + Real.negMulLog v + Real.negMulLog s
      + Real.negMulLog t) / Real.log 2 := by
    unfold entropy
    congr 1
    rw [finsum_eq_sum_of_support_subset (s := {(1, 1), (1, -1), (-1, 1), (-1, -1)})]
    · rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
        Finset.sum_insert (by norm_num), Finset.sum_singleton]
      ring
    · intro c hc
      simp only [Function.mem_support] at hc
      by_contra hcn
      apply hc
      have : Wp X Y ⁻¹' {c} = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hcn (h ▸ Wp_mem X Y hXv hYv hXm hYm ω)
      rw [this]; simp
  have eX : entropy P X = (Real.negMulLog (1 / 2) + Real.negMulLog (1 / 2)) / Real.log 2 := by
    unfold entropy
    congr 1
    have hX' : P.real (X ⁻¹' {1}) = 1 / 2 := hX
    have hX'' : P.real (X ⁻¹' {-1}) = 1 / 2 := E5
    rw [finsum_eq_sum_of_support_subset (s := ({1, -1} : Finset ℝ))]
    · rw [Finset.sum_pair (by norm_num)]
      change Real.negMulLog (P.real (X ⁻¹' {1})) + Real.negMulLog (P.real (X ⁻¹' {-1})) = _
      rw [hX', hX'']
    · intro c hc
      simp only [Function.mem_support] at hc
      by_contra hcn
      apply hc
      have : X ⁻¹' {c} = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro h
        apply hcn
        rcases hXv ω with h' | h' <;> simp [← h, h']
      rw [this]; simp
  rw [eW, eX, hp]
  unfold h
  rw [← sub_div]
  congr 1
  have h2u : 1 - 2 * v = 2 * u := by linarith
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, h2u, Real.negMulLog_mul,
    Real.negMulLog_mul, hN2, hNh, hvs, htu]
  have : u * Real.log 2 + s * Real.log 2 = 1 / 2 * Real.log 2 := by
    rw [← add_mul, ← hvs, huv]
  linarith

end Entropy

end EntropyLocalCoord.Dev.Lem41

open MeasureTheory EntropyLocalCoord.Leader in
theorem EntropyLocalCoord.Leader.chk_lemma_4_1 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {α : Fin k → Type*}
    [∀ l, MeasurableSpace (α l)] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ∀ l, Ω → α l) (hZ : ∀ l, Measurable (Z l)) (X Y : Ω → ℝ)
    (hXm : Measurable[sourceSigma Z Finset.univ] X)
    (hYm : Measurable[sourceSigma Z Finset.univ] Y)
    (hX : IsUnbiasedSign P X) (hY : IsUnbiasedSign P Y) :
    tvNorm (fun j => infoMeasure P Z X j - infoMeasure P Z Y j) ≤
      h (P.real {ω | X ω ≠ Y ω}) := by
  open EntropyLocalCoord.Dev.Lem41 EntropyLocalCoord.Dev.CDF in
  have hXm' : Measurable X := hXm.mono (sourceSigma_le Z hZ _) le_rfl
  have hYm' : Measurable Y := hYm.mono (sourceSigma_le Z hZ _) le_rfl
  have hs1 := df_gap_sum P Z hZ X Y hX.1 hY.1 hXm' hYm' hXm hYm
  have hs2 := df_gap_sum P Z hZ Y X hY.1 hX.1 hYm' hXm' hYm hXm
  rw [entropy_gap P X Y hX.1 hY.1 hXm' hYm' hX.2 hY.2] at hs1
  rw [entropy_gap P Y X hY.1 hX.1 hYm' hXm' hY.2 hX.2] at hs2
  have hne : {ω | Y ω ≠ X ω} = {ω | X ω ≠ Y ω} := by ext ω; simp [ne_comm]
  rw [hne] at hs2
  have hn1 := df_gap_nonneg P Z hZ X Y hX.1 hY.1 hXm' hYm'
  have hn2 := df_gap_nonneg P Z hZ Y X hY.1 hX.1 hYm' hXm'
  have hsw := infoMeasure_swap P Z X Y hX.1 hY.1 hXm' hYm'
  unfold tvNorm
  have hb : ∀ j : Fin k, |infoMeasure P Z X j - infoMeasure P Z Y j| ≤
      (infoMeasure P Z (Wp X Y) j - infoMeasure P Z X j) +
      (infoMeasure P Z (Wp Y X) j - infoMeasure P Z Y j) := by
    intro j
    have a1 := hn1 j
    have a2 := hn2 j
    have a3 := hsw j
    rw [abs_le]
    constructor <;> linarith
  calc 1 / 2 * ∑ j, |infoMeasure P Z X j - infoMeasure P Z Y j|
      ≤ 1 / 2 * ∑ j, ((infoMeasure P Z (Wp X Y) j - infoMeasure P Z X j) +
          (infoMeasure P Z (Wp Y X) j - infoMeasure P Z Y j)) := by
        gcongr with j _
        exact hb j
    _ = h (P.real {ω | X ω ≠ Y ω}) := by
        rw [Finset.sum_add_distrib, hs1, hs2]; ring
end

theorem solution : type_of% @EntropyLocalCoord.Leader.chk_lemma_4_1 := @EntropyLocalCoord.Leader.chk_lemma_4_1
