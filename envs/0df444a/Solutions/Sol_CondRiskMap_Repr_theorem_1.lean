-- Prove2me | solution 1 for CondRiskMap.Repr.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:42:48.399844+00:00
-- url     : https://prove2.me/submissions/a71cd90a-93c5-4dec-befe-9e857d00b44f

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting
import Theorems.Thm_CondRiskMap_Repr_dom_conj_subset_probGiven

open CondRiskMap.Repr MeasureTheory

namespace CRMThm1Aux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma pair_smul (μ : SignedMeasure Ω) (c : ℝ) (f : Ω → ℝ) :
    pair μ (c • f) = c * pair μ f := by
  unfold pair
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]
  ring

lemma pair_zero (μ : SignedMeasure Ω) : pair μ 0 = 0 := by
  unfold pair; simp

lemma int_pos {μ : SignedMeasure Ω} {f : Ω → ℝ} (h : Integrable f μ.totalVariation) :
    Integrable f μ.toJordanDecomposition.posPart := by
  unfold SignedMeasure.totalVariation at h; exact (integrable_add_measure.mp h).1

lemma int_neg {μ : SignedMeasure Ω} {f : Ω → ℝ} (h : Integrable f μ.totalVariation) :
    Integrable f μ.toJordanDecomposition.negPart := by
  unfold SignedMeasure.totalVariation at h; exact (integrable_add_measure.mp h).2

lemma pair_eq_of_decomp (s : SignedMeasure Ω) (P N : Measure Ω) [IsFiniteMeasure P]
    [IsFiniteMeasure N] (h : s = P.toSignedMeasure - N.toSignedMeasure) (f : Ω → ℝ)
    (hP : Integrable f P) (hN : Integrable f N) (hs : Integrable f s.totalVariation) :
    pair s f = ∫ x, f x ∂P - ∫ x, f x ∂N := by
  set j := s.toJordanDecomposition
  have hj : s = j.posPart.toSignedMeasure - j.negPart.toSignedMeasure :=
    (SignedMeasure.toSignedMeasure_toJordanDecomposition s).symm
  have heq : j.posPart + N = P + j.negPart := by
    rw [← Measure.toSignedMeasure_eq_toSignedMeasure_iff, Measure.toSignedMeasure_add,
      Measure.toSignedMeasure_add]
    have := hj.symm.trans h
    rw [sub_eq_sub_iff_add_eq_add] at this
    exact this
  have hi := congrArg (fun m : Measure Ω => ∫ x, f x ∂m) heq
  rw [integral_add_measure (int_pos hs) hN, integral_add_measure hP (int_neg hs)] at hi
  unfold pair
  linarith

lemma pair_comb (μ ν : SignedMeasure Ω) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (f : Ω → ℝ)
    (hμ : Integrable f μ.totalVariation) (hν : Integrable f ν.totalVariation)
    (hs : Integrable f (a • μ + b • ν).totalVariation) :
    pair (a • μ + b • ν) f = a * pair μ f + b * pair ν f := by
  set jμ := μ.toJordanDecomposition
  set jν := ν.toJordanDecomposition
  have hdec : a • μ + b • ν =
      (a.toNNReal • jμ.posPart + b.toNNReal • jν.posPart).toSignedMeasure -
      (a.toNNReal • jμ.negPart + b.toNNReal • jν.negPart).toSignedMeasure := by
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add, Measure.toSignedMeasure_smul,
      Measure.toSignedMeasure_smul, Measure.toSignedMeasure_smul, Measure.toSignedMeasure_smul]
    conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition μ,
      ← SignedMeasure.toSignedMeasure_toJordanDecomposition ν]
    simp only [JordanDecomposition.toSignedMeasure]
    have e1 : (a.toNNReal : ℝ) = a := Real.coe_toNNReal a ha
    have e2 : (b.toNNReal : ℝ) = b := Real.coe_toNNReal b hb
    rw [show a • (jμ.posPart.toSignedMeasure - jμ.negPart.toSignedMeasure) =
        a.toNNReal • jμ.posPart.toSignedMeasure - a.toNNReal • jμ.negPart.toSignedMeasure by
          rw [smul_sub, NNReal.smul_def, NNReal.smul_def, e1],
      show b • (jν.posPart.toSignedMeasure - jν.negPart.toSignedMeasure) =
        b.toNNReal • jν.posPart.toSignedMeasure - b.toNNReal • jν.negPart.toSignedMeasure by
          rw [smul_sub, NNReal.smul_def, NNReal.smul_def, e2]]
    abel
  rw [pair_eq_of_decomp _ _ _ hdec f
    (((int_pos hμ).smul_measure_nnreal).add_measure ((int_pos hν).smul_measure_nnreal))
    (((int_neg hμ).smul_measure_nnreal).add_measure ((int_neg hν).smul_measure_nnreal)) hs]
  rw [integral_add_measure ((int_pos hμ).smul_measure_nnreal) ((int_pos hν).smul_measure_nnreal),
    integral_add_measure ((int_neg hμ).smul_measure_nnreal) ((int_neg hν).smul_measure_nnreal),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal a ha, Real.coe_toNNReal b hb]
  unfold pair
  ring


lemma pair_add (μ : SignedMeasure Ω) {f g : Ω → ℝ} (hf : Integrable f μ.totalVariation)
    (hg : Integrable g μ.totalVariation) : pair μ (f + g) = pair μ f + pair μ g := by
  unfold pair
  simp only [Pi.add_apply]
  rw [integral_add (int_pos hf) (int_pos hg), integral_add (int_neg hf) (int_neg hg)]
  ring

noncomputable def mOf (s : SignedMeasure Ω) (hs : 0 ≤ s) : Measure Ω :=
  s.toMeasureOfZeroLE Set.univ MeasurableSet.univ ((VectorMeasure.le_restrict_univ_iff_le _ _).2 hs)

instance (s : SignedMeasure Ω) (hs : 0 ≤ s) : IsFiniteMeasure (mOf s hs) := by
  unfold mOf; infer_instance

lemma mOf_toSM (s : SignedMeasure Ω) (hs : 0 ≤ s) : (mOf s hs).toSignedMeasure = s :=
  SignedMeasure.toMeasureOfZeroLE_toSignedMeasure _ _

lemma jd_nonneg (s : SignedMeasure Ω) (hs : 0 ≤ s) :
    s.toJordanDecomposition.posPart = mOf s hs ∧ s.toJordanDecomposition.negPart = 0 := by
  let j : JordanDecomposition Ω :=
    { posPart := mOf s hs, negPart := 0, mutuallySingular := Measure.MutuallySingular.zero_right }
  have hj : s.toJordanDecomposition = j := SignedMeasure.toJordanDecomposition_eq (by
    rw [JordanDecomposition.toSignedMeasure]
    show s = (mOf s hs).toSignedMeasure - (0 : Measure Ω).toSignedMeasure
    rw [Measure.toSignedMeasure_zero, sub_zero, mOf_toSM])
  rw [hj]; exact ⟨rfl, rfl⟩

lemma pair_of_nonneg (s : SignedMeasure Ω) (hs : 0 ≤ s) (f : Ω → ℝ) :
    pair s f = ∫ x, f x ∂(mOf s hs) := by
  unfold pair
  rw [(jd_nonneg s hs).1, (jd_nonneg s hs).2, integral_zero_measure, sub_zero]

lemma int_mOf (s : SignedMeasure Ω) (hs : 0 ≤ s) {h : Ω → ℝ}
    (hh : Integrable h s.totalVariation) : Integrable h (mOf s hs) := by
  have := int_pos hh
  rwa [(jd_nonneg s hs).1] at this

lemma pair_mono (s : SignedMeasure Ω) (hs : 0 ≤ s) {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x)
    (hf : Integrable f s.totalVariation) (hg : Integrable g s.totalVariation) :
    pair s f ≤ pair s g := by
  rw [pair_of_nonneg s hs, pair_of_nonneg s hs]
  exact integral_mono (int_mOf s hs hf) (int_mOf s hs hg) hfg

/-! EReal helpers -/

lemma ereal_sub_le {a r : ℝ} {c : EReal} (h : ((a - r : ℝ) : EReal) ≤ c) :
    (a : EReal) - c ≤ r := by
  induction c using EReal.rec with
  | bot => exact absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)
  | top => simp
  | coe c =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [EReal.coe_le_coe_iff] at h; linarith

lemma ereal_conv {a b r s t : ℝ} {c : EReal} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : (a : EReal) - c ≤ r) (hb : (b : EReal) - c ≤ s) :
    ((t * a + (1 - t) * b : ℝ) : EReal) - c ≤ ((t * r + (1 - t) * s : ℝ) : EReal) := by
  induction c using EReal.rec with
  | bot => exact absurd ha (by simp)
  | top => simp
  | coe c =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at ha hb ⊢
    nlinarith

lemma ereal_mono {a b : ℝ} (c : EReal) (h : a ≤ b) : (a : EReal) - c ≤ (b : EReal) - c := by
  induction c using EReal.rec with
  | bot => simp
  | top => simp
  | coe c =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]; linarith

lemma ereal_shift (a y : ℝ) (c : EReal) :
    ((a + y : ℝ) : EReal) - c = ((a : EReal) - c) + y := by
  induction c using EReal.rec with
  | bot => simp
  | top => simp
  | coe c =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]; congr 1; ring

lemma ereal_lsc {α : Type*} [TopologicalSpace α] {g : α → ℝ} (hg : Continuous g) (c : EReal) :
    LowerSemicontinuous fun x => (g x : EReal) - c := by
  induction c using EReal.rec with
  | bot =>
    have : (fun x => (g x : EReal) - ⊥) = fun _ => ⊤ := by funext x; simp
    rw [this]; exact lowerSemicontinuous_const
  | top =>
    have : (fun x => (g x : EReal) - ⊤) = fun _ => ⊥ := by funext x; simp
    rw [this]; exact lowerSemicontinuous_const
  | coe c =>
    simp only [← EReal.coe_sub]
    exact (continuous_coe_real_ereal.comp (hg.sub continuous_const)).lowerSemicontinuous

lemma ereal_sub_anti {x d : ℝ} {c : EReal} (h : c ≤ d) : (x : EReal) - d ≤ (x : EReal) - c := by
  induction c using EReal.rec with
  | bot => simp
  | top => exact absurd h (by simp)
  | coe c =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [EReal.coe_le_coe_iff] at h; linarith

end CRMThm1Aux

open CRMThm1Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S) :
    (∀ ρ : 𝒳 → 𝒳, IsCondRiskMapping S ρ → IsLsc S ρ →
      ∀ ω X, ((ρω S ρ ω X : ℝ) : EReal) =
        ⨆ μ ∈ ProbGiven S ω, ((pair (S.toMeasure μ) (S.toFun X) : ℝ) : EReal) - conj S ρ μ ω) ∧
    (∀ ρ : 𝒳 → 𝒳, MapsToX₁ S ρ → ∀ ρs : 𝒴 → Ω → EReal,
      (∀ ω X, ((ρω S ρ ω X : ℝ) : EReal) =
        ⨆ μ ∈ ProbGiven S ω, ((pair (S.toMeasure μ) (S.toFun X) : ℝ) : EReal) - ρs μ ω) →
      IsLsc S ρ ∧ A1 S ρ ∧ A2 S ρ ∧ A3 S ρ) := by
  refine ⟨?_, ?_⟩
  · intro ρ hρ hlsc ω X
    have hA1 := hρ.2.1
    apply le_antisymm
    · by_contra hlt
      push_neg at hlt
      obtain ⟨b, hb1, hb2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      have hbr : b < ρω S ρ ω X := EReal.coe_lt_coe_iff.mp hb2
      let epi : Set (𝒳 × ℝ) := {p | ρω S ρ ω p.1 ≤ p.2}
      have hclosed : IsClosed epi := (hlsc ω).isClosed_epigraph
      have hconv : Convex ℝ epi := by
        intro p hp q hq a c ha hc hac
        obtain rfl : c = 1 - a := by linarith
        show ρω S ρ ω (a • p.1 + (1 - a) • q.1) ≤ a * p.2 + (1 - a) * q.2
        have := hA1 a ha (by linarith) p.1 q.1 ω
        have h1 := mul_le_mul_of_nonneg_left (show ρω S ρ ω p.1 ≤ p.2 from hp) ha
        have h2 := mul_le_mul_of_nonneg_left (show ρω S ρ ω q.1 ≤ q.2 from hq) hc
        linarith
      have hnot : (X, b) ∉ epi := fun h => absurd (show ρω S ρ ω X ≤ b from h) (not_le.mpr hbr)
      obtain ⟨f, u, hfu, hf⟩ := geometric_hahn_banach_point_closed hconv hclosed hnot
      let ℓ : 𝒳 →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ 𝒳 ℝ)
      set a := f ((0 : 𝒳), (1 : ℝ)) with ha_def
      have hfa : ∀ (Y : 𝒳) (r : ℝ), f (Y, r) = ℓ Y + r * a := by
        intro Y r
        have : ((Y, r) : 𝒳 × ℝ) = (Y, 0) + r • ((0 : 𝒳), (1 : ℝ)) := by
          ext <;> simp
        rw [this, map_add, map_smul, smul_eq_mul]
        rfl
      have hmem : ∀ Y : 𝒳, (Y, ρω S ρ ω Y) ∈ epi := fun Y =>
        show ρω S ρ ω Y ≤ ρω S ρ ω Y from le_refl _
      have hall : ∀ Y, u < ℓ Y + ρω S ρ ω Y * a := fun Y => by
        have := hf _ (hmem Y); rwa [hfa] at this
      rw [hfa] at hfu
      have hapos : 0 < a := by
        by_contra hna
        push_neg at hna
        have := hall X
        nlinarith
      obtain ⟨μ, hμ⟩ := S.dual_rep_X ((-(1 / a)) • ℓ)
      have hμval : ∀ Y, pair (S.toMeasure μ) (S.toFun Y) = (-ℓ Y) / a := by
        intro Y
        rw [← hμ Y, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      have hconj : conj S ρ μ ω ≤ ((-u / a : ℝ) : EReal) := by
        refine iSup_le fun Y => ?_
        rw [EReal.coe_le_coe_iff, hμval]
        have := hall Y
        rw [div_sub' (ne_of_gt hapos), div_le_div_iff_of_pos_right hapos]
        linarith
      have henv : μ ∈ envelope S ρ ω :=
        lt_of_le_of_lt hconj (EReal.coe_lt_top _)
      have hPG := dom_conj_subset_probGiven S hC hC' ρ hρ hlsc ω henv
      have hterm : ((b : ℝ) : EReal) <
          ((pair (S.toMeasure μ) (S.toFun X) : ℝ) : EReal) - conj S ρ μ ω := by
        refine lt_of_lt_of_le ?_ (ereal_sub_anti hconj)
        rw [← EReal.coe_sub, EReal.coe_lt_coe_iff, hμval]
        rw [show -ℓ X / a - -u / a = (-ℓ X + u) / a by ring, lt_div_iff₀ hapos]
        linarith
      have := le_iSup₂_of_le (f := fun μ (_ : μ ∈ ProbGiven S ω) =>
        ((pair (S.toMeasure μ) (S.toFun X) : ℝ) : EReal) - conj S ρ μ ω) μ hPG le_rfl
      exact absurd (lt_of_lt_of_le hterm this) (not_lt.mpr hb1.le)
    · refine iSup₂_le fun μ _ => ereal_sub_le ?_
      exact le_iSup (fun Y : 𝒳 =>
        (((pair (S.toMeasure μ) (S.toFun Y) - ρω S ρ ω Y : ℝ)) : EReal)) X
  · intro ρ hmaps ρs hrep
    have hT : ∀ ω X μ, μ ∈ ProbGiven S ω →
        ((pair (S.toMeasure μ) (S.toFun X) : ℝ) : EReal) - ρs μ ω ≤ ((ρω S ρ ω X : ℝ) : EReal) := by
      intro ω X μ hμ
      rw [hrep]
      exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ ProbGiven S ω) =>
        ((pair (S.toMeasure μ) (S.toFun X) : ℝ) : EReal) - ρs μ ω) μ hμ le_rfl
    -- pairing against an `ℱ₁`-measurable element
    have hpY : ∀ ω, ∀ μ ∈ ProbGiven S ω, ∀ Y ∈ S.X₁,
        pair (S.toMeasure μ) (S.toFun Y) = S.toFun Y ω := by
      intro ω μ hμ Y hY
      have hnn : 0 ≤ S.toMeasure μ := hμ.1.1
      set m := mOf (S.toMeasure μ) hnn
      have hm : ∀ A, MeasurableSet A → m.real A = S.toMeasure μ A := by
        intro A hA
        rw [← Measure.toSignedMeasure_apply_measurable hA, mOf_toSM]
      let B := S.toFun Y ⁻¹' {S.toFun Y ω}
      have hB : MeasurableSet[S.F₁] B := S.X₁_measurable Y hY (measurableSet_singleton _)
      have hB2 : MeasurableSet B := S.F₁_le _ hB
      have hBc : m Bᶜ = 0 := by
        have h1 := hm Bᶜ hB2.compl
        rw [hμ.2 Bᶜ hB.compl, Set.indicator_of_notMem (by simp [B])] at h1
        exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h1
      have huniv : m.real Set.univ = 1 := by rw [hm _ MeasurableSet.univ]; exact hμ.1.2
      rw [pair_of_nonneg _ hnn]
      have hae : (fun x => S.toFun Y x) =ᵐ[m] fun _ => S.toFun Y ω := by
        rw [Filter.EventuallyEq, ae_iff]
        refine measure_mono_null (fun x hx => ?_) hBc
        simpa [B] using hx
      rw [integral_congr_ae hae, integral_const, huniv, one_smul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ω
      have hF : LowerSemicontinuous fun X => ⨆ μ ∈ ProbGiven S ω,
          ((pair (S.toMeasure μ) (S.toFun X) : ℝ) : EReal) - ρs μ ω :=
        lowerSemicontinuous_biSup fun μ _ => ereal_lsc (S.continuous_pair_X μ) _
      intro X y hy
      have := hF X (y : EReal) (by
        have h0 := EReal.coe_lt_coe_iff.mpr hy; rw [hrep] at h0; exact h0)
      filter_upwards [this] with X' hX'
      rw [← hrep] at hX'
      exact EReal.coe_lt_coe_iff.mp hX'
    · intro t ht0 ht1 X Y ω
      rw [← EReal.coe_le_coe_iff, hrep]
      refine iSup₂_le fun μ hμ => ?_
      rw [map_add, pair_add _ (S.integrable μ _) (S.integrable μ _), map_smul, map_smul,
        pair_smul, pair_smul]
      exact ereal_conv ht0 ht1 (hT ω X μ hμ) (hT ω Y μ hμ)
    · intro X Y hXY ω
      rw [← EReal.coe_le_coe_iff, hrep, hrep]
      refine iSup₂_le fun μ hμ => le_iSup₂_of_le (f := fun μ (_ : μ ∈ ProbGiven S ω) =>
        ((pair (S.toMeasure μ) (S.toFun Y) : ℝ) : EReal) - ρs μ ω) μ hμ ?_
      exact ereal_mono _ (pair_mono _ hμ.1.1 hXY (S.integrable μ X) (S.integrable μ Y))
    · have hle : ∀ ω X, ∀ Y ∈ S.X₁, ρω S ρ ω (X + Y) ≤ ρω S ρ ω X + S.toFun Y ω := by
        intro ω X Y hY
        rw [← EReal.coe_le_coe_iff, EReal.coe_add, hrep]
        refine iSup₂_le fun μ hμ => ?_
        rw [map_add, pair_add _ (S.integrable μ _) (S.integrable μ _), hpY ω μ hμ Y hY,
          ereal_shift]
        exact add_le_add_left (hT ω X μ hμ) _
      intro Y hY X
      apply S.toFun_injective
      funext ω
      rw [map_add, Pi.add_apply]
      show ρω S ρ ω (X + Y) = ρω S ρ ω X + S.toFun Y ω
      apply le_antisymm (hle ω X Y hY)
      have := hle ω (X + Y) (-Y) (S.X₁.neg_mem hY)
      rw [add_neg_cancel_right, map_neg, Pi.neg_apply] at this
      linarith
