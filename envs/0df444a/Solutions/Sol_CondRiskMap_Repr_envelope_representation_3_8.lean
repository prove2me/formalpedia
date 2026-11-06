-- Prove2me | solution 1 for CondRiskMap.Repr.envelope_representation_3_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:36:45.997958+00:00
-- url     : https://prove2.me/submissions/30d66400-c1fc-4cb2-b04e-520f63b78eb2

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting
import Theorems.Thm_CondRiskMap_Repr_dom_conj_subset_probGiven

open CondRiskMap.Repr MeasureTheory

namespace CRMEnvAux

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

end CRMEnvAux

open CRMEnvAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ) :
    ∀ ω, (∀ μ ∈ envelope S ρ ω, conj S ρ μ ω = 0) ∧ (∀ μ ∉ envelope S ρ ω, conj S ρ μ ω = ⊤) ∧
      IsClosed (envelope S ρ ω) ∧ Convex ℝ (envelope S ρ ω) ∧
      envelope S ρ ω ⊆ ProbGiven S ω ∧
      ∀ X, IsLUB ((fun μ => pair (S.toMeasure μ) (S.toFun X)) '' envelope S ρ ω) (ρω S ρ ω X) := by
  intro ω
  have hA1 := hρ.2.1
  have hρt : ∀ t : ℝ, 0 < t → ∀ X, ρω S ρ ω (t • X) = t * ρω S ρ ω X := by
    intro t ht X
    unfold ρω
    rw [hph t X ht, map_smul]
    rfl
  have hρ0 : ρω S ρ ω 0 = 0 := by
    have h2 := hρt 2 (by norm_num) 0
    rw [smul_zero] at h2
    linarith
  have hpairt : ∀ μ (t : ℝ) X, pair (S.toMeasure μ) (S.toFun (t • X)) =
      t * pair (S.toMeasure μ) (S.toFun X) := by
    intro μ t X; rw [map_smul, pair_smul]
  have hφ0 : ∀ μ, pair (S.toMeasure μ) (S.toFun 0) - ρω S ρ ω 0 = 0 := by
    intro μ; rw [map_zero, pair_zero, hρ0, sub_zero]
  -- characterization of the envelope
  have hchar : ∀ μ, μ ∈ envelope S ρ ω ↔
      ∀ X, pair (S.toMeasure μ) (S.toFun X) ≤ ρω S ρ ω X := by
    intro μ
    constructor
    · intro hμ X
      have hle : ∀ X, ((pair (S.toMeasure μ) (S.toFun X) - ρω S ρ ω X : ℝ) : EReal) ≤
          conj S ρ μ ω := fun X =>
        le_iSup (fun X : 𝒳 => (((pair (S.toMeasure μ) (S.toFun X) - ρω S ρ ω X : ℝ)) : EReal)) X
      have htop : conj S ρ μ ω ≠ ⊤ := ne_of_lt hμ
      have hbot : conj S ρ μ ω ≠ ⊥ := by
        intro h; have := hle 0; rw [h] at this; exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
      set M := (conj S ρ μ ω).toReal
      have hM : ∀ X, pair (S.toMeasure μ) (S.toFun X) - ρω S ρ ω X ≤ M := by
        intro X
        have := hle X
        rw [← EReal.coe_toReal htop hbot] at this
        exact EReal.coe_le_coe_iff.mp this
      by_contra hcon
      push_neg at hcon
      set d := pair (S.toMeasure μ) (S.toFun X) - ρω S ρ ω X
      have hd : 0 < d := by simp only [d]; linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (M / d)
      have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (by
        have := hM 0; rw [hφ0] at this; exact this) hd.le) hn
      have h1 := hM ((n : ℝ) • X)
      rw [hpairt, hρt _ hnpos] at h1
      rw [div_lt_iff₀ hd] at hn
      have : (n : ℝ) * pair (S.toMeasure μ) (S.toFun X) - n * ρω S ρ ω X = n * d := by
        simp only [d]; ring
      linarith
    · intro h
      show conj S ρ μ ω < ⊤
      refine lt_of_le_of_lt (iSup_le fun X => ?_) EReal.zero_lt_top
      exact EReal.coe_nonpos.mpr (sub_nonpos.mpr (h X))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ hμ
    apply le_antisymm
    · refine iSup_le fun X => ?_
      exact EReal.coe_nonpos.mpr (sub_nonpos.mpr ((hchar μ).mp hμ X))
    · refine le_trans ?_ (le_iSup (fun X : 𝒳 =>
        (((pair (S.toMeasure μ) (S.toFun X) - ρω S ρ ω X : ℝ)) : EReal)) 0)
      rw [hφ0]; rfl
  · intro μ hμ
    exact not_lt_top_iff.mp hμ
  · have : envelope S ρ ω = ⋂ X, {μ | pair (S.toMeasure μ) (S.toFun X) ≤ ρω S ρ ω X} := by
      ext μ; simp only [Set.mem_iInter, Set.mem_setOf_eq]; exact hchar μ
    rw [this]
    exact isClosed_iInter fun X => isClosed_le (S.continuous_pair_Y X) continuous_const
  · intro μ hμ ν hν a b ha hb hab
    rw [hchar] at hμ hν ⊢
    intro X
    have hint := S.integrable (a • μ + b • ν) X
    rw [map_add, map_smul, map_smul] at hint ⊢
    rw [pair_comb _ _ a b ha hb _ (S.integrable μ X) (S.integrable ν X) hint]
    have h1 := mul_le_mul_of_nonneg_left (hμ X) ha
    have h2 := mul_le_mul_of_nonneg_left (hν X) hb
    have : ρω S ρ ω X = a * ρω S ρ ω X + b * ρω S ρ ω X := by
      rw [← add_mul, hab, one_mul]
    linarith
  · exact dom_conj_subset_probGiven S hC hC' ρ hρ hlsc ω
  · intro X
    refine ⟨?_, ?_⟩
    · rintro _ ⟨μ, hμ, rfl⟩
      exact (hchar μ).mp hμ X
    · intro b hb
      by_contra hlt
      push_neg at hlt
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
      have hnot : (X, b) ∉ epi := fun h => absurd (show ρω S ρ ω X ≤ b from h) (not_le.mpr hlt)
      obtain ⟨f, u, hfu, hf⟩ := geometric_hahn_banach_point_closed hconv hclosed hnot
      let ℓ : 𝒳 →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ 𝒳 ℝ)
      set a := f ((0 : 𝒳), (1 : ℝ)) with ha_def
      have hfa : ∀ (Y : 𝒳) (r : ℝ), f (Y, r) = ℓ Y + r * a := by
        intro Y r
        have : ((Y, r) : 𝒳 × ℝ) = (Y, 0) + r • ((0 : 𝒳), (1 : ℝ)) := by
          ext <;> simp
        rw [this, map_add, map_smul, smul_eq_mul]
        rfl
      have hmem : ∀ Y : 𝒳, (Y, ρω S ρ ω Y) ∈ epi := fun Y => show ρω S ρ ω Y ≤ ρω S ρ ω Y from le_refl _
      have h1 := hf _ (hmem X)
      rw [hfa] at hfu h1
      have hapos : 0 < a := by
        by_contra hna
        push_neg at hna
        nlinarith
      have hu0 : u < 0 := by
        have := hf _ (hmem 0)
        rw [hfa, map_zero, hρ0] at this
        linarith
      have hall : ∀ Y, 0 ≤ ℓ Y + ρω S ρ ω Y * a := by
        intro Y
        by_contra hneg
        push_neg at hneg
        set v := ℓ Y + ρω S ρ ω Y * a
        have htpos : 0 < u / v + 1 := by
          have : 0 < u / v := div_pos_of_neg_of_neg hu0 hneg
          linarith
        have := hf _ (hmem ((u / v + 1) • Y))
        rw [hfa, map_smul, hρt _ htpos, smul_eq_mul] at this
        have e : (u / v + 1) * ℓ Y + (u / v + 1) * ρω S ρ ω Y * a = u + v := by
          have hv : v ≠ 0 := ne_of_lt hneg
          have : (u / v + 1) * v = u + v := by field_simp
          rw [← this]; simp only [v]; ring
        linarith
      obtain ⟨μ, hμ⟩ := S.dual_rep_X ((-(1 / a)) • ℓ)
      have hμval : ∀ Y, pair (S.toMeasure μ) (S.toFun Y) = (-ℓ Y) / a := by
        intro Y
        rw [← hμ Y, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring
      have hμenv : μ ∈ envelope S ρ ω := by
        rw [hchar]
        intro Y
        rw [hμval, div_le_iff₀ hapos]
        have := hall Y
        linarith
      have hbX := hb ⟨μ, hμenv, rfl⟩
      simp only at hbX
      rw [hμval, div_le_iff₀ hapos] at hbX
      linarith
