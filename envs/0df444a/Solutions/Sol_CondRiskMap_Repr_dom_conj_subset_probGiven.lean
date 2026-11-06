-- Prove2me | solution 1 for CondRiskMap.Repr.dom_conj_subset_probGiven
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:11:33.77376+00:00
-- url     : https://prove2.me/submissions/cc483dd0-6c45-403e-b7cc-ee0a9fdebd38

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

open CondRiskMap.Repr MeasureTheory

namespace CRMDomConjAux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma pair_add (μ : SignedMeasure Ω) {f g : Ω → ℝ} (hf : Integrable f μ.totalVariation)
    (hg : Integrable g μ.totalVariation) : pair μ (f + g) = pair μ f + pair μ g := by
  unfold SignedMeasure.totalVariation at hf hg
  rw [integrable_add_measure] at hf hg
  unfold pair
  simp only [Pi.add_apply]
  rw [integral_add hf.1 hg.1, integral_add hf.2 hg.2]
  ring

lemma pair_smul (μ : SignedMeasure Ω) (c : ℝ) (f : Ω → ℝ) :
    pair μ (c • f) = c * pair μ f := by
  unfold pair
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]
  ring

lemma pair_indicator (μ : SignedMeasure Ω) {B : Set Ω} (hB : MeasurableSet B) :
    pair μ (B.indicator 1) = μ B := by
  unfold pair
  rw [integral_indicator_one hB, integral_indicator_one hB]
  conv_rhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition μ]
  rw [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
    Measure.toSignedMeasure_apply_measurable hB, Measure.toSignedMeasure_apply_measurable hB]

end CRMDomConjAux

open CRMDomConjAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {𝒳 𝒴 : Type*}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hlsc : IsLsc S ρ) :
    ∀ ω, envelope S ρ ω ⊆ ProbGiven S ω := by
  intro ω μ hμ
  obtain ⟨_, _, hA2, hA3⟩ := hρ
  set φ : 𝒳 → ℝ := fun X => pair (S.toMeasure μ) (S.toFun X) - ρω S ρ ω X with hφ
  -- the conjugate is finite, so `φ` is bounded above
  have hbdd : ∃ M : ℝ, ∀ X, φ X ≤ M := by
    have hle : ∀ X, ((φ X : ℝ) : EReal) ≤ conj S ρ μ ω := fun X =>
      le_iSup (fun X : 𝒳 => (((pair (S.toMeasure μ) (S.toFun X) - ρω S ρ ω X : ℝ)) : EReal)) X
    have htop : conj S ρ μ ω ≠ ⊤ := ne_of_lt hμ
    have hbot : conj S ρ μ ω ≠ ⊥ := by
      intro h; have := hle 0; rw [h] at this; exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
    refine ⟨(conj S ρ μ ω).toReal, fun X => ?_⟩
    have := hle X
    rw [← EReal.coe_toReal htop hbot] at this
    exact EReal.coe_le_coe_iff.mp this
  obtain ⟨M, hM⟩ := hbdd
  have hint : ∀ X, Integrable (S.toFun X) (S.toMeasure μ).totalVariation :=
    fun X => S.integrable μ X
  -- Step A: `⟨μ, Y⟩ = Y(ω)` for `Y ∈ 𝒳₁`
  have hshift : ∀ Y ∈ S.X₁, ∀ X, φ (X + Y) =
      φ X + (pair (S.toMeasure μ) (S.toFun Y) - S.toFun Y ω) := by
    intro Y hY X
    simp only [hφ, ρω]
    rw [hA3 Y hY X, map_add, map_add, pair_add _ (hint X) (hint Y)]
    simp only [Pi.add_apply]
    ring
  have hcle : ∀ Y ∈ S.X₁, pair (S.toMeasure μ) (S.toFun Y) - S.toFun Y ω ≤ 0 := by
    intro Y hY
    set c := pair (S.toMeasure μ) (S.toFun Y) - S.toFun Y ω
    have hn : ∀ n : ℕ, φ (n • Y) = φ 0 + n * c := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [succ_nsmul, hshift Y hY, ih]
        push_cast; ring
    by_contra hc
    push_neg at hc
    obtain ⟨n, hn'⟩ := exists_nat_gt ((M - φ 0) / c)
    have h1 := hM (n • Y)
    rw [hn] at h1
    rw [div_lt_iff₀ hc] at hn'
    linarith
  have hpairY : ∀ Y ∈ S.X₁, pair (S.toMeasure μ) (S.toFun Y) = S.toFun Y ω := by
    intro Y hY
    have h1 := hcle Y hY
    have h2 := hcle (-Y) (S.X₁.neg_mem hY)
    have : S.toFun (-Y) = (-1 : ℝ) • S.toFun Y := by rw [map_neg]; simp
    rw [this, pair_smul] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    linarith
  have hB : ∀ B, MeasurableSet[S.F₁] B → S.toMeasure μ B = B.indicator 1 ω := by
    intro B hBm
    obtain ⟨Y, hY, hYe⟩ := hC' B hBm
    have := hpairY Y hY
    rw [hYe, pair_indicator _ (S.F₁_le B hBm)] at this
    exact this
  refine ⟨⟨?_, ?_⟩, hB⟩
  · -- Step B: nonnegativity, via (C) and (A2)
    by_contra hneg
    obtain ⟨X, hX0, hXneg⟩ := hC μ hneg
    set p := pair (S.toMeasure μ) (S.toFun X)
    set t : ℝ := (|M| + |ρω S ρ ω 0| + 1) / (-p)
    have hpos : 0 < -p := by linarith
    have ht : t * (-p) = |M| + |ρω S ρ ω 0| + 1 := by
      exact div_mul_cancel₀ _ (ne_of_gt hpos)
    have hmono : ρω S ρ ω ((-t) • X) ≤ ρω S ρ ω 0 := by
      apply hA2
      intro ω'
      have ht0 : 0 ≤ t := by positivity
      rw [map_smul, map_zero]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      nlinarith [hX0 ω']
    have h1 := hM ((-t) • X)
    simp only [hφ] at h1
    rw [map_smul, pair_smul] at h1
    have hk : -t * pair (S.toMeasure μ) (S.toFun X) = |M| + |ρω S ρ ω 0| + 1 := by
      rw [← ht]; simp only [p]; ring
    have := le_abs_self M
    have := le_abs_self (ρω S ρ ω 0)
    linarith
  · have := hB Set.univ MeasurableSet.univ
    simpa using this
