-- Prove2me | solution 1 for GIGnBounds.Tail.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:47:02.150046+00:00
-- url     : https://prove2.me/submissions/d999ae6b-b40d-407a-b136-ab4f3934e354

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting
import Theorems.Thm_GIGnBounds_Tail_lemma_8
import Theorems.Thm_GIGnBounds_Tail_lemma_9
import Theorems.Thm_GIGnBounds_Tail_lemma_10

open MeasureTheory ProbabilityTheory GIGnBounds.Tail

theorem solution (μA : Measure ℝ) [IsProbabilityMeasure μA] (hA : IsTimeLaw μA)
    (hA2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μA < ⊤)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : IsIIDSeq P X μA) (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x) :
    P.real {ω | (x : EReal) ≤
        supFrom (fun t => (ordCount (fun j => X j ω) t : ℝ) - rate μA * t - ν * t)} ≤
      Real.exp (-((9 : ℝ) / 100) * (ν / (ν + rate μA)) * (nMoment μA 2)⁻¹ * x) := by
  set μ := rate μA with hμdef
  have hμ : 0 < μ := inv_pos.mpr hA.mean_pos
  have hμmean : μ * mean μA = 1 := by
    rw [hμdef, rate]; exact inv_mul_cancel₀ hA.mean_pos.ne'
  -- the normalised inter-arrival law `Z = μ_A A`
  set f : ℝ → ℝ := fun a => μ * a with hf
  have hfm : Measurable f := measurable_const.mul measurable_id
  set νZ : Measure ℝ := μA.map f with hνZ
  have : IsProbabilityMeasure νZ := Measure.isProbabilityMeasure_map hfm.aemeasurable
  set Z : ℕ → Ω → ℝ := fun i ω => μ * X i ω with hZdef
  have hZ : IsIIDSeq P Z νZ := by
    refine ⟨fun i => hfm.comp (hX.measurable i), ?_, ?_⟩
    · exact hX.indep.comp (fun _ => f) (fun _ => hfm)
    · intro i
      have : Z i = f ∘ X i := rfl
      rw [this, ← Measure.map_map hfm (hX.measurable i), hX.law i]
  have hν0 : νZ (Set.Iio 0) = 0 := by
    rw [hνZ, Measure.map_apply hfm measurableSet_Iio]
    have : f ⁻¹' Set.Iio 0 = Set.Iio 0 := by
      ext a; simp only [hf, Set.mem_preimage, Set.mem_Iio]
      constructor
      · intro h; by_contra h'; push Not at h'; nlinarith
      · intro h; nlinarith
    rw [this]; exact hA.nonneg
  have hν1 : ∫ z, z ∂νZ = 1 := by
    rw [hνZ, integral_map (f := fun z : ℝ => z) hfm.aemeasurable aestronglyMeasurable_id]
    simp only [hf]
    rw [integral_const_mul]
    exact hμmean
  have hν2 : ∫⁻ z, ENNReal.ofReal (z ^ 2) ∂νZ < ⊤ := by
    rw [hνZ, lintegral_map (by fun_prop) hfm]
    simp only [hf]
    have : ∀ a : ℝ, ENNReal.ofReal ((μ * a) ^ 2) = ENNReal.ofReal (μ ^ 2) * ENNReal.ofReal (a ^ 2) := by
      intro a; rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    simp_rw [this]
    rw [lintegral_const_mul _ (by fun_prop)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA2
  -- second moment of `Z`
  set m2 := ∫ w, w ^ 2 ∂νZ with hm2
  have hm2eq : m2 = nMoment μA 2 := by
    rw [hm2, nMoment, hνZ, integral_map hfm.aemeasurable (by fun_prop)]
    congr 1
    ext a
    simp only [hf, ← hμdef]
    rw [Real.rpow_two, mul_comm]
  have hI2 : Integrable (fun z : ℝ => z ^ 2) νZ := by
    refine ⟨(continuous_pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => sq_nonneg z))]
    exact hν2
  have hI1 : Integrable (fun z : ℝ => z) νZ := by
    by_contra h
    rw [integral_undef h] at hν1
    norm_num at hν1
  have hm2ge : 1 ≤ m2 := by
    have h1 : ∫ z, z ∂νZ ≤ ∫ z, (1 + z ^ 2) / 2 ∂νZ := by
      have i3 : Integrable (fun z : ℝ => (1 + z ^ 2) / 2) νZ :=
        ((integrable_const 1).add hI2).div_const 2
      apply integral_mono hI1 i3
      intro z; simp only; nlinarith [sq_nonneg (z - 1)]
    have e3 : ∫ z, (1 + z ^ 2) ∂νZ = ∫ z, (1 : ℝ) ∂νZ + ∫ z, z ^ 2 ∂νZ :=
      integral_add (integrable_const 1) hI2
    rw [integral_div, e3, hν1] at h1
    simp at h1
    linarith
  have hm2pos : 0 < m2 := by linarith
  -- apply Lemmas 10, 9, 8
  set c := μ / (μ + ν) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by rw [hc, div_lt_one (by positivity)]; linarith
  set θ := (1 - c) / (11 * c * m2) with hθdef
  have hθ : 0 < θ := by
    apply div_pos (by linarith); positivity
  have hmgf := GIGnBounds.Tail.lemma_10 νZ hν0 hν1 hν2 c hc0 hc1
  set x' := x * (1 + ν / μ)⁻¹ with hx'
  have hx'pos : 0 < x' := by positivity
  have h9 := GIGnBounds.Tail.lemma_9 νZ hν0 hν1 c hc0 hc1 θ hθ hmgf Ω P Z hZ x' hx'pos
  have h8 := GIGnBounds.Tail.lemma_8 μA hA Ω P X hX ν x hν hx
  rw [h8]
  refine le_trans (le_of_eq ?_) (h9.trans ?_)
  · rfl
  · apply Real.exp_le_exp.mpr
    have hθx : θ * x' = ν * x / (11 * m2 * (μ + ν)) := by
      rw [hθdef, hx', hc]
      field_simp
      ring
    rw [← hm2eq]
    have : (9 : ℝ) / 100 * (ν / (ν + μ)) * m2⁻¹ * x = (9 / 100) * (ν * x / (m2 * (μ + ν))) := by
      field_simp
      ring
    have hpos : 0 < ν * x / (m2 * (μ + ν)) := by positivity
    have : ν * x / (11 * m2 * (μ + ν)) = (1 / 11) * (ν * x / (m2 * (μ + ν))) := by
      field_simp
    nlinarith
