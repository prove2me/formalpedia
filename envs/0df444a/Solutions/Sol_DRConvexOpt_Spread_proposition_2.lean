-- Prove2me | solution 1 for DRConvexOpt.Spread.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:25:03.975658+00:00
-- url     : https://prove2.me/submissions/5d023645-806a-43ee-8296-b3552023de0b

import Mathlib
import Definitions.Def_DRConvexOpt_Spread_Setting

open MeasureTheory

namespace RRAux_DRSpread

open DRConvexOpt.Spread

lemma posPart_ind {nP : ℕ} (f : Fin nP → ℝ) (θ : ℝ) :
    (fun z : Fin nP → ℝ => max (f ⬝ᵥ z - θ) 0)
      = Set.indicator {z | θ ≤ f ⬝ᵥ z} (fun z => f ⬝ᵥ z - θ) := by
  funext z
  by_cases h : θ ≤ f ⬝ᵥ z
  · rw [Set.indicator_of_mem (by exact h)]; exact max_eq_left (by linarith)
  · rw [Set.indicator_of_notMem (by exact h)]; exact max_eq_right (by linarith)

lemma negPart_ind {nP : ℕ} (f : Fin nP → ℝ) (θ : ℝ) :
    (fun z : Fin nP → ℝ => max (θ - f ⬝ᵥ z) 0)
      = Set.indicator {z | f ⬝ᵥ z < θ} (fun z => θ - f ⬝ᵥ z) := by
  funext z
  by_cases h : f ⬝ᵥ z < θ
  · rw [Set.indicator_of_mem (by exact h)]; exact max_eq_left (by linarith)
  · rw [Set.indicator_of_notMem (by exact h)]; exact max_eq_right (by linarith [not_lt.mp h])

lemma spread_eq {nP : ℕ} (f : Fin nP → ℝ) (θ ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ν : Measure (Fin nP → ℝ)) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z => f ⬝ᵥ z) ν) (hρ : ν.real {z | θ ≤ f ⬝ᵥ z} = ρ) :
    condMeanGe ν f θ - condMeanLt ν f θ
      = ρ⁻¹ * ∫ z, max (f ⬝ᵥ z - θ) 0 ∂ν + (1 - ρ)⁻¹ * ∫ z, max (θ - f ⬝ᵥ z) 0 ∂ν := by
  have hg : Measurable (fun z : Fin nP → ℝ => f ⬝ᵥ z) := by fun_prop
  have hS : MeasurableSet {z : Fin nP → ℝ | θ ≤ f ⬝ᵥ z} := measurableSet_le measurable_const hg
  have hT : MeasurableSet {z : Fin nP → ℝ | f ⬝ᵥ z < θ} := measurableSet_lt hg measurable_const
  have hc : {z : Fin nP → ℝ | f ⬝ᵥ z < θ} = {z | θ ≤ f ⬝ᵥ z}ᶜ := by
    ext z; simp
  have hρ' : ν.real {z | f ⬝ᵥ z < θ} = 1 - ρ := by
    rw [hc, measureReal_compl hS, hρ, probReal_univ]
  have e1 : ∫ z, max (f ⬝ᵥ z - θ) 0 ∂ν = (∫ z in {z | θ ≤ f ⬝ᵥ z}, f ⬝ᵥ z ∂ν) - ρ * θ := by
    rw [posPart_ind, integral_indicator hS, integral_sub hint.integrableOn (integrable_const _),
      setIntegral_const, hρ, smul_eq_mul]
  have e2 : ∫ z, max (θ - f ⬝ᵥ z) 0 ∂ν = (1 - ρ) * θ - (∫ z in {z | f ⬝ᵥ z < θ}, f ⬝ᵥ z ∂ν) := by
    rw [negPart_ind, integral_indicator hT, integral_sub (integrable_const _) hint.integrableOn,
      setIntegral_const, hρ', smul_eq_mul]
  unfold condMeanGe condMeanLt
  rw [e1, e2, hρ, hρ']
  have : (1 - ρ) ≠ 0 := by linarith
  have : ρ ≠ 0 := by linarith
  field_simp
  ring

lemma pt (ρ θ g u v w : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (h1 : g = θ + u - v)
    (h2 : ρ⁻¹ * u + (1 - ρ)⁻¹ * v ≤ w) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |g| ≤ |θ| + w ∧ ρ⁻¹ * max (g - θ) 0 + (1 - ρ)⁻¹ * max (θ - g) 0 ≤ w := by
  have ha : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ0 |>.mpr hρ1.le
  have hb : 1 ≤ (1 - ρ)⁻¹ := one_le_inv₀ (by linarith) |>.mpr (by linarith)
  have hua : u ≤ ρ⁻¹ * u := le_mul_of_one_le_left hu ha
  have hvb : v ≤ (1 - ρ)⁻¹ * v := le_mul_of_one_le_left hv hb
  have hau : 0 ≤ ρ⁻¹ * u := by positivity
  have hbv : 0 ≤ (1 - ρ)⁻¹ * v := mul_nonneg (by linarith) hv
  constructor
  · rw [h1]
    have : |u - v| ≤ w := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    calc |θ + u - v| = |θ + (u - v)| := by ring_nf
      _ ≤ |θ| + |u - v| := abs_add_le _ _
      _ ≤ |θ| + w := by linarith
  · have e1 : max (g - θ) 0 ≤ u := max_le (by linarith) hu
    have e2 : max (θ - g) 0 ≤ v := max_le (by linarith) hv
    have := mul_le_mul_of_nonneg_left e1 (le_of_lt (inv_pos.2 hρ0))
    have := mul_le_mul_of_nonneg_left e2 (le_of_lt (inv_pos.2 (by linarith : (0:ℝ) < 1 - ρ)))
    linarith

lemma meas_set {nP : ℕ} (f : Fin nP → ℝ) (θ ρ : ℝ) :
    MeasurableSet {ω : (Fin nP → ℝ) × (ℝ × ℝ × ℝ) | f ⬝ᵥ ω.1 = θ + uOf ω - vOf ω ∧
      ρ⁻¹ * uOf ω + (1 - ρ)⁻¹ * vOf ω ≤ wOf ω ∧ 0 ≤ uOf ω ∧ 0 ≤ vOf ω} := by
  unfold uOf vOf wOf
  simp only [Set.ofPred_and]
  refine (measurableSet_eq_fun ?_ ?_).inter ((measurableSet_le ?_ ?_).inter
    ((measurableSet_le ?_ ?_).inter (measurableSet_le ?_ ?_))) <;> fun_prop

lemma sup_dir {nP : ℕ} (f : Fin nP → ℝ) (θ σ ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (μ : Measure ((Fin nP → ℝ) × (ℝ × ℝ × ℝ))) (hμ : μ ∈ liftedSpreadSet f θ σ ρ) :
    μ.map Prod.fst ∈ spreadSet f θ σ ρ := by
  obtain ⟨hP, hw, hwσ, hae, hρ⟩ := hμ
  have hg : Measurable (fun z : Fin nP → ℝ => f ⬝ᵥ z) := by fun_prop
  have hfst : Measurable (Prod.fst : (Fin nP → ℝ) × (ℝ × ℝ × ℝ) → (Fin nP → ℝ)) := measurable_fst
  have hP' : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map hfst.aemeasurable
  have hae' : ∀ᵐ ω ∂μ, f ⬝ᵥ ω.1 = θ + uOf ω - vOf ω ∧ ρ⁻¹ * uOf ω + (1 - ρ)⁻¹ * vOf ω ≤ wOf ω ∧
      0 ≤ uOf ω ∧ 0 ≤ vOf ω :=
    (ae_iff_measure_eq (meas_set f θ ρ).nullMeasurableSet).mpr (by rw [hae, measure_univ])
  have hpt : ∀ᵐ ω ∂μ, |f ⬝ᵥ ω.1| ≤ |θ| + wOf ω ∧
      ρ⁻¹ * max (f ⬝ᵥ ω.1 - θ) 0 + (1 - ρ)⁻¹ * max (θ - f ⬝ᵥ ω.1) 0 ≤ wOf ω := by
    filter_upwards [hae'] with ω h
    exact pt ρ θ _ _ _ _ hρ0 hρ1 h.1 h.2.1 h.2.2.1 h.2.2.2
  have hgi : Integrable (fun ω : (Fin nP → ℝ) × (ℝ × ℝ × ℝ) => f ⬝ᵥ ω.1) μ := by
    refine Integrable.mono' ((integrable_const |θ|).add hw) (hg.comp hfst).aestronglyMeasurable ?_
    filter_upwards [hpt] with ω h
    simpa [Real.norm_eq_abs] using h.1
  have hint : Integrable (fun z => f ⬝ᵥ z) (μ.map Prod.fst) :=
    (integrable_map_measure hg.aestronglyMeasurable hfst.aemeasurable).mpr hgi
  have hS : MeasurableSet {z : Fin nP → ℝ | θ ≤ f ⬝ᵥ z} := measurableSet_le measurable_const hg
  have hρ' : (μ.map Prod.fst).real {z | θ ≤ f ⬝ᵥ z} = ρ := by
    rw [map_measureReal_apply hfst hS]; exact hρ
  refine ⟨hP', hint, hρ', ?_⟩
  rw [spread_eq f θ ρ hρ0 hρ1 _ hint hρ']
  have hA : Measurable (fun z : Fin nP → ℝ => max (f ⬝ᵥ z - θ) 0) := by fun_prop
  have hB : Measurable (fun z : Fin nP → ℝ => max (θ - f ⬝ᵥ z) 0) := by fun_prop
  rw [integral_map hfst.aemeasurable hA.aestronglyMeasurable,
    integral_map hfst.aemeasurable hB.aestronglyMeasurable]
  have iA : Integrable (fun ω : (Fin nP → ℝ) × (ℝ × ℝ × ℝ) => max (f ⬝ᵥ ω.1 - θ) 0) μ :=
    (hgi.sub (integrable_const θ)).pos_part
  have iB : Integrable (fun ω : (Fin nP → ℝ) × (ℝ × ℝ × ℝ) => max (θ - f ⬝ᵥ ω.1) 0) μ :=
    ((integrable_const θ).sub hgi).pos_part
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iA.const_mul _) (iB.const_mul _),
    ← hwσ]
  refine integral_mono_ae ((iA.const_mul _).add (iB.const_mul _)) hw ?_
  filter_upwards [hpt] with ω h
  exact h.2

lemma sub_dir {nP : ℕ} (f : Fin nP → ℝ) (θ σ ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ν : Measure (Fin nP → ℝ)) (hν : ν ∈ spreadSet f θ σ ρ) :
    ∃ μ ∈ liftedSpreadSet f θ σ ρ, μ.map Prod.fst = ν := by
  obtain ⟨hP, hint, hρ, hsp⟩ := hν
  rw [spread_eq f θ ρ hρ0 hρ1 ν hint hρ] at hsp
  set s := ρ⁻¹ * ∫ z, max (f ⬝ᵥ z - θ) 0 ∂ν + (1 - ρ)⁻¹ * ∫ z, max (θ - f ⬝ᵥ z) 0 ∂ν with hs
  let T : (Fin nP → ℝ) → (Fin nP → ℝ) × (ℝ × ℝ × ℝ) := fun z =>
    (z, (max (f ⬝ᵥ z - θ) 0, max (θ - f ⬝ᵥ z) 0,
      ρ⁻¹ * max (f ⬝ᵥ z - θ) 0 + (1 - ρ)⁻¹ * max (θ - f ⬝ᵥ z) 0 + (σ - s)))
  have hT : Measurable T := by fun_prop
  have hg : Measurable (fun z : Fin nP → ℝ => f ⬝ᵥ z) := by fun_prop
  have hwm : Measurable (wOf : (Fin nP → ℝ) × (ℝ × ℝ × ℝ) → ℝ) := by unfold wOf; fun_prop
  have iA : Integrable (fun z : Fin nP → ℝ => max (f ⬝ᵥ z - θ) 0) ν :=
    (hint.sub (integrable_const θ)).pos_part
  have iB : Integrable (fun z : Fin nP → ℝ => max (θ - f ⬝ᵥ z) 0) ν :=
    ((integrable_const θ).sub hint).pos_part
  have iW : Integrable (wOf ∘ T) ν :=
    ((iA.const_mul _).add (iB.const_mul _)).add (integrable_const _)
  refine ⟨ν.map T, ⟨Measure.isProbabilityMeasure_map hT.aemeasurable,
    (integrable_map_measure hwm.aestronglyMeasurable hT.aemeasurable).mpr iW, ?_, ?_, ?_⟩, ?_⟩
  · rw [integral_map hT.aemeasurable hwm.aestronglyMeasurable]
    show ∫ z, (ρ⁻¹ * max (f ⬝ᵥ z - θ) 0 + (1 - ρ)⁻¹ * max (θ - f ⬝ᵥ z) 0 + (σ - s)) ∂ν = σ
    rw [integral_add (by exact (iA.const_mul ρ⁻¹).add (iB.const_mul (1 - ρ)⁻¹))
        (integrable_const (σ - s)),
      integral_add (by exact iA.const_mul ρ⁻¹) (by exact iB.const_mul (1 - ρ)⁻¹), integral_const_mul, integral_const_mul,
      integral_const, probReal_univ, one_smul, ← hs]
    ring
  · apply le_antisymm prob_le_one
    have hpre : T ⁻¹' {ω : (Fin nP → ℝ) × (ℝ × ℝ × ℝ) | f ⬝ᵥ ω.1 = θ + uOf ω - vOf ω ∧
        ρ⁻¹ * uOf ω + (1 - ρ)⁻¹ * vOf ω ≤ wOf ω ∧ 0 ≤ uOf ω ∧ 0 ≤ vOf ω} = Set.univ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true, T, uOf, vOf, wOf]
      refine ⟨?_, ?_, le_max_right _ _, le_max_right _ _⟩
      · rcases le_total θ (f ⬝ᵥ z) with h | h
        · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
        · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · linarith
    calc (1 : ENNReal) = ν Set.univ := measure_univ.symm
      _ = ν (T ⁻¹' _) := by rw [hpre]
      _ ≤ _ := Measure.le_map_apply hT.aemeasurable _
  · have hm : MeasurableSet {ω : (Fin nP → ℝ) × (ℝ × ℝ × ℝ) | θ ≤ f ⬝ᵥ ω.1} :=
      measurableSet_le measurable_const (by fun_prop)
    rw [map_measureReal_apply hT hm]
    exact hρ
  · rw [Measure.map_map measurable_fst hT]
    exact Measure.map_id

end RRAux_DRSpread

open DRConvexOpt.Spread in
theorem solution {nP : ℕ} (f : Fin nP → ℝ) (θ σ ρ : ℝ) (hσ : 0 ≤ σ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    spreadSet f θ σ ρ = (fun μ => μ.map Prod.fst) '' liftedSpreadSet f θ σ ρ := by
  ext ν
  constructor
  · intro hν
    obtain ⟨μ, hμ, he⟩ := RRAux_DRSpread.sub_dir f θ σ ρ hρ0 hρ1 ν hν
    exact ⟨μ, hμ, he⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact RRAux_DRSpread.sup_dir f θ σ ρ hρ0 hρ1 μ hμ

#print axioms solution
