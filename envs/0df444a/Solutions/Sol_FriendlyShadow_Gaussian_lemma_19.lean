-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T11:20:50.170739+00:00
-- url     : https://prove2.me/submissions/4ca4ff47-6e43-44c0-b727-a21700b9e20f

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

set_option autoImplicit false

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace L19Aux

/-- Union bound over the rows for the tail event of the maximum. -/
theorem tail_le {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : Fin n → Ω → EuclideanSpace ℝ (Fin d)) (hx : ∀ i, Measurable (x i))
    (θ : EuclideanSpace ℝ (Fin d)) (hn : (Finset.univ : Finset (Fin n)).Nonempty) (t : ℝ) :
    P {ω | t ≤ Finset.univ.sup' hn (fun i => |⟪θ, x i ω⟫|)} ≤
      ∑ i, (P.map (x i)) {y | t ≤ |⟪y - 0, θ⟫|} := by
  have hsub : {ω | t ≤ Finset.univ.sup' hn (fun i => |⟪θ, x i ω⟫|)} ⊆
      ⋃ i, (x i) ⁻¹' {y | t ≤ |⟪y - 0, θ⟫|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hn (fun i => |⟪θ, x i ω⟫|)
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, sub_zero]
    rw [real_inner_comm]
    linarith [hi ▸ hω]
  refine (measure_mono hsub).trans ((measure_iUnion_fintype_le P _).trans ?_)
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hS : MeasurableSet {y : EuclideanSpace ℝ (Fin d) | t ≤ |⟪y - 0, θ⟫|} :=
    measurableSet_le measurable_const
      ((continuous_abs.comp ((continuous_id.sub continuous_const).inner
        continuous_const)).measurable)
  rw [Measure.map_apply (hx i) hS]

end L19Aux

open MeasureTheory FriendlyShadow.Gaussian RealInnerProductSpace ENNReal in
theorem solution {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : Fin n → Ω → EuclideanSpace ℝ (Fin d))
    (hx : ∀ i, Measurable (x i)) (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hμ : ∀ i, IsDensity (μ i)) (hlaw : ∀ i, P.map (x i) = densityMeasure (μ i))
    (hmean : ∀ i, HasMean (μ i) 0) (r : ℝ) (hr : ∀ i, NthDeviationLE (μ i) 0 n r)
    (θ : EuclideanSpace ℝ (Fin d)) (hθ : ‖θ‖ = 1) :
    ∫⁻ ω, (⨆ i, ENNReal.ofReal |⟪θ, x i ω⟫|) ∂P ≤ ENNReal.ofReal (2 * r) := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp
  have hn : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.2 ⟨⟨0, hnpos⟩⟩
  set f : Ω → ℝ := fun ω => Finset.univ.sup' hn (fun i => |⟪θ, x i ω⟫|) with hf
  have hfm : Measurable f := by
    have h := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin n))) hn
      (f := fun i ω => |⟪θ, x i ω⟫|)
      (fun i _ => (continuous_abs.comp (continuous_const.inner continuous_id)).measurable.comp
        (hx i))
    convert h using 1
    funext ω
    rw [Finset.sup'_apply]
  have hsup : ∀ ω, (⨆ i, ENNReal.ofReal |⟪θ, x i ω⟫|) = ENNReal.ofReal (f ω) := by
    intro ω
    apply le_antisymm
    · exact iSup_le (fun i => ENNReal.ofReal_le_ofReal
        (Finset.le_sup' (fun i => |⟪θ, x i ω⟫|) (Finset.mem_univ i)))
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hn (fun i => |⟪θ, x i ω⟫|)
      rw [hf]
      simp only
      rw [hi]
      exact le_iSup (fun i => ENNReal.ofReal |⟪θ, x i ω⟫|) i
  have hnn : 0 ≤ᵐ[P] f := Filter.Eventually.of_forall (fun ω => by
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' hn (fun i => |⟪θ, x i ω⟫|)
    show 0 ≤ f ω
    rw [hf]
    simp only
    rw [hi]
    exact abs_nonneg _)
  simp_rw [hsup]
  rw [lintegral_eq_lintegral_meas_le P hnn hfm.aemeasurable]
  -- split `Ioi 0` into `Ioc 0 r` and `Ioi r`
  have hcover : Set.Ioi (0 : ℝ) ⊆ Set.Ioc 0 r ∪ Set.Ioi r := by
    intro t ht
    by_cases h : t ≤ r
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (lt_of_not_ge h)
  have h1 : ∫⁻ t in Set.Ioc 0 r, P {a | t ≤ f a} ≤ ENNReal.ofReal r := by
    calc ∫⁻ t in Set.Ioc 0 r, P {a | t ≤ f a}
        ≤ ∫⁻ _t in Set.Ioc 0 r, (1 : ℝ≥0∞) := lintegral_mono (fun t => prob_le_one)
      _ = ENNReal.ofReal r := by
        rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]
  have h2 : ∫⁻ t in Set.Ioi r, P {a | t ≤ f a} ≤ ENNReal.ofReal r := by
    calc ∫⁻ t in Set.Ioi r, P {a | t ≤ f a}
        ≤ ∫⁻ t in Set.Ioi r, ∑ i, densityMeasure (μ i) {y | t ≤ |⟪y - 0, θ⟫|} := by
          refine lintegral_mono (fun t => ?_)
          refine (L19Aux.tail_le P x hx θ hn t).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl (fun i _ => by rw [hlaw i])
      _ = ∑ i, ∫⁻ t in Set.Ioi r, densityMeasure (μ i) {y | t ≤ |⟪y - 0, θ⟫|} := by
          rw [lintegral_finsetSum']
          intro i _
          refine Measurable.aemeasurable ?_
          refine Antitone.measurable (fun s t hst => measure_mono ?_)
          intro y hy
          simp only [Set.mem_ofPred_eq] at hy ⊢
          linarith
      _ ≤ ∑ _i : Fin n, ENNReal.ofReal (r / n) := Finset.sum_le_sum (fun i _ => hr i θ hθ)
      _ = ENNReal.ofReal r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  calc ∫⁻ t in Set.Ioi 0, P {a | t ≤ f a}
      ≤ ∫⁻ t in Set.Ioc 0 r ∪ Set.Ioi r, P {a | t ≤ f a} := lintegral_mono_set hcover
    _ ≤ (∫⁻ t in Set.Ioc 0 r, P {a | t ≤ f a}) + ∫⁻ t in Set.Ioi r, P {a | t ≤ f a} :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * r) := by
        rcases le_or_gt 0 r with hr0 | hr0
        · rw [← ENNReal.ofReal_add hr0 hr0]
          ring_nf
        · rw [ENNReal.ofReal_of_nonpos hr0.le, ENNReal.ofReal_of_nonpos (by linarith)]
          simp
