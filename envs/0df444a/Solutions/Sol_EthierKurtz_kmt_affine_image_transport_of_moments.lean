-- Prove2me | solution 1 for EthierKurtz.kmt_affine_image_transport_of_moments
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T03:03:08.784962+00:00
-- url     : https://prove2.me/submissions/653c22bb-fe3f-4c30-9c77-0f4a01f88ee0

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation

open MeasureTheory ProbabilityTheory EthierKurtz in
theorem solution
    (mu nu : ProbabilityMeasure Real) (m sig : Real)
    (hsig : 0 <= sig)
    (hmap : Measure.map (fun y : Real => m + sig * y) (nu : Measure Real) = (mu : Measure Real))
    (hmean : MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (nu : Measure Real) = 1)
    (hmu_mean : MeasureTheory.integral (mu : Measure Real) (fun y : Real => y) = m)
    (hmu_variance : variance (fun y : Real => y) (mu : Measure Real) = sig ^ 2)
    (happrox : kmtApproximation nu) :
    kmtApproximation mu := by
  obtain ⟨Q, hind, hlaw, hBM, C, K, lam, hC, hK, hlam, hbound⟩ := happrox
  let T : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} →
      (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} :=
    fun z => (fun i => m + sig * z.1 i, z.2)
  have hT : Measurable T := by
    refine Measurable.prodMk ?_ measurable_snd
    exact measurable_pi_lambda _ fun i => measurable_const.add
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
  have haff : Measurable (fun y : ℝ => m + sig * y) := by fun_prop
  have hcoord : ∀ i : ℕ,
      Measurable (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.1 i) :=
    fun i => (measurable_pi_apply i).comp measurable_fst
  have hB : ∀ t : NNReal,
      Measurable (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.2.val t) :=
    fun t => (measurable_pi_apply t).comp (measurable_subtype_coe.comp measurable_snd)
  have hQT : ((Q.map hT.aemeasurable : ProbabilityMeasure _) : Measure _) =
      (Q : Measure _).map T :=
    ProbabilityMeasure.toMeasure_map _ _
  refine ⟨Q.map hT.aemeasurable, ?_, ?_, ?_, ?_⟩
  · rw [hQT, iIndepFun_iff_measure_inter_preimage_eq_mul]
    have h2 := hind.comp (fun _ x => m + sig * x) (fun _ => haff)
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h2
    intro S sets hS
    have hmS : MeasurableSet (⋂ i ∈ S,
        (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.1 i) ⁻¹' sets i) :=
      Finset.measurableSet_biInter S fun i hi => hcoord i (hS i hi)
    rw [Measure.map_apply hT hmS,
      Finset.prod_congr rfl fun i hi => Measure.map_apply hT (hcoord i (hS i hi))]
    simp only [Set.preimage_iInter]
    exact h2 S hS
  · intro i
    refine ⟨(hcoord i).aemeasurable, ?_⟩
    rw [hQT, Measure.map_map (hcoord i) hT]
    have hcomp : (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.1 i) ∘ T
        = (fun y : ℝ => m + sig * y) ∘
          (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.1 i) := rfl
    rw [hcomp, ← Measure.map_map haff (hcoord i), (hlaw i).map_eq, hmap]
  · refine ⟨⟨fun I => ?_⟩, ?_⟩
    · have hF : Measurable (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} =>
          I.restrict (fun t => z.2.val t)) :=
        measurable_pi_lambda _ fun t => hB t
      refine ⟨hF.aemeasurable, ?_⟩
      rw [hQT, Measure.map_map hF hT]
      exact (hBM.hasLaw I).map_eq
    · exact Filter.Eventually.of_forall fun z => z.2.property
  · have hm' : ∫ x : ℝ, x ∂(mu : Measure ℝ) = m := hmu_mean
    have hs' : Real.sqrt (variance (fun x : ℝ => x) (mu : Measure ℝ)) = sig := by
      rw [hmu_variance, Real.sqrt_sq hsig]
    have hm0 : ∫ x : ℝ, x ∂(nu : Measure ℝ) = 0 := hmean
    have hs1 : Real.sqrt (variance (fun x : ℝ => x) (nu : Measure ℝ)) = 1 := by
      rw [hvariance, Real.sqrt_one]
    simp only [hm0, hs1] at hbound
    simp only [hQT, hm', hs']
    have hmeasE : ∀ (n : ℕ) (c a b : ℝ), MeasurableSet
        {z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} |
          ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ c < |(∑ i ∈ Finset.range k, z.1 i) -
            (a * ((k : NNReal) : ℝ) + b * z.2.val (k : NNReal))|} := by
      intro n c a b
      simp only [Set.ofPred_exists, Set.ofPred_and]
      refine MeasurableSet.iUnion fun k =>
        (MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_)
      refine measurableSet_lt measurable_const ?_
      exact ((Finset.measurable_sum _ fun i _ => hcoord i).sub
        (measurable_const.add (measurable_const.mul (hB _)))).abs
    have halg : ∀ (z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b}) (k : ℕ),
        (∑ i ∈ Finset.range k, (T z).1 i) -
            (m * ((k : NNReal) : ℝ) + sig * (T z).2.val (k : NNReal))
          = sig * ((∑ i ∈ Finset.range k, z.1 i) -
            (0 * ((k : NNReal) : ℝ) + 1 * z.2.val (k : NNReal))) := by
      intro z k
      simp only [T, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum, NNReal.coe_natCast]
      ring
    rcases hsig.eq_or_lt with h0 | hpos
    · refine ⟨C, K, lam, hC, hK, hlam, ?_⟩
      intro n hn x hx
      rw [Measure.map_apply hT (hmeasE n _ _ _)]
      refine lt_of_le_of_lt (measure_mono ?_) (hbound n hn x hx)
      intro z hz
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz
      obtain ⟨k, hk1, hkn, hlt⟩ := hz
      exfalso
      rw [halg z k, ← h0, zero_mul, abs_zero] at hlt
      have hlog : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hn)
      have := mul_nonneg hC.le hlog
      linarith
    · refine ⟨sig * C, K, lam / sig, mul_pos hpos hC, hK, div_pos hlam hpos, ?_⟩
      intro n hn x hx
      rw [Measure.map_apply hT (hmeasE n _ _ _)]
      have hx' : 0 < x / sig := div_pos hx hpos
      have hlt2 := hbound n hn (x / sig) hx'
      have hexp : -lam * (x / sig) = -(lam / sig) * x := by ring
      rw [hexp] at hlt2
      refine lt_of_le_of_lt (measure_mono ?_) hlt2
      intro z hz
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
      obtain ⟨k, hk1, hkn, hlt⟩ := hz
      refine ⟨k, hk1, hkn, ?_⟩
      rw [halg z k, abs_mul, abs_of_pos hpos] at hlt
      have hC' : C * Real.log (n : ℝ) + x / sig = (sig * C * Real.log (n : ℝ) + x) / sig := by
        field_simp
      rw [hC', div_lt_iff₀ hpos]
      linarith
