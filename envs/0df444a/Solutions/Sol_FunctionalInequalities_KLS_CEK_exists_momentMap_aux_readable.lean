-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.exists_momentMap_aux_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:22.475284+00:00
-- url     : https://prove2.me/submissions/8586ab95-8799-421d-8a6d-131c8182bf4a

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Integrability
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_MomentMap
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_bounded_perturbation_finite_curve_readable
import Theorems.Thm_FunctionalInequalities_KLS_CEK_bounded_source_lipschitz_primal_readable
import Theorems.Thm_FunctionalInequalities_KLS_CEK_hasDerivAt_integral_exp_neg_legendre_add_smul_readable

section
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Every affine summand of the actual extended-real conjugate is continuous,
including when its fixed intercept is an infinite value. -/
theorem FunctionalInequalities.Analysis.continuous_legendre_summand (φ : E → EReal) (x : E) :
    Continuous (fun y : E => (inner ℝ x y : EReal) - φ x) := by
  by_cases hb : φ x = ⊥
  · simpa only [hb, EReal.coe_sub_bot] using
      (continuous_const : Continuous (fun _ : E => (⊤ : EReal)))
  by_cases ht : φ x = ⊤
  · simpa only [ht, EReal.sub_top] using
      (continuous_const : Continuous (fun _ : E => (⊥ : EReal)))
  lift φ x to ℝ using ⟨ht, hb⟩ with r hr
  have hc : Continuous (fun y : E => inner ℝ x y - r) :=
    (continuous_const.inner continuous_id).sub continuous_const
  simpa only [Function.comp_def, ← hr, ← EReal.coe_sub] using continuous_coe_real_ereal.comp hc
/-- The conjugate is lower semicontinuous for any extended-real input;
no properness, convexity, finite dimension or global finiteness is required. -/
theorem FunctionalInequalities.Analysis.lowerSemicontinuous_legendre (φ : E → EReal) :
    LowerSemicontinuous (legendre φ) := by
  exact lowerSemicontinuous_iSup (fun x =>
    (continuous_legendre_summand φ x).lowerSemicontinuous)
end
end
end

section
noncomputable section
section
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
section Truncation
variable {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
/-- A nonzero measure and the source a.e. finiteness give a real finite-domain
witness; probability normalization and centering are unnecessary. -/
theorem FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite (f : E → EReal) (hμ : μ ≠ 0)
    (hf : PotentialIntegrable f μ) : ∃ x, f x ≠ ⊤ := by
  let : NeZero μ := ⟨hμ⟩
  exact hf.2.1.exists
end Truncation
end
end
end
end

noncomputable section
open MeasureTheory Set
open scoped Topology
open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **Weak moment map of a bounded isotropic law** (Cordero-Erausquin–Klartag arXiv:1304.0630v1,
Theorem 2, existence, via the bounded CEK primal `bounded_source_lipschitz_primal` and the first
variation; weak Letwin route): for an isotropic probability law `μ` supported in the
closed ball of radius `L`, there is a convex `L`-Lipschitz potential `ψ` with `∫ e^{-ψ} = 1`
whose a.e. gradient pushes the law `e^{-ψ} dx` forward to `μ`. No regularity beyond Lipschitz is
claimed. -/
 theorem solution (μ : ProbabilityMeasure E)
    (hμ : FunctionalInequalities.KLS.Isotropic μ) (L : NNReal) (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ ψ : E → ℝ, ConvexOn ℝ (univ : Set E) ψ ∧ LipschitzWith L ψ ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (fun x => -ψ x)).map (gradient ψ) = (μ : Measure E) := by
  classical
  obtain ⟨q, a, m, ψ, hq, hlsc, hqint, hqball, ha, hqa, hfloor, hleg, hupper,
    hψdef, hψ, hmass, hconv, hlip, hcont, hint, hnorm, hprob, hmax⟩ :=
    FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal_readable μ hμ L hL
  refine ⟨ψ, hconv, hlip, hnorm, ?_⟩
  have hμne : (μ : Measure E) ≠ 0 := by
    intro hzero
    have h := (measure_univ : (μ : Measure E) univ = 1)
    rw [hzero] at h
    simp at h
  have hqproper : FunctionalInequalities.Analysis.ProperPotential q :=
    ⟨hq.1, FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite q hμne hqint⟩
  have hgrad : Measurable (gradient ψ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ ψ)
  let ν : Measure E := (volume : Measure E).tilted (fun x => -ψ x)
  have hνprob : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact isProbabilityMeasure_tilted hint
  have hpush : ν.map (gradient ψ) = (μ : Measure E) := by
    have hmapfinite : IsFiniteMeasure (ν.map (gradient ψ)) :=
      ⟨by
        rw [Measure.map_apply hgrad MeasurableSet.univ]
        simp only [preimage_univ, hνprob.measure_univ]
        exact ENNReal.one_lt_top⟩
    apply @ext_of_forall_integral_eq_of_IsFiniteMeasure E _ _ _ _
      (ν.map (gradient ψ)) (μ : Measure E) hmapfinite inferInstance
    intro b
    have hb : Continuous (b : E → ℝ) := b.continuous
    have hM : ∀ z, |b z| ≤ (‖b‖ : ℝ) := by
      intro z
      simpa only [Real.norm_eq_abs] using b.norm_coe_le_norm z
    let Z : ℝ → ℝ := fun t =>
      ∫ x, Real.exp
        (-(FunctionalInequalities.Analysis.legendre (fun z => q z + ((t * b z : ℝ) : EReal)) x).toReal)
        ∂(volume : Measure E)
    have hZdata : ∀ t : ℝ, 0 < Z t ∧
        FunctionalInequalities.Probability.MomentMeasure.mass (volume : Measure E)
            (FunctionalInequalities.Analysis.legendre (fun z => q z + ((t * b z : ℝ) : EReal))) =
          ENNReal.ofReal (Z t) := by
      intro t
      let φt : E → EReal := fun z => q z + ((t * b z : ℝ) : EReal)
      let ψt : E → ℝ := fun x => (FunctionalInequalities.Analysis.legendre φt x).toReal
      have htop : ∀ x, FunctionalInequalities.Analysis.legendre φt x ≠ ⊤ := by
        intro x
        exact
          (FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_readable q hqproper x
            (hleg x).1 b (‖b‖ : ℝ) (norm_nonneg _) hM t).1
      have hbot : ∀ x, FunctionalInequalities.Analysis.legendre φt x ≠ ⊥ := by
        intro x
        exact
          (FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_readable q hqproper x
            (hleg x).1 b (‖b‖ : ℝ) (norm_nonneg _) hM t).2.1
      have hc : ∀ x, |ψt x - ψ x| ≤ |t| * (‖b‖ : ℝ) := by
        intro x
        dsimp [ψt, φt]
        simpa [hψdef] using
          (FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_readable q hqproper x
            (hleg x).1 b (‖b‖ : ℝ) (norm_nonneg _) hM t).2.2
      let c : ℝ := |t| * (‖b‖ : ℝ)
      have hmeas : AEStronglyMeasurable
          (fun x => Real.exp (-(FunctionalInequalities.Analysis.legendre φt x).toReal))
          (volume : Measure E) := by
        apply Measurable.aestronglyMeasurable
        exact
          (Continuous.measurable
            (Continuous.comp Real.continuous_exp continuous_neg)).comp
          (Measurable.ereal_toReal
            (LowerSemicontinuous.measurable
              (FunctionalInequalities.Analysis.lowerSemicontinuous_legendre φt)))
      have hbound : ∀ᵐ x ∂(volume : Measure E),
          ‖Real.exp (-(FunctionalInequalities.Analysis.legendre φt x).toReal)‖ ≤
            Real.exp c * Real.exp (-ψ x) := by
        filter_upwards [] with x
        have hx := hc x
        have hle : -ψt x ≤ -ψ x + c := by
          have hx' := (abs_le.mp hx).1
          dsimp [c] at hx' ⊢
          linarith
        have he : Real.exp (-ψt x) ≤ Real.exp (-ψ x + c) :=
          Real.exp_le_exp.mpr hle
        dsimp [ψt] at he
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc
          Real.exp (-(FunctionalInequalities.Analysis.legendre φt x).toReal) = Real.exp (-ψt x) := rfl
          _ ≤ Real.exp (-ψ x + c) := he
          _ = Real.exp c * Real.exp (-ψ x) := by
            rw [Real.exp_add]
            exact mul_comm _ _
      have hInt : Integrable
          (fun x => Real.exp (-(FunctionalInequalities.Analysis.legendre φt x).toReal))
          (volume : Measure E) :=
        (hint.const_mul (Real.exp c)).mono' hmeas hbound
      have hnonneg : 0 ≤ᵐ[(volume : Measure E)]
          fun x => Real.exp (-(FunctionalInequalities.Analysis.legendre φt x).toReal) :=
        Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
      have hlow : ∀ᵐ x ∂(volume : Measure E),
          Real.exp (-c) * Real.exp (-ψ x) ≤
            Real.exp (-(FunctionalInequalities.Analysis.legendre φt x).toReal) := by
        filter_upwards [] with x
        have hx := hc x
        have hle : -ψ x - c ≤ -ψt x := by
          have hx' := (abs_le.mp hx).2
          dsimp [c] at hx' ⊢
          linarith
        have he : Real.exp (-ψ x - c) ≤ Real.exp (-ψt x) :=
          Real.exp_le_exp.mpr hle
        dsimp [ψt] at he
        calc
          Real.exp (-c) * Real.exp (-ψ x) =
              Real.exp (-ψ x - c) := by
                rw [← Real.exp_add]
                congr 1
                ring
          _ ≤ Real.exp (-ψt x) := he
          _ = Real.exp (-(FunctionalInequalities.Analysis.legendre φt x).toReal) := rfl
      have hlowint := integral_mono_ae
        (hint.const_mul (Real.exp (-c))) hInt hlow
      have hZpos : 0 < Z t := by
        have hlowint' :
            Real.exp (-c) * 1 ≤ Z t := by
          calc
            Real.exp (-c) * 1 =
                ∫ x, Real.exp (-c) * Real.exp (-ψ x) ∂(volume : Measure E) := by
                  rw [integral_const_mul, hnorm]
            _ ≤ Z t := hlowint
        exact lt_of_lt_of_le (by positivity) hlowint'
      constructor
      · exact hZpos
      · rw [FunctionalInequalities.Probability.MomentMeasure.mass]
        calc
          (∫⁻ x, FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre φt) x ∂(volume : Measure E)) =
              ∫⁻ x, ENNReal.ofReal
                (Real.exp (-(FunctionalInequalities.Analysis.legendre φt x).toReal)) ∂(volume : Measure E) := by
            apply lintegral_congr
            intro x
            rw [FunctionalInequalities.Probability.MomentMeasure.density]
            have hr :
                FunctionalInequalities.Analysis.legendre φt x =
                  ((FunctionalInequalities.Analysis.legendre φt x).toReal : EReal) :=
              (EReal.coe_toReal (htop x) (hbot x)).symm
            have hneg :
                -(FunctionalInequalities.Analysis.legendre φt x) =
                  ((-(FunctionalInequalities.Analysis.legendre φt x).toReal : ℝ) : EReal) := by
              calc
                -(FunctionalInequalities.Analysis.legendre φt x) =
                    -((FunctionalInequalities.Analysis.legendre φt x).toReal : EReal) :=
                  congrArg Neg.neg hr
                _ = ((-(FunctionalInequalities.Analysis.legendre φt x).toReal : ℝ) : EReal) := by
                  rw [EReal.coe_neg]
            rw [hneg]
            exact EReal.exp_coe _
          _ = ENNReal.ofReal
                (∫ x, Real.exp (-(FunctionalInequalities.Analysis.legendre φt x).toReal)
                  ∂(volume : Measure E)) :=
            (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
          _ = ENNReal.ofReal (Z t) := rfl
    have hpot : ∀ t : ℝ,
        FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable
          (fun z => q z + ((t * b z : ℝ) : EReal)) (μ : Measure E) := by
      intro t
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        rw [EReal.add_eq_bot_iff] at hz
        rcases hz with hz | hz
        · exact (hqint.1 z) hz
        · exact (EReal.coe_ne_bot _) hz
      · filter_upwards [hqint.2.1] with z hz
        exact EReal.add_ne_top hz (EReal.coe_ne_top _)
      · have hbint : Integrable (fun z => t * b z) (μ : Measure E) :=
          (b.integrable (μ : Measure E)).const_mul t
        have hi := hqint.2.2.add hbint
        apply hi.congr
        filter_upwards [hqint.2.1] with z hz
        rw [EReal.toReal_add]
        · rfl
        · exact hz
        · exact hqint.1 z
        · exact EReal.coe_ne_top _
        · exact EReal.coe_ne_bot _
    have hIntq : ∀ t : ℝ,
        (∫ z, (q z + ((t * b z : ℝ) : EReal)).toReal ∂(μ : Measure E)) =
          ∫ z, (q z).toReal ∂(μ : Measure E) +
            t * ∫ z, b z ∂(μ : Measure E) := by
      intro t
      have hbint : Integrable (fun z => t * b z) (μ : Measure E) :=
        (b.integrable (μ : Measure E)).const_mul t
      have hqreal : Integrable (fun z => (q z).toReal) (μ : Measure E) :=
        hqint.2.2
      calc
        (∫ z, (q z + ((t * b z : ℝ) : EReal)).toReal ∂(μ : Measure E)) =
            ∫ z, (q z).toReal + t * b z ∂(μ : Measure E) := by
              apply integral_congr_ae
              filter_upwards [hqint.2.1] with z hz
              rw [EReal.toReal_add]
              · rfl
              · exact hz
              · exact hqint.1 z
              · exact EReal.coe_ne_top _
              · exact EReal.coe_ne_bot _
        _ = ∫ z, (q z).toReal ∂(μ : Measure E) +
              ∫ z, t * b z ∂(μ : Measure E) :=
            integral_add hqreal hbint
        _ = ∫ z, (q z).toReal ∂(μ : Measure E) +
              t * ∫ z, b z ∂(μ : Measure E) := by
            rw [integral_const_mul]
    have hJt : ∀ t : ℝ,
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E)
            (fun z => q z + ((t * b z : ℝ) : EReal)) =
          (Real.log (Z t) - ∫ z, (q z).toReal ∂(μ : Measure E) -
            t * ∫ z, b z ∂(μ : Measure E) : EReal) := by
      intro t
      have hz := hZdata t
      rw [FunctionalInequalities.Probability.MomentMeasure.variationalFunctional, hz.2, ENNReal.log_ofReal]
      simp only [if_neg (not_le.mpr hz.1)]
      rw [hIntq t]
      let A : ℝ := ∫ z, (q z).toReal ∂(μ : Measure E)
      let B : ℝ := ∫ z, b z ∂(μ : Measure E)
      change (↑(Real.log (Z t)) - ↑(A + t * B) : EReal) =
        (↑(Real.log (Z t)) - ↑A - ↑t * ↑B : EReal)
      calc
        (↑(Real.log (Z t)) - ↑(A + t * B) : EReal) =
            ↑(Real.log (Z t) - (A + t * B)) :=
          (EReal.coe_sub _ _).symm
        _ = ↑((Real.log (Z t) - A) - t * B) := by
          congr 1
          ring
        _ = (↑(Real.log (Z t)) - ↑A - ↑t * ↑B : EReal) := by
          simp only [EReal.coe_sub, EReal.coe_mul]
    have hJq :
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional (volume : Measure E) (μ : Measure E) q =
          (-(∫ z, (q z).toReal ∂(μ : Measure E)) : EReal) := by
      rw [FunctionalInequalities.Probability.MomentMeasure.variationalFunctional, hmass]
      simp only [ENNReal.log_one, zero_sub]
    have hZ0 : Z 0 = 1 := by
      dsimp [Z]
      simp only [zero_mul, add_zero]
      calc
        (∫ x, Real.exp (-(FunctionalInequalities.Analysis.legendre q x).toReal) ∂(volume : Measure E)) =
            ∫ x, Real.exp (-ψ x) ∂(volume : Measure E) := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [hψ x, EReal.toReal_coe]
        _ = 1 := hnorm
    have hmax0 :
        IsLocalMax
          (fun t => Real.log (Z t) -
            t * ∫ z, b z ∂(μ : Measure E)) 0 := by
      apply IsMaxOn.isLocalMax
      · intro t _
        have hi := hmax
          (fun z => q z + ((t * b z : ℝ) : EReal)) (hpot t)
        rw [hJt t, hJq] at hi
        have hi' := EReal.coe_le_coe_iff.mp hi
        have hi'' :
            Real.log (Z t) - t * ∫ z, b z ∂(μ : Measure E) ≤ 0 := by
          linarith
        simpa [hZ0] using hi''
      · exact Filter.univ_mem
    have hderiv :=
      FunctionalInequalities.KLS.CEK.hasDerivAt_integral_exp_neg_legendre_add_smul_readable q hqproper hlsc ψ hψ hlip hint
        (b : E → ℝ) hb hM
    have hZderiv :
        HasDerivAt Z
          (∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E)) 0 := by
      change HasDerivAt
        (fun t =>
          ∫ x, Real.exp
            (-(FunctionalInequalities.Analysis.legendre (fun z => q z + ((t * b z : ℝ) : EReal)) x).toReal)
            ∂(volume : Measure E))
        (∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E)) 0
      exact hderiv
    have hderivlog :
        HasDerivAt
          (fun t => Real.log (Z t) - t * ∫ x, b x ∂(μ : Measure E))
          (∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E) -
            ∫ x, b x ∂(μ : Measure E)) 0 := by
      let B : ℝ := ∫ x, b x ∂(μ : Measure E)
      have hmul : HasDerivAt (fun t : ℝ => t * B) B 0 := by
        simpa only [id_eq, one_mul] using
          (hasDerivAt_id (0 : ℝ)).mul_const B
      have hlog := HasDerivAt.log hZderiv (by simp [hZ0])
      have hsub := hlog.sub hmul
      change HasDerivAt
        (fun t : ℝ => Real.log (Z t) - t * B)
        (_ / Z 0 - B) 0 at hsub
      rw [hZ0, div_one] at hsub
      simpa only [B] using hsub
    have hEL :
        ∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E) =
          ∫ x, b x ∂(μ : Measure E) :=
      sub_eq_zero.mp (IsLocalMax.hasDerivAt_eq_zero hmax0 hderivlog)
    calc
      ∫ y, b y ∂(ν.map (gradient ψ)) =
          ∫ x, b (gradient ψ x) ∂ν := by
            exact integral_map hgrad.aemeasurable hb.aestronglyMeasurable
      _ = ∫ x, (Real.exp (-ψ x) /
            ∫ y, Real.exp (-ψ y) ∂(volume : Measure E)) •
            b (gradient ψ x) ∂(volume : Measure E) := by
            dsimp [ν]
            exact integral_tilted (fun x => -ψ x) (fun x => b (gradient ψ x))
      _ = ∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E) := by
            simp only [hnorm, div_one, smul_eq_mul]
      _ = ∫ x, b x ∂(μ : Measure E) := hEL
  exact hpush
