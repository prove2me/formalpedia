-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.exists_variational_maximum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:17:56.915551+00:00
-- url     : https://prove2.me/submissions/d3c4114b-4a02-4ae1-968e-381d3df240ec

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Integrability
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Affine
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_VariationalMaximum
import Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_affineSubtract_readable
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_affineSubtract_readable
import Theorems.Thm_FunctionalInequalities_Analysis_lowerTruncate_convexification_readable
import Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_limit_ge_normalized_supremum_readable
import Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_normalized_competitor_readable
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_affineSubtract_potentialIntegrable_readable
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_biconjugate_lowerTruncate_potentialIntegrable_readable
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_integral_affineSubtract_readable

section
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- One finite value excludes `-∞` for the entire Legendre transform. -/
theorem FunctionalInequalities.Analysis.legendre_ne_bot (φ : E → EReal) (hφ : ProperPotential φ) (y : E) :
    legendre φ y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hφ.2
  have hb := hφ.1 x
  lift φ x to ℝ using ⟨hx, hb⟩ with r hr
  have hle : ((inner ℝ x y - r : ℝ) : EReal) ≤ legendre φ y := by
    change ((inner ℝ x y - r : ℝ) : EReal) ≤
      ⨆ z : E, (inner ℝ z y : EReal) - φ z
    simpa only [← hr, EReal.coe_sub] using
      (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hle)
/-- Fenchel inequality for a proper extended potential; no convexity is assumed. -/
theorem FunctionalInequalities.Analysis.fenchel_le (φ : E → EReal) (hφ : ProperPotential φ) (x y : E) :
    (inner ℝ x y : EReal) ≤ φ x + legendre φ y := by
  have h := le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x
  have hi := (EReal.sub_le_iff_le_add (.inl (hφ.1 x))
    (.inr (legendre_ne_bot φ hφ y))).mp h
  simpa only [add_comm] using hi
/-- The biconjugate never exceeds a proper extended potential. -/
theorem FunctionalInequalities.Analysis.biconjugate_le (φ : E → EReal) (hφ : ProperPotential φ) (x : E) :
    legendre (legendre φ) x ≤ φ x := by
  apply iSup_le
  intro y
  exact EReal.sub_le_of_le_add (by
    simpa only [real_inner_comm] using fenchel_le φ hφ x y)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A single finite-value witness makes the lower truncation proper;
the input need not be convex, nonnegative, or globally finite. -/
theorem FunctionalInequalities.Analysis.lowerTruncate_proper (φ : E → EReal) (M : ℝ)
    (hfinite : ∃ x, φ x ≠ ⊤) : ProperPotential (lowerTruncate φ M) := by
  refine ⟨?_, ?_⟩
  · intro x
    exact ne_of_gt ((EReal.bot_lt_coe (-M)).trans_le (le_max_right _ _))
  · obtain ⟨x, hx⟩ := hfinite
    refine ⟨x, ne_of_lt ?_⟩
    exact max_lt (Ne.lt_top hx) (EReal.coe_lt_top (-M))
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
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Finite real shifts cancel even when the logarithm is infinite. -/
theorem FunctionalInequalities.Analysis.sub_coe_cancel_shift (z : EReal) (A b : ℝ) :
    (z - (b : EReal)) - ((A - b : ℝ) : EReal) = z - (A : EReal) := by
  induction z with
  | bot => simp
  | top => rw [EReal.top_sub_coe b, EReal.top_sub_coe (A - b), EReal.top_sub_coe A]
  | coe z =>
    norm_cast
    ring
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
omit [MeasurableSpace E] in
/-- The actual extended truncation has the expected real value at every finite
input point. Infinite values are not silently converted to zero in this identity. -/
theorem FunctionalInequalities.Probability.MomentMeasure.lowerTruncate_toReal_of_finite (f : E → EReal) (M : ℝ) (x : E)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    (lowerTruncate f M x).toReal = max (f x).toReal (-M) := by
  change (max (f x) ((-M : ℝ) : EReal)).toReal = max (f x).toReal (-M)
  lift f x to ℝ using ⟨ht, hb⟩ with r hr
  rcases le_total r (-M) with h | h
  · simp only [EReal.toReal_coe,
      max_eq_right (EReal.coe_le_coe_iff.mpr h), max_eq_right h]
  · simp only [EReal.toReal_coe,
      max_eq_left (EReal.coe_le_coe_iff.mpr h), max_eq_left h]
/-- Lower truncation preserves the source admissibility for every real cutoff,
with no global finiteness, convexity or measurability assumption on the input. -/
theorem FunctionalInequalities.Probability.MomentMeasure.lowerTruncate_potentialIntegrable [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hf : PotentialIntegrable f μ) :
    PotentialIntegrable (lowerTruncate f M) μ := by
  have hae : (fun x => (lowerTruncate f M x).toReal) =ᵐ[μ]
      (fun x => max (f x).toReal (-M)) := by
    filter_upwards [hf.2.1] with x hx
    exact lowerTruncate_toReal_of_finite f M x hx (hf.1 x)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ne_of_gt ((EReal.bot_lt_coe (-M)).trans_le (le_max_right _ _))
  · filter_upwards [hf.2.1] with x hx
    exact ne_of_lt (max_lt (Ne.lt_top hx) (EReal.coe_lt_top (-M)))
  · exact (hf.2.2.sup (integrable_const (-M))).congr hae.symm
end Truncation
section Convexification
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E}
/-- The integral comparison needed for the source convexification step follows
from the admissibility just proved and the actual pointwise biconjugate bound. -/
theorem FunctionalInequalities.Probability.MomentMeasure.integral_biconjugate_lowerTruncate_le [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ) :
    (∫ x, (legendre (legendre (lowerTruncate f M)) x).toReal ∂μ) ≤
      ∫ x, (lowerTruncate f M x).toReal ∂μ := by
  have hg := lowerTruncate_potentialIntegrable f M hf
  have hc := biconjugate_lowerTruncate_potentialIntegrable_readable f M hμ hf
  have hproper := lowerTruncate_proper f M (potentialIntegrable_exists_finite f hμ hf)
  apply integral_mono_ae hc.2.2 hg.2.2
  filter_upwards [hg.2.1] with x hx
  exact EReal.toReal_le_toReal (biconjugate_le _ hproper x) (hc.1 x) hx
end Convexification
end
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
/-- The actual translated conjugate mass for a right-translation-invariant
background measure, retaining both zero and infinite values. -/
theorem FunctionalInequalities.Probability.MomentMeasure.mass_legendre_affineSubtract (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (a : E) (b : ℝ) :
    mass dx (legendre (affineSubtract f a b)) =
      EReal.exp ((-b : ℝ) : EReal) * mass dx (legendre f) := by
  have hneg (x : E) :
      -(legendre f (x + a) + (b : EReal)) =
        -legendre f (x + a) + ((-b : ℝ) : EReal) := by
    simpa only [sub_eq_add_neg, EReal.coe_neg] using
      (EReal.neg_add (.inr (EReal.coe_ne_top b)) (.inr (EReal.coe_ne_bot b)))
  unfold mass density
  simp_rw [legendre_affineSubtract_readable, hneg, EReal.exp_add]
  rw [lintegral_mul_const' _ _ (by simp)]
  rw [lintegral_add_right_eq_self (μ := dx) (fun y : E => EReal.exp (-legendre f y)) a]
  exact mul_comm _ _
end
section
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E}
omit [BorelSpace E] in
/-- On a centered probability measure, the linear integral vanishes and the
constant contributes exactly its value, rather than total-mass times its value. -/
theorem FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract_of_probability [CompleteSpace E] [IsProbabilityMeasure μ]
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : (∫ x, x ∂μ) = 0) :
    (∫ x, (affineSubtract f a b x).toReal ∂μ) = (∫ x, (f x).toReal ∂μ) - b := by
  have hlin : (∫ x, inner ℝ a x ∂μ) = 0 := by
    simpa only [innerSL_apply_apply, hbar, map_zero] using (innerSL ℝ a).integral_comp_comm hfirst
  simpa [hlin] using integral_affineSubtract_readable f a b hf hfirst
/-- Exact extended logarithm correction for the actual conjugate mass. -/
theorem FunctionalInequalities.Probability.MomentMeasure.log_mass_legendre_affineSubtract (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (a : E) (b : ℝ) :
    ENNReal.log (mass dx (legendre (affineSubtract f a b))) =
      ENNReal.log (mass dx (legendre f)) - (b : EReal) := by
  rw [mass_legendre_affineSubtract, ENNReal.log_mul_add, EReal.log_exp, EReal.coe_neg]
  rw [add_comm]
  rfl
/-- CEK's functional is invariant under the actual affine subtraction for a
centered probability measure, retaining zero/infinite exponential mass. -/
theorem FunctionalInequalities.Probability.MomentMeasure.variationalFunctional_affineSubtract [CompleteSpace E] [IsProbabilityMeasure μ]
    (dx : Measure E) [Measure.IsAddRightInvariant dx]
    (f : E → EReal) (a : E) (b : ℝ) (hf : PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : (∫ x, x ∂μ) = 0) :
    variationalFunctional dx μ (affineSubtract f a b) = variationalFunctional dx μ f := by
  unfold variationalFunctional
  rw [log_mass_legendre_affineSubtract, integral_affineSubtract_of_probability f a b hf hfirst hbar]
  exact sub_coe_cancel_shift _ _ b
end
end
end
end

noncomputable section
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- **CEK Proposition12 (38).** Actual variational attainment for every
admissible competitor, with an actual convex lsc admissible witness whose
Legendre exponential mass is1. Original measure hypotheses only; neither a
maximizing sequence, convergence, desired bound nor maximizer is supplied. -/
theorem solution (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ φ : E → EReal, FunctionalInequalities.Analysis.ConvexPotential φ ∧ LowerSemicontinuous φ ∧ FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable φ μ ∧
      FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre φ) = 1 ∧
      ∀ f : E → EReal, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f μ →
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ f ≤ FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ φ := by
  obtain ⟨S, ψ, _hψconv, hpψ, hψnn, hψ0, hZpos, hZfin, hS, hnormSup⟩ :=
    FunctionalInequalities.KLS.CEK.exists_limit_ge_normalized_supremum_readable dx μ hsub hfirstMoment hbar
  have hμ : μ ≠ 0 := by
    intro hz
    have hu : μ univ = 1 := measure_univ
    simp only [hz, Measure.coe_zero, Pi.zero_apply, zero_ne_one] at hu
  have htr : FunctionalInequalities.Analysis.lowerTruncate ψ 0 = ψ := by
    funext x
    simpa only [FunctionalInequalities.Analysis.lowerTruncate, neg_zero, EReal.coe_zero] using max_eq_left (hψnn x)
  have hwit : ∃ x, ψ x ≠ ⊤ := ⟨0, by rw [hψ0]; exact EReal.zero_ne_top⟩
  obtain ⟨hc, _hclsc, _hproper, _hbounds, hdual⟩ := FunctionalInequalities.Analysis.lowerTruncate_convexification_readable ψ 0 hwit
  have hpc := FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable_readable ψ 0 hμ hpψ
  have hint := FunctionalInequalities.Probability.MomentMeasure.integral_biconjugate_lowerTruncate_le ψ 0 hμ hpψ
  simp only [htr] at hc hdual hpc hint
  let c : E → EReal := FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre ψ)
  have hdualfun : FunctionalInequalities.Analysis.legendre c = FunctionalInequalities.Analysis.legendre ψ := funext hdual
  have hmass : FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre c) = FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre ψ) := congrArg (FunctionalInequalities.Probability.MomentMeasure.mass dx) hdualfun
  have hZcpos : 0 < FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre c) := by rw [hmass]; exact hZpos
  have hZcfin : FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre c) ≠ ⊤ := by rw [hmass]; exact hZfin
  have hIc : FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ ψ ≤ FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ c := by
    unfold FunctionalInequalities.Probability.MomentMeasure.variationalFunctional
    rw [hmass]
    exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr hint)
  let V : ℝ := Real.log (FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre c)).toReal - ∫ x, (c x).toReal ∂μ
  have hV : FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ c = (V : EReal) := by
    unfold FunctionalInequalities.Probability.MomentMeasure.variationalFunctional
    rw [ENNReal.log_pos_real hZcpos.ne' hZcfin, ← EReal.coe_sub]
  have hmax : ∀ f : E → EReal, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f μ →
      FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ f ≤ FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ c := by
    intro f hf
    have heps : ∀ ε : ℝ, 0 < ε → FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ f ≤ ((V + ε : ℝ) : EReal) := by
      intro ε hε
      obtain ⟨η, hcη, hpη, hnnη, hzη, hvalue⟩ :=
        FunctionalInequalities.KLS.CEK.exists_normalized_competitor_readable dx μ hsub hfirstMoment hbar f hf ε hε
      have hη := (hnormSup η hcη hpη hnnη hzη).trans (hS.trans hIc)
      rw [hV] at hη
      simpa only [EReal.coe_add] using hvalue.trans (add_le_add hη (le_refl (ε : EReal)))
    rw [hV]
    have ht : Tendsto (fun ε : ℝ => ((V + ε : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (V : EReal)) := by
      have hcont : Continuous (fun ε : ℝ => ((V + ε : ℝ) : EReal)) :=
        continuous_coe_real_ereal.comp (continuous_const.add continuous_id)
      simpa only [add_zero] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact heps ε hε
  let b : ℝ := Real.log (FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre c)).toReal
  let φ := FunctionalInequalities.Analysis.affineSubtract c 0 b
  have hpφ : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable φ μ := FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable_readable c 0 b hpc hfirstMoment
  have hcφ : FunctionalInequalities.Analysis.ConvexPotential φ := ⟨hpφ.1, FunctionalInequalities.Analysis.convex_epigraph_affineSubtract_readable c 0 b hc.2⟩
  have hlsφ : LowerSemicontinuous φ := by
    have heq : φ = FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.affineSubtract (FunctionalInequalities.Analysis.legendre ψ) 0 (-b)) := by
      funext x
      rw [FunctionalInequalities.Analysis.legendre_affineSubtract_readable]
      simp only [φ, c, FunctionalInequalities.Analysis.affineSubtract, inner_zero_left, zero_add, add_zero, EReal.coe_neg, sub_eq_add_neg]
    rw [heq]
    exact FunctionalInequalities.Analysis.lowerSemicontinuous_legendre _
  have hmassφ : FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre φ) = 1 := by
    apply ENNReal.log_injective
    rw [FunctionalInequalities.Probability.MomentMeasure.log_mass_legendre_affineSubtract dx c 0 b, ENNReal.log_pos_real hZcpos.ne' hZcfin]
    change ((b : EReal) - (b : EReal)) = ENNReal.log 1
    rw [← EReal.coe_sub, sub_self, EReal.coe_zero, ENNReal.log_one]
  have hIφ : FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ φ = FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ c :=
    FunctionalInequalities.Probability.MomentMeasure.variationalFunctional_affineSubtract dx c 0 b hpc hfirstMoment hbar
  refine ⟨φ, hcφ, hlsφ, hpφ, hmassφ, ?_⟩
  intro f hf
  rw [hIφ]
  exact hmax f hf
