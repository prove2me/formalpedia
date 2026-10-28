-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_convexified_lowerTruncate_variational_le_add_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:41:13.502722+00:00
-- url     : https://prove2.me/submissions/4e9f9076-7987-4346-bfdc-8ef317703d0d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Integrability
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Truncation
import Theorems.Thm_FunctionalInequalities_Analysis_lowerTruncate_convexification_readable
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_biconjugate_lowerTruncate_potentialIntegrable_readable

section
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The Legendre transform reverses pointwise order, including extended values. -/
theorem FunctionalInequalities.Analysis.legendre_antitone {φ ψ : E → EReal} (h : ∀ x, φ x ≤ ψ x) (y : E) :
    legendre ψ y ≤ legendre φ y := by
  apply iSup_le
  intro x
  exact (EReal.sub_le_sub le_rfl (h x)).trans
    (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
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
end
end
end

section
noncomputable section
section
open MeasureTheory
open scoped ENNReal
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Measurable
variable [MeasurableSpace E]
/-- The monotonicity used for the truncation in CEK (61): increasing the primal
potential increases the mass of the exponential of its negative Legendre transform. -/
theorem FunctionalInequalities.Probability.MomentMeasure.mass_legendre_mono (dx : Measure E) {φ ψ : E → EReal} (h : ∀ x, φ x ≤ ψ x) :
    mass dx (legendre φ) ≤ mass dx (legendre ψ) := by
  apply lintegral_mono
  intro x
  exact EReal.exp_monotone (EReal.neg_le_neg_iff.mpr (legendre_antitone h x))
end Measurable
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

noncomputable section
open FunctionalInequalities.Analysis
section
open MeasureTheory
variable {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
/-- Nonnegative cutoffs do not increase the norm of a real lower truncation. -/
theorem FunctionalInequalities.Probability.MomentMeasure.norm_max_neg_le (r M : ℝ) (hM : 0 ≤ M) : ‖max r (-M)‖ ≤ ‖r‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact (neg_abs_le r).trans (le_max_left _ _)
  · exact max_le (le_abs_self r) ((neg_nonpos.mpr hM).trans (abs_nonneg r))
omit [MeasurableSpace E] in
/-- At a finite input point, the actual sequence of cutoffs eventually leaves
the input unchanged. This avoids any unproved EReal convergence assumption. -/
theorem FunctionalInequalities.Probability.MomentMeasure.tendsto_lowerTruncate_toReal (f : E → EReal) (x : E)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    Filter.Tendsto (fun n : ℕ => (lowerTruncate f (n : ℝ) x).toReal)
      Filter.atTop (nhds ((f x).toReal)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (-(f x).toReal)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (lowerTruncate f (n : ℝ) x).toReal = (f x).toReal := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    rw [lowerTruncate_toReal_of_finite f (n : ℝ) x ht hb, max_eq_left]
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hev)
/-- Dominated convergence for the actual lower truncations, with domination
by the norm of the original real restriction. -/
theorem FunctionalInequalities.Probability.MomentMeasure.tendsto_integral_lowerTruncate [IsFiniteMeasure μ]
    (f : E → EReal) (hf : PotentialIntegrable f μ) :
    Filter.Tendsto (fun n : ℕ => ∫ x, (lowerTruncate f (n : ℝ) x).toReal ∂μ)
      Filter.atTop (nhds (∫ x, (f x).toReal ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖(f x).toReal‖)
  · intro n
    exact (lowerTruncate_potentialIntegrable f (n : ℝ) hf).2.2.aestronglyMeasurable
  · exact hf.2.2.norm
  · intro n
    filter_upwards [hf.2.1] with x hx
    rw [lowerTruncate_toReal_of_finite f (n : ℝ) x hx (hf.1 x)]
    exact norm_max_neg_le _ _ (Nat.cast_nonneg n)
  · filter_upwards [hf.2.1] with x hx
    exact tendsto_lowerTruncate_toReal f x hx (hf.1 x)
/-- The signed difference of the actual integrals tends to zero; it is the
source's truncation error rather than an assumed tail bound. -/
theorem FunctionalInequalities.Probability.MomentMeasure.tendsto_integral_lowerTruncate_error [IsFiniteMeasure μ]
    (f : E → EReal) (hf : PotentialIntegrable f μ) :
    Filter.Tendsto (fun n : ℕ =>
      (∫ x, (lowerTruncate f (n : ℝ) x).toReal ∂μ) - ∫ x, (f x).toReal ∂μ)
      Filter.atTop (nhds 0) := by
  have hconst : Filter.Tendsto (fun _ : ℕ => ∫ x, (f x).toReal ∂μ)
      Filter.atTop (nhds (∫ x, (f x).toReal ∂μ)) := tendsto_const_nhds
  simpa only [sub_self] using (tendsto_integral_lowerTruncate f hf).sub hconst
end
section
open MeasureTheory
/-- The finite integral error controls subtraction from any extended logarithm,
including `±∞`; no positive finite exponential-mass assumption is required. -/
theorem FunctionalInequalities.Probability.MomentMeasure.sub_coe_le_sub_coe_add (z : EReal) (A C ε : ℝ) (h : C - A ≤ ε) :
    z - (A : EReal) ≤ (z - (C : EReal)) + (ε : EReal) := by
  induction z with
  | bot => simp
  | top => simp
  | coe z =>
    exact_mod_cast (show z - A ≤ z - C + ε by linarith)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E}
/-- Every actual admissible competitor has a convex lsc admissible competitor,
obtained by the actual biconjugate of a positive integer lower truncation, whose
variational value loses at most epsilon. The cutoff is selected from dominated
convergence, and the statement retains extended zero/infinite exponential mass. -/
theorem solution [IsFiniteMeasure μ]
    (dx : Measure E) (f : E → EReal) (hμ : μ ≠ 0) (hf : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      let c := FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.lowerTruncate f (n : ℝ)))
      FunctionalInequalities.Analysis.ConvexPotential c ∧ LowerSemicontinuous c ∧ FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable c μ ∧
        FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ f ≤ FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ c + (ε : EReal) := by
  have hev := (FunctionalInequalities.Probability.MomentMeasure.tendsto_integral_lowerTruncate_error f hf).eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let n := N + 1
  let g := FunctionalInequalities.Analysis.lowerTruncate f (n : ℝ)
  let c := FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre g)
  have herr : (∫ x, (g x).toReal ∂μ) - ∫ x, (f x).toReal ∂μ < ε :=
    hN n (Nat.le_succ N)
  have hfinite := FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite f hμ hf
  obtain ⟨hc, hls, _, _, hdual⟩ := FunctionalInequalities.Analysis.lowerTruncate_convexification_readable f (n : ℝ) hfinite
  have hcint := FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable_readable f (n : ℝ) hμ hf
  have hcle := FunctionalInequalities.Probability.MomentMeasure.integral_biconjugate_lowerTruncate_le f (n : ℝ) hμ hf
  have hdualFun : FunctionalInequalities.Analysis.legendre c = FunctionalInequalities.Analysis.legendre g := funext hdual
  have hmass : FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre c) = FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre g) := congrArg (FunctionalInequalities.Probability.MomentMeasure.mass dx) hdualFun
  have hmono : ENNReal.log (FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre f)) ≤ ENNReal.log (FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre g)) :=
    ENNReal.log_le_log (FunctionalInequalities.Probability.MomentMeasure.mass_legendre_mono dx (fun x => le_max_left _ _))
  refine ⟨n, Nat.succ_pos N, hc, hls, hcint, ?_⟩
  change ENNReal.log (FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre f)) - (∫ x, (f x).toReal ∂μ : ℝ) ≤
    (ENNReal.log (FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre c)) - (∫ x, (c x).toReal ∂μ : ℝ)) + (ε : EReal)
  rw [hmass]
  exact (EReal.sub_le_sub hmono le_rfl).trans
    (FunctionalInequalities.Probability.MomentMeasure.sub_coe_le_sub_coe_add _ _ _ ε (by linarith [hcle]))
