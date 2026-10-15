-- Prove2me | solution 1 for CauchyRiemannIndex.sConv_annihilator_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T19:48:28.958166+00:00
-- url     : https://prove2.me/submissions/af637206-c440-4317-a595-a8e6188354b3

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Theorems.Thm_CauchyRiemannIndex_periodic_weak_solution_bound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Order.Compact

-- ===== Scratch/CR411Bridge.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- Matrices as continuous linear maps of `ℝ²ⁿ`, continuously in the matrix. -/
def matCLM (n : ℕ) : Mat n →ₗ[ℝ] (Vec n →L[ℝ] Vec n) :=
  (LinearMap.toContinuousLinearMap : (Vec n →ₗ[ℝ] Vec n) ≃ₗ[ℝ] (Vec n →L[ℝ] Vec n)).toLinearMap ∘ₗ
    (Matrix.toEuclideanLin : Mat n ≃ₗ[ℝ] (Vec n →ₗ[ℝ] Vec n)).toLinearMap

lemma matCLM_apply (A : Mat n) (v : Vec n) : matCLM n A v = Matrix.toEuclideanLin A v := rfl

lemma continuous_matCLM : Continuous (matCLM n) := LinearMap.continuous_of_finiteDimensional _

/-- A uniform operator bound for a continuous `1`-periodic matrix loop. -/
lemma exists_bound_loop (Sinf : ℝ → Mat n) (hc : Continuous Sinf) (hper : Function.Periodic Sinf 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t (v : Vec n), ‖Matrix.toEuclideanLin (Sinf t) v‖ ≤ M * ‖v‖ := by
  have hg : Continuous fun t => matCLM n (Sinf t) := continuous_matCLM.comp hc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t v => ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
  rw [← matCLM_apply, hty]
  calc ‖matCLM n (Sinf y) v‖ ≤ ‖matCLM n (Sinf y)‖ * ‖v‖ := (matCLM n (Sinf y)).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by
      gcongr
      exact (hC y (Set.Ico_subset_Icc_self hy)).trans (le_max_left _ _)

lemma exists_bound_mat (A : Mat n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : Vec n), ‖Matrix.toEuclideanLin A v‖ ≤ M * ‖v‖ :=
  ⟨‖matCLM n A‖, norm_nonneg _, fun v => (matCLM n A).le_opNorm v⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous map on `ℝ × ℝ` vanishing for large `|s|` is in `L^p` of the strip. -/
lemma memLp_of_vanish {E : Type*} [NormedAddCommGroup E] (g : ℝ × ℝ → E) (hg : Continuous g)
    (R : ℝ) (hR : ∀ s t, R < |s| → g (s, t) = 0) : MemLp g p cylMeasure := by
  set K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : K.indicator g =ᵐ[cylMeasure] g := by
    unfold cylMeasure
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ico) ?_
    rintro ⟨s, t⟩ ⟨-, ht⟩
    by_cases hx : (s, t) ∈ K
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have : R < |s| := by
        by_contra h
        push_neg at h
        exact hx ⟨abs_le.1 h, Set.Ico_subset_Icc_self ht⟩
      exact (hR s t this).symm
  refine (memLp_congr_ae hae).1 ((memLp_indicator_iff_restrict hKm).2 ?_)
  haveI : IsFiniteMeasure (cylMeasure.restrict K) := by
    refine isFiniteMeasure_restrict.2 (ne_of_lt (lt_of_le_of_lt ?_ (hKc.measure_lt_top (μ := (volume : Measure (ℝ × ℝ))))))
    exact Measure.le_iff'.1 Measure.restrict_le_self K
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C (ae_restrict_of_forall_mem hKm hC)

lemma partialS_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialS u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialS, hev.fderiv_eq]

lemma partialT_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialT u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialT, hev.fderiv_eq]

lemma IsTestSection.continuous {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Continuous u :=
  hu.1.continuous

lemma IsTestSection.continuous_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialS u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.continuous_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialT u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.memLp {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : MemLp u p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish u hu.continuous R hR

lemma IsTestSection.memLp_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialS u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialS R fun s t hs => partialS_eq_zero R hR hs

lemma IsTestSection.memLp_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialT u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialT R fun s t hs => partialT_eq_zero R hR hs

lemma IsTestSection.sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u - v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.sub hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u + v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.add hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    IsTestSection (c • u) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  refine ⟨ContDiff.const_smul c hu.1, fun s t => by simp [hu.2.1], R₁, fun s t hs => ?_⟩
  simp [h₁ s t hs]

lemma isTestSection_zero : IsTestSection (0 : ℝ × ℝ → Vec n) :=
  ⟨contDiff_const, fun _ _ => rfl, 0, fun _ _ _ => rfl⟩

lemma partialS_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u + v) = partialS u + partialS v := by
  funext x
  simp only [partialS, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u + v) = partialT u + partialT v := by
  funext x
  simp only [partialT, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u - v) = partialS u - partialS v := by
  funext x
  simp only [partialS, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u - v) = partialT u - partialT v := by
  funext x
  simp only [partialT, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialS (c • u) = c • partialS u := by
  funext x
  simp only [partialS, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialT_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialT (c • u) = c • partialT u := by
  funext x
  simp only [partialT, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialS_zero : partialS (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialS]

lemma partialT_zero : partialT (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialT]

end

end CauchyRiemannIndex

-- ===== Scratch/CR746Parent.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma cr746_cylMeasure_eq_prod :
    cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

lemma cr746_int_prod {E : Type*} [NormedAddCommGroup E] (F : ℝ × ℝ → E)
    (hF : Integrable F cylMeasure) :
    Integrable F ((volume : Measure ℝ).prod (volume.restrict (Set.Ico (0 : ℝ) 1))) := by
  rwa [cr746_cylMeasure_eq_prod] at hF

lemma cr746_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ × ℝ → E)
    (hF : Integrable F cylMeasure) :
    ∫ x, F x ∂cylMeasure = ∫ t in Set.Ico (0 : ℝ) 1, ∫ σ, F (σ, t) := by
  rw [cr746_cylMeasure_eq_prod] at hF ⊢
  exact integral_prod_symm _ hF

/-- A vanishing radius for a compactly supported function and its derivative. -/
lemma cr746_vanish (ρ : ℝ → ℝ) (hρc : HasCompactSupport ρ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, R < |y| → ρ y = 0 ∧ deriv ρ y = 0 := by
  obtain ⟨R, hR⟩ := hρc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun y hy => ?_⟩
  have hU : IsOpen {y : ℝ | max R 0 < |y|} := isOpen_lt continuous_const continuous_abs
  have h0 : ∀ z, max R 0 < |z| → ρ z = 0 := by
    intro z hz
    by_contra h
    have := hR (subset_tsupport _ h)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith [le_max_left R 0]
  refine ⟨h0 y hy, ?_⟩
  have hev : ρ =ᶠ[𝓝 y] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hy) fun z hz => h0 z hz
  rw [hev.deriv_eq]; simp

/-- A continuous `1`-periodic map is bounded. -/
lemma cr746_bound_periodic {E : Type*} [NormedAddCommGroup E] (v : ℝ → E) (hv : Continuous v)
    (hp : Function.Periodic v 1) : ∃ M : ℝ, ∀ t, ‖v t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hp.compact_of_continuous one_ne_zero hv).isBounded.exists_norm_le
  exact ⟨M, fun t => hM _ ⟨t, rfl⟩⟩

/-- The product test section `u(σ, t) = ρ(s - σ) ψ(t)` and its partial derivatives. -/
lemma cr746_test (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (ψ : ℝ → Vec n)
    (hψ : ContDiff ℝ ∞ ψ) (hψp : Function.Periodic ψ 1) (s : ℝ) :
    IsTestSection (fun x : ℝ × ℝ => ρ (s - x.1) • ψ x.2) ∧
    (∀ x : ℝ × ℝ, partialS (fun x : ℝ × ℝ => ρ (s - x.1) • ψ x.2) x =
      -(deriv ρ (s - x.1) • ψ x.2)) ∧
    (∀ x : ℝ × ℝ, partialT (fun x : ℝ × ℝ => ρ (s - x.1) • ψ x.2) x =
      ρ (s - x.1) • deriv ψ x.2) := by
  obtain ⟨R, -, hR⟩ := cr746_vanish ρ hρc
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hd : ∀ x : ℝ × ℝ, HasFDerivAt (fun x : ℝ × ℝ => ρ (s - x.1) • ψ x.2)
      (ρ (s - x.1) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv ψ x.2)).comp
          (ContinuousLinearMap.snd ℝ ℝ ℝ)) +
        (deriv ρ (s - x.1) • -(ContinuousLinearMap.fst ℝ ℝ ℝ)).smulRight (ψ x.2)) x := by
    intro x
    have hc : HasFDerivAt (fun x : ℝ × ℝ => ρ (s - x.1))
        (deriv ρ (s - x.1) • -(ContinuousLinearMap.fst ℝ ℝ ℝ)) x :=
      (hρd (s - x.1)).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_fst.const_sub s)
    have hf : HasFDerivAt (fun x : ℝ × ℝ => ψ x.2)
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv ψ x.2)).comp
          (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
      (hψd x.2).hasDerivAt.hasFDerivAt.comp x hasFDerivAt_snd
    exact hc.smul hf
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (hρ.comp (contDiff_const.sub contDiff_fst)).smul (hψ.comp contDiff_snd)
  · intro s' t; simp [hψp t]
  · refine ⟨R + |s|, fun σ t hσ => ?_⟩
    have : R < |s - σ| := by
      have := abs_sub_abs_le_abs_sub σ s
      rw [abs_sub_comm] at this
      linarith
    simp [(hR _ this).1]
  · intro x
    rw [partialS, (hd x).fderiv]
    simp
  · intro x
    rw [partialT, (hd x).fderiv]
    simp

/-- A uniform `L¹` bound for `g ∈ L^q` on slabs `[a - R, a + R] × [0, 1)`. -/
lemma cr746_slab (q : ℝ≥0∞) [Fact (1 ≤ q)] (g : LpCyl n q) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, ∀ a : ℝ,
      Integrable (g : ℝ × ℝ → Vec n)
        (cylMeasure.restrict (Set.Icc (a - R) (a + R) ×ˢ (Set.univ : Set ℝ))) ∧
      ∫ x in Set.Icc (a - R) (a + R) ×ˢ (Set.univ : Set ℝ), ‖g x‖ ∂cylMeasure ≤ K := by
  have hq : 1 ≤ q := Fact.out
  set e : ℝ := 1 / (1 : ℝ≥0∞).toReal - 1 / q.toReal with he
  have hexp : 0 ≤ e := by
    rcases eq_or_ne q (⊤ : ℝ≥0∞) with h | h
    · simp [he, h]
    · have h1 : 1 ≤ q.toReal := by
        have := ENNReal.toReal_mono h hq
        simpa using this
      simp only [he, ENNReal.toReal_one, div_one, sub_nonneg]
      exact (div_le_one (by linarith)).2 h1
  set E : ℝ≥0∞ := eLpNorm g q cylMeasure * (ENNReal.ofReal (2 * R)) ^ e
  have hE : E < (⊤ : ℝ≥0∞) := ENNReal.mul_lt_top (Lp.eLpNorm_lt_top g)
    (ENNReal.rpow_lt_top_of_nonneg hexp ENNReal.ofReal_ne_top)
  refine ⟨E.toReal, fun a => ?_⟩
  set μ' := cylMeasure.restrict (Set.Icc (a - R) (a + R) ×ˢ (Set.univ : Set ℝ))
  have hμ : μ' Set.univ ≤ ENNReal.ofReal (2 * R) := by
    rw [Measure.restrict_apply_univ, cylMeasure,
      Measure.restrict_apply (measurableSet_Icc.prod MeasurableSet.univ), Set.prod_inter_prod,
      Set.inter_univ, Set.univ_inter, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
      Real.volume_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, mul_one]
    exact le_of_eq (congrArg ENNReal.ofReal (by ring))
  have h1 : eLpNorm g 1 μ' ≤ E := by
    calc eLpNorm g 1 μ' ≤ eLpNorm g q μ' * μ' Set.univ ^ e :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq (Lp.aestronglyMeasurable g).restrict
      _ ≤ E := mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self)
          (ENNReal.rpow_le_rpow hμ hexp)
  have hint : Integrable g μ' := by
    rw [← memLp_one_iff_integrable]
    exact ⟨(Lp.aestronglyMeasurable g).restrict, h1.trans_lt hE⟩
  refine ⟨hint, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hint.1, ← eLpNorm_one_eq_lintegral_enorm]
  exact ENNReal.toReal_mono hE.ne h1

/-- A bounded continuous weight in `s` supported in a slab: integrability and a bound. -/
lemma cr746_weighted (q : ℝ≥0∞) [Fact (1 ≤ q)] (g : LpCyl n q) (R K a : ℝ)
    (hg : Integrable (g : ℝ × ℝ → Vec n)
      (cylMeasure.restrict (Set.Icc (a - R) (a + R) ×ˢ (Set.univ : Set ℝ))))
    (hK : ∫ x in Set.Icc (a - R) (a + R) ×ˢ (Set.univ : Set ℝ), ‖g x‖ ∂cylMeasure ≤ K)
    (w : ℝ → ℝ) (hw : Continuous w) (Mw : ℝ) (hMw : ∀ σ, |w σ| ≤ Mw)
    (hwz : ∀ σ, σ ∉ Set.Icc (a - R) (a + R) → w σ = 0) :
    Integrable (fun x : ℝ × ℝ => w x.1 • g x) cylMeasure ∧
      ∫ x, ‖w x.1 • g x‖ ∂cylMeasure ≤ Mw * K := by
  set A := Set.Icc (a - R) (a + R) ×ˢ (Set.univ : Set ℝ)
  have hon : IntegrableOn (fun x : ℝ × ℝ => w x.1 • g x) A cylMeasure :=
    hg.bdd_smul Mw (hw.comp continuous_fst).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hMw x.1)
  have hzero : ∀ x ∉ A, w x.1 • g x = 0 := by
    intro x hx
    rw [hwz x.1 (fun h => hx ⟨h, trivial⟩), zero_smul]
  refine ⟨hon.integrable_of_forall_notMem_eq_zero hzero, ?_⟩
  have hM0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := A)
    (fun x hx => by rw [hzero x hx, norm_zero])]
  calc ∫ x in A, ‖w x.1 • g x‖ ∂cylMeasure ≤ ∫ x in A, Mw * ‖g x‖ ∂cylMeasure := by
        refine integral_mono hon.norm (hg.norm.const_mul Mw) fun x => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hMw _) (norm_nonneg _)
    _ = Mw * ∫ x in A, ‖g x‖ ∂cylMeasure := integral_const_mul _ _
    _ ≤ Mw * K := mul_le_mul_of_nonneg_left hK hM0

/-- Fubini for `∫ ⟨v(t), F(σ, t)⟩` with `v` bounded and continuous. -/
lemma cr746_fubini (F : ℝ × ℝ → Vec n) (hF : Integrable F cylMeasure) (v : ℝ → Vec n)
    (hv : Continuous v) (Mv : ℝ) (hMv : ∀ t, ‖v t‖ ≤ Mv) :
    Integrable (fun x : ℝ × ℝ => inner ℝ (v x.2) (F x)) cylMeasure ∧
    ∫ x, inner ℝ (v x.2) (F x) ∂cylMeasure =
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (v t) (∫ σ, F (σ, t)) := by
  have hI : Integrable (fun x : ℝ × ℝ => inner ℝ (v x.2) (F x)) cylMeasure := by
    refine Integrable.mono' (hF.norm.const_mul Mv)
      ((hv.comp continuous_snd).aestronglyMeasurable.inner hF.1) (ae_of_all _ fun x => ?_)
    calc ‖inner ℝ (v x.2) (F x)‖ ≤ ‖v x.2‖ * ‖F x‖ := norm_inner_le_norm _ _
      _ ≤ Mv * ‖F x‖ := mul_le_mul_of_nonneg_right (hMv _) (norm_nonneg _)
  refine ⟨hI, ?_⟩
  rw [cr746_integral_eq _ hI]
  refine integral_congr_ae ?_
  filter_upwards [(cr746_int_prod _ hF).prod_left_ae] with t ht
  exact integral_inner ht (v t)

theorem cr746_main (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (Sinf : ℝ → Mat n)
    (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) (g : LpCyl n q)
    (hg : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (g x) ∂cylMeasure = 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    ∃ C : ℝ, ∀ᵐ x ∂cylMeasure, ‖∫ σ, ρ σ • g (x.1 - σ, x.2)‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := periodic_weak_solution_bound n Sinf hS hnd
  obtain ⟨R, hR0, hR⟩ := cr746_vanish ρ hρc
  obtain ⟨K, hK⟩ := cr746_slab q g R hR0
  obtain ⟨M0, hM0⟩ := hρ.continuous.bounded_above_of_compact_support hρc
  have hdc : Continuous (deriv ρ) := hρ.continuous_deriv (by simp)
  obtain ⟨M1, hM1⟩ := hdc.bounded_above_of_compact_support hρc.deriv
  have hsupp : ∀ s σ : ℝ, σ ∉ Set.Icc (s - R) (s + R) → R < |s - σ| := by
    intro s σ h
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · rw [lt_abs]; left; linarith
    · rw [lt_abs]; right; linarith
  have hF0 : ∀ s, Integrable (fun x : ℝ × ℝ => ρ (s - x.1) • g x) cylMeasure ∧
      ∫ x, ‖ρ (s - x.1) • g x‖ ∂cylMeasure ≤ M0 * K := fun s =>
    cr746_weighted q g R K s (hK s).1 (hK s).2 (fun σ => ρ (s - σ))
      (hρ.continuous.comp (continuous_const.sub continuous_id)) M0
      (fun σ => by simpa [Real.norm_eq_abs] using hM0 (s - σ))
      (fun σ h => (hR _ (hsupp s σ h)).1)
  have hF1 : ∀ s, Integrable (fun x : ℝ × ℝ => deriv ρ (s - x.1) • g x) cylMeasure ∧
      ∫ x, ‖deriv ρ (s - x.1) • g x‖ ∂cylMeasure ≤ M1 * K := fun s =>
    cr746_weighted q g R K s (hK s).1 (hK s).2 (fun σ => deriv ρ (s - σ))
      (hdc.comp (continuous_const.sub continuous_id)) M1
      (fun σ => by simpa [Real.norm_eq_abs] using hM1 (s - σ))
      (fun σ h => (hR _ (hsupp s σ h)).2)
  -- the slice identity at every `s`
  have hslice : ∀ s, ∀ ψ : ℝ → Vec n, ContDiff ℝ ∞ ψ → Function.Periodic ψ 1 →
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
          Matrix.toEuclideanLin (Sinf t) (ψ t)) (∫ σ, ρ (s - σ) • g (σ, t)) =
        ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (∫ σ, deriv ρ (s - σ) • g (σ, t)) := by
    intro s ψ hψ hψp
    obtain ⟨hu, hpS, hpT⟩ := cr746_test ρ hρ hρc ψ hψ hψp s
    have h0 := hg _ hu
    set A : ℝ → Vec n := fun t => Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
      Matrix.toEuclideanLin (Sinf t) (ψ t) with hAdef
    have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
    have hAc : Continuous A :=
      ((continuous_matCLM.comp continuous_const).clm_apply hdψ).add
        ((continuous_matCLM.comp hS.1).clm_apply hψ.continuous)
    have hAp : Function.Periodic A 1 := by
      intro t
      have hd1 : deriv ψ (t + 1) = deriv ψ t := by
        rw [← deriv_comp_add_const]
        exact congrArg (fun f => deriv f t) (funext hψp)
      simp only [hAdef, hd1, hψp t, hS.2.1 t]
    obtain ⟨MA, hMA⟩ := cr746_bound_periodic A hAc hAp
    obtain ⟨Mψ, hMψ⟩ := cr746_bound_periodic ψ hψ.continuous hψp
    obtain ⟨i1, e1⟩ := cr746_fubini _ (hF0 s).1 A hAc MA hMA
    obtain ⟨i2, e2⟩ := cr746_fubini _ (hF1 s).1 ψ hψ.continuous Mψ hMψ
    have hpt : ∀ x : ℝ × ℝ, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2)
        (fun x : ℝ × ℝ => ρ (s - x.1) • ψ x.2) x) (g x) =
        inner ℝ (A x.2) (ρ (s - x.1) • g x) - inner ℝ (ψ x.2) (deriv ρ (s - x.1) • g x) := by
      intro x
      simp only [crOp, hpS, hpT, hAdef, map_smul, inner_add_left, inner_neg_left,
        real_inner_smul_left, real_inner_smul_right]
      ring
    simp only [hpt] at h0
    rw [integral_sub i1 i2, sub_eq_zero, e1, e2] at h0
    exact h0
  -- the bound on every slice
  have hGs : ∀ s, ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)),
      ‖∫ σ, ρ (s - σ) • g (σ, t)‖ ≤ |C₀| * (M1 * K) := by
    intro s
    have P0 := cr746_int_prod _ (hF0 s).1
    have P1 := cr746_int_prod _ (hF1 s).1
    have hη : IntegrableOn (fun t => ∫ σ, ρ (s - σ) • g (σ, t)) (Set.Ico 0 1) :=
      P0.integral_prod_right
    have hf : IntegrableOn (fun t => ∫ σ, deriv ρ (s - σ) • g (σ, t)) (Set.Ico 0 1) :=
      P1.integral_prod_right
    have hL1 : ∫ t in Set.Ico (0 : ℝ) 1, ‖∫ σ, deriv ρ (s - σ) • g (σ, t)‖ ≤ M1 * K := by
      calc ∫ t in Set.Ico (0 : ℝ) 1, ‖∫ σ, deriv ρ (s - σ) • g (σ, t)‖
          ≤ ∫ t in Set.Ico (0 : ℝ) 1, ∫ σ, ‖deriv ρ (s - σ) • g (σ, t)‖ :=
            integral_mono hf.norm P1.norm.integral_prod_right
              (fun t => norm_integral_le_integral_norm _)
        _ = ∫ x, ‖deriv ρ (s - x.1) • g x‖ ∂cylMeasure :=
            (cr746_integral_eq _ (hF1 s).1.norm).symm
        _ ≤ M1 * K := (hF1 s).2
    filter_upwards [hC₀ _ _ hη hf (hslice s)] with t ht
    calc _ ≤ C₀ * ∫ t in Set.Ico (0 : ℝ) 1, ‖∫ σ, deriv ρ (s - σ) • g (σ, t)‖ := ht
      _ ≤ |C₀| * ∫ t in Set.Ico (0 : ℝ) 1, ‖∫ σ, deriv ρ (s - σ) • g (σ, t)‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (integral_nonneg fun _ => norm_nonneg _)
      _ ≤ |C₀| * (M1 * K) := mul_le_mul_of_nonneg_left hL1 (abs_nonneg _)
  -- assemble
  refine ⟨|C₀| * (M1 * K), ?_⟩
  set G : ℝ × ℝ → Vec n := fun x => ∫ σ, ρ σ • g (x.1 - σ, x.2) with hGdef
  have hGm : StronglyMeasurable G := by
    refine StronglyMeasurable.integral_prod_right (f := fun (x : ℝ × ℝ) (σ : ℝ) => ρ σ • g (x.1 - σ, x.2)) ?_
    exact (hρ.continuous.comp continuous_snd).stronglyMeasurable.smul
      ((Lp.stronglyMeasurable g).comp_measurable
        ((measurable_fst.fst.sub measurable_snd).prodMk measurable_fst.snd))
  have hmeas : MeasurableSet {x : ℝ × ℝ | ‖G x‖ ≤ |C₀| * (M1 * K)} :=
    measurableSet_le hGm.norm.measurable measurable_const
  have hae : ae cylMeasure =
      ae ((volume : Measure ℝ).prod (volume.restrict (Set.Ico (0 : ℝ) 1))) := by
    rw [cr746_cylMeasure_eq_prod]
  show ∀ᵐ x ∂cylMeasure, ‖G x‖ ≤ |C₀| * (M1 * K)
  rw [Filter.Eventually, hae, ← Filter.Eventually, Measure.ae_prod_iff_ae_ae hmeas]
  refine ae_of_all _ fun s => ?_
  filter_upwards [hGs s] with t ht
  have hGst : G (s, t) = ∫ σ, ρ (s - σ) • g (σ, t) := by
    simp only [hGdef]
    rw [← integral_sub_left_eq_self (fun σ => ρ (s - σ) • g (σ, t)) volume s]
    simp [sub_sub_cancel]
  rw [hGst]
  exact ht

end

end CauchyRiemannIndex

open CauchyRiemannIndex MeasureTheory
open scoped ENNReal NNReal ContDiff

theorem solution (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (Sinf : ℝ → Mat n)
    (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) (g : LpCyl n q)
    (hg : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (g x) ∂cylMeasure = 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    ∃ C : ℝ, ∀ᵐ x ∂cylMeasure, ‖∫ σ, ρ σ • g (x.1 - σ, x.2)‖ ≤ C :=
  cr746_main n q Sinf hS hnd g hg ρ hρ hρc
