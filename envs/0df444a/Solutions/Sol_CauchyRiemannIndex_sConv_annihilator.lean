-- Prove2me | solution 1 for CauchyRiemannIndex.sConv_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T08:45:33.907108+00:00
-- url     : https://prove2.me/submissions/c58a9817-e0d5-4b49-8a92-aee13f7ec378

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Theorems.Thm_CauchyRiemannIndex_sConv_memLp

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

-- ===== Scratch/CRSConvBase.lean =====
/-!
# Convolution in `s` on the cylinder: shifts, Tonelli, measurability

`G(s, t) = ∫ ρ(σ) g(s - σ, t) dσ`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma sca_cyl_eq_prod :
    cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

instance sca_sFinite : SFinite cylMeasure := by unfold cylMeasure; infer_instance

lemma sca_mp (a : ℝ) :
    MeasurePreserving (fun x : ℝ × ℝ => (x.1 - a, x.2)) cylMeasure cylMeasure := by
  have h := (measurePreserving_sub_right (volume : Measure ℝ) a).prod
    (MeasurePreserving.id (volume.restrict (Set.Ico (0 : ℝ) 1)))
  rw [sca_cyl_eq_prod]
  convert h using 1
  funext x
  rfl

lemma sca_me (a : ℝ) : MeasurableEmbedding (fun x : ℝ × ℝ => (x.1 - a, x.2)) :=
  ((MeasurableEquiv.subRight a).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding

lemma sca_meas_shift : Measurable (fun p : (ℝ × ℝ) × ℝ => (p.1.1 - p.2, p.1.2)) := by
  fun_prop

/-- Tonelli for `s`-shifts on the cylinder. -/
lemma sca_tonelli {k : ℝ → ℝ≥0∞} (hk : Measurable k) {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, (∫⁻ σ, k σ * h (x.1 - σ, x.2)) ∂cylMeasure =
      (∫⁻ σ, k σ) * ∫⁻ x, h x ∂cylMeasure := by
  rw [lintegral_lintegral_swap ((hk.comp measurable_snd).mul (hh.comp sca_meas_shift)).aemeasurable]
  have h1 : ∀ σ : ℝ, ∫⁻ x, k σ * h (x.1 - σ, x.2) ∂cylMeasure = k σ * ∫⁻ x, h x ∂cylMeasure := by
    intro σ
    rw [lintegral_const_mul (k σ) (f := fun x : ℝ × ℝ => h (x.1 - σ, x.2))
      (hh.comp ((measurable_fst.sub_const σ).prodMk measurable_snd))]
    congr 1
    exact (sca_mp σ).lintegral_comp hh
  simp_rw [h1]
  rw [lintegral_mul_const _ hk]

lemma sca_sm {g : ℝ × ℝ → Vec n} (hg : StronglyMeasurable g) {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    StronglyMeasurable (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) := by
  have : StronglyMeasurable
      (Function.uncurry fun (x : ℝ × ℝ) (σ : ℝ) => ρ σ • g (x.1 - σ, x.2)) :=
    (hρ.measurable.comp measurable_snd).stronglyMeasurable.smul (hg.comp_measurable sca_meas_shift)
  exact this.integral_prod_right

lemma sca_enorm_le (g : ℝ × ℝ → Vec n) (ρ : ℝ → ℝ) (x : ℝ × ℝ) :
    ‖∫ σ, ρ σ • g (x.1 - σ, x.2)‖ₑ ≤ ∫⁻ σ, ‖ρ σ‖ₑ * ‖g (x.1 - σ, x.2)‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1
  funext σ
  rw [enorm_smul]

end

end CauchyRiemannIndex

-- ===== Scratch/CRSConvAnn.lean =====
/-!
# `G = ρ *ₛ g` is again an annihilator of `D = ∂ₛ + J₀ ∂ₜ + S∞(t)` on test sections

Fubini in `(x, σ)`, then for each `σ` the change of variables `s ↦ s - σ`: since `S∞` does not
depend on `s`, `D` commutes with `s`-shifts, and shifted test sections are test sections.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma sca_shift_isTestSection (a : ℝ) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    IsTestSection (fun x : ℝ × ℝ => u (x + (a, 0))) := by
  obtain ⟨R, hR⟩ := hu.2.2
  refine ⟨hu.1.comp (contDiff_id.add contDiff_const), ?_, R + |a|, ?_⟩
  · intro s t
    simp only [Prod.mk_add_mk, add_zero]
    exact hu.2.1 (s + a) t
  · intro s t hs
    simp only [Prod.mk_add_mk, add_zero]
    apply hR
    have h1 := abs_add_le (s + a) (-a)
    rw [abs_neg, add_neg_cancel_right] at h1
    linarith

lemma sca_shift_partialS (a : ℝ) (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    partialS (fun x : ℝ × ℝ => u (x + (a, 0))) x = partialS u (x + (a, 0)) := by
  simp only [partialS]
  rw [fderiv_comp_add_right]

lemma sca_shift_partialT (a : ℝ) (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    partialT (fun x : ℝ × ℝ => u (x + (a, 0))) x = partialT u (x + (a, 0)) := by
  simp only [partialT]
  rw [fderiv_comp_add_right]

lemma sca_shift_crOp (a : ℝ) (Sinf : ℝ → Mat n) (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    crOp (fun x : ℝ × ℝ => Sinf x.2) (fun x : ℝ × ℝ => u (x + (a, 0))) x =
      crOp (fun x : ℝ × ℝ => Sinf x.2) u (x + (a, 0)) := by
  simp only [crOp, sca_shift_partialS, sca_shift_partialT, Prod.snd_add, add_zero]

lemma sca_continuous_crOp (Sinf : ℝ → Mat n) (hc : Continuous Sinf) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) : Continuous (crOp (fun x : ℝ × ℝ => Sinf x.2) u) :=
  (hu.continuous_partialS.add ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT)).add
    ((continuous_matCLM.comp (hc.comp continuous_snd)).clm_apply hu.continuous)

lemma sca_enorm_inner_le (a b : Vec n) : ‖inner ℝ a b‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm a b)

lemma sca_ae_strip : ∀ᵐ x ∂cylMeasure, x.2 ∈ Set.Ico (0 : ℝ) 1 := by
  unfold cylMeasure
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx
  exact hx.2

/-- Integrability on `cylMeasure × dσ` from a shifted product bound. -/
lemma sca_integrable_of_bound {E : Type*} [NormedAddCommGroup E] {Ξ : (ℝ × ℝ) × ℝ → E}
    (hΞ : AEStronglyMeasurable Ξ (cylMeasure.prod volume)) {k : ℝ → ℝ≥0∞} (hk : Measurable k)
    {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h)
    (hb : ∀ x : ℝ × ℝ, x.2 ∈ Set.Ico (0 : ℝ) 1 → ∀ σ, ‖Ξ (x, σ)‖ₑ ≤ k σ * h (x.1 - σ, x.2))
    (hfin : (∫⁻ σ, k σ) * ∫⁻ x, h x ∂cylMeasure < ⊤) :
    Integrable Ξ (cylMeasure.prod volume) := by
  refine ⟨hΞ, ?_⟩
  show ∫⁻ p, ‖Ξ p‖ₑ ∂(cylMeasure.prod volume) < ⊤
  rw [lintegral_prod _ hΞ.enorm]
  refine lt_of_le_of_lt ?_ hfin
  rw [← sca_tonelli hk hh]
  refine lintegral_mono_ae ?_
  filter_upwards [sca_ae_strip] with x hx
  exact lintegral_mono fun σ => hb x hx σ

theorem sca_annihilator (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (Sinf : ℝ → Mat n)
    (hc : Continuous Sinf) (g : LpCyl n q)
    (hg : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (g x) ∂cylMeasure = 0)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (u : ℝ × ℝ → Vec n) (hu : IsTestSection u) :
    ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x)
      (∫ σ, ρ σ • g (x.1 - σ, x.2)) ∂cylMeasure = 0 := by
  have hq1 : 1 ≤ q := Fact.out
  have hgs : StronglyMeasurable (g : ℝ × ℝ → Vec n) := Lp.stronglyMeasurable g
  set F := crOp (fun x : ℝ × ℝ => Sinf x.2) u with hFdef
  have hFc : Continuous F := sca_continuous_crOp Sinf hc hu
  obtain ⟨R, hR⟩ := hu.2.2
  have hF0 : ∀ x : ℝ × ℝ, R < |x.1| → F x = 0 := by
    rintro ⟨s, t⟩ hx
    simp only [hFdef, crOp, partialS_eq_zero R hR hx, partialT_eq_zero R hR hx, hR s t hx,
      map_zero, add_zero]
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ σ, a < |σ| → ρ σ = 0 := by
    obtain ⟨a, ha⟩ := hρc.isCompact.isBounded.exists_norm_le
    refine ⟨a, fun σ hσ => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
    have := ha σ hm
    rw [Real.norm_eq_abs] at this
    linarith
  set K' : Set (ℝ × ℝ) := Set.Icc (-(R + a)) (R + a) ×ˢ Set.univ with hK'
  have hK'm : MeasurableSet K' := measurableSet_Icc.prod MeasurableSet.univ
  set h : ℝ × ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal M * K'.indicator (fun y => ‖g y‖ₑ) y with hhdef
  have hhm : Measurable h := measurable_const.mul (hgs.measurable.enorm.indicator hK'm)
  have hρm : Measurable fun σ => ‖ρ σ‖ₑ := hρ.measurable.enorm
  -- finiteness of the bound
  have hfin : (∫⁻ σ, ‖ρ σ‖ₑ) * ∫⁻ x, h x ∂cylMeasure < ⊤ := by
    have hρi : Integrable ρ := hρ.integrable_of_hasCompactSupport hρc
    have hK'f : cylMeasure K' ≠ ⊤ := by
      rw [sca_cyl_eq_prod, hK', Measure.prod_prod]
      exact ENNReal.mul_ne_top (by simp) (by simp)
    haveI : IsFiniteMeasure (cylMeasure.restrict K') := isFiniteMeasure_restrict.2 hK'f
    have hgi : ∫⁻ y in K', ‖g y‖ₑ ∂cylMeasure < ⊤ :=
      (((Lp.memLp g).restrict K').integrable hq1).2
    rw [hhdef, lintegral_const_mul _ (hgs.measurable.enorm.indicator hK'm),
      lintegral_indicator hK'm]
    exact ENNReal.mul_lt_top hρi.2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgi)
  -- the pointwise bound
  have hbd : ∀ x : ℝ × ℝ, x.2 ∈ Set.Ico (0 : ℝ) 1 → ∀ σ,
      ‖F x‖ₑ * (‖ρ σ‖ₑ * ‖g (x.1 - σ, x.2)‖ₑ) ≤ ‖ρ σ‖ₑ * h (x.1 - σ, x.2) := by
    intro x hx σ
    by_cases hxR : R < |x.1|
    · rw [hF0 x hxR]; simp
    by_cases hσ : a < |σ|
    · rw [ha σ hσ]; simp
    push_neg at hxR hσ
    have hd : |x.1 - σ| ≤ R + a := (abs_sub _ _).trans (add_le_add hxR hσ)
    have hmem : (x.1 - σ, x.2) ∈ K' :=
      ⟨⟨(abs_le.1 hd).1, (abs_le.1 hd).2⟩, Set.mem_univ _⟩
    have hFx : ‖F x‖ₑ ≤ ENNReal.ofReal M := by
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal
        (hM x ⟨⟨(abs_le.1 hxR).1, (abs_le.1 hxR).2⟩, ⟨hx.1, hx.2.le⟩⟩)
    simp only [hhdef, Set.indicator_of_mem hmem]
    calc ‖F x‖ₑ * (‖ρ σ‖ₑ * ‖g (x.1 - σ, x.2)‖ₑ)
        ≤ ENNReal.ofReal M * (‖ρ σ‖ₑ * ‖g (x.1 - σ, x.2)‖ₑ) := by gcongr
      _ = ‖ρ σ‖ₑ * (ENNReal.ofReal M * ‖g (x.1 - σ, x.2)‖ₑ) := by ring
  -- integrability on the product
  have hgsh : StronglyMeasurable fun p : (ℝ × ℝ) × ℝ => g (p.1.1 - p.2, p.1.2) :=
    hgs.comp_measurable sca_meas_shift
  have hρs : StronglyMeasurable fun p : (ℝ × ℝ) × ℝ => ρ p.2 :=
    (hρ.comp continuous_snd).stronglyMeasurable
  have hΘi : Integrable (fun p : (ℝ × ℝ) × ℝ => ‖F p.1‖ • (ρ p.2 • g (p.1.1 - p.2, p.1.2)))
      (cylMeasure.prod volume) := by
    refine sca_integrable_of_bound
      ((hFc.norm.comp continuous_fst).stronglyMeasurable.smul (hρs.smul hgsh)).aestronglyMeasurable
      hρm hhm (fun x hx σ => ?_) hfin
    simp only [enorm_smul, enorm_norm]
    exact hbd x hx σ
  have hΦi : Integrable (fun p : (ℝ × ℝ) × ℝ => inner ℝ (F p.1) (ρ p.2 • g (p.1.1 - p.2, p.1.2)))
      (cylMeasure.prod volume) := by
    refine sca_integrable_of_bound
      (StronglyMeasurable.inner (hFc.comp continuous_fst).stronglyMeasurable
        (hρs.smul hgsh)).aestronglyMeasurable
      hρm hhm (fun x hx σ => ?_) hfin
    refine (sca_enorm_inner_le _ _).trans ?_
    rw [enorm_smul]
    exact hbd x hx σ
  -- step 1: move the inner product inside the σ-integral
  have step1 : ∫ x, inner ℝ (F x) (∫ σ, ρ σ • g (x.1 - σ, x.2)) ∂cylMeasure =
      ∫ x, (∫ σ, inner ℝ (F x) (ρ σ • g (x.1 - σ, x.2))) ∂cylMeasure := by
    refine integral_congr_ae ?_
    filter_upwards [hΘi.prod_right_ae] with x hx
    by_cases hF : F x = 0
    · simp [hF]
    have hint : Integrable (fun σ => ρ σ • g (x.1 - σ, x.2)) := by
      have hfun : (fun σ => ρ σ • g (x.1 - σ, x.2)) =
          fun σ => ‖F x‖⁻¹ • (‖F x‖ • (ρ σ • g (x.1 - σ, x.2))) := by
        funext σ
        rw [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hF), one_smul]
      rw [hfun]
      exact hx.smul (‖F x‖⁻¹)
    exact (integral_inner hint (F x)).symm
  rw [step1, integral_integral_swap hΦi]
  have hz : ∀ σ : ℝ, ∫ x, inner ℝ (F x) (ρ σ • g (x.1 - σ, x.2)) ∂cylMeasure = 0 := by
    intro σ
    simp_rw [real_inner_smul_right]
    rw [integral_const_mul]
    have e1 := (sca_mp σ).integral_comp (sca_me σ)
      (fun y : ℝ × ℝ => inner ℝ (F (y + (σ, 0))) (g y))
    simp only [Prod.mk_add_mk, sub_add_cancel, add_zero, Prod.mk.eta] at e1
    rw [e1]
    have e2 : ∀ y : ℝ × ℝ, F (y + (σ, 0)) =
        crOp (fun x : ℝ × ℝ => Sinf x.2) (fun x : ℝ × ℝ => u (x + (σ, 0))) y :=
      fun y => (sca_shift_crOp σ Sinf u y).symm
    simp_rw [e2]
    rw [hg _ (sca_shift_isTestSection σ hu), mul_zero]
  simp only [hz, integral_zero]

end

end CauchyRiemannIndex

-- ===== Scratch/CRSConvParent.lean =====
open MeasureTheory CauchyRiemannIndex
open scoped ENNReal ContDiff

theorem solution (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (Sinf : ℝ → Mat n)
    (hc : Continuous Sinf) (g : LpCyl n q)
    (hg : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (g x) ∂cylMeasure = 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    MemLp (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) q cylMeasure ∧
      ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
        ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x)
          (∫ σ, ρ σ • g (x.1 - σ, x.2)) ∂cylMeasure = 0 :=
  ⟨sConv_memLp n q g ρ hρ.continuous (hρ.continuous.integrable_of_hasCompactSupport hρc),
    fun u hu => sca_annihilator n q Sinf hc g hg ρ hρ.continuous hρc u hu⟩
