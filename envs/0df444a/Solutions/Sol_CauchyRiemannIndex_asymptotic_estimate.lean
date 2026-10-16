-- Prove2me | solution 1 for CauchyRiemannIndex.asymptotic_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T17:40:30.979311+00:00
-- url     : https://prove2.me/submissions/41b6045d-7cc6-4b86-b0bf-cf230b4c6644

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_estimate
import Mathlib.Data.Matrix.Basis

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

-- ===== Scratch/CR49.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- An entrywise bound on a matrix gives an operator bound on `ℝ²ⁿ`. -/
lemma cr49_entry_bound (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : Mat n) (ε : ℝ),
    (∀ i j, |A i j| ≤ ε) → ∀ v : Vec n, ‖Matrix.toEuclideanLin A v‖ ≤ ε * K * ‖v‖ := by
  refine ⟨∑ i, ∑ j, ‖matCLM n (Matrix.single i j 1)‖,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
  intro A ε hA v
  have hdec : matCLM n A = ∑ i, ∑ j, A i j • matCLM n (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single A]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hop : ‖matCLM n A‖ ≤ ε * ∑ i, ∑ j, ‖matCLM n (Matrix.single i j 1)‖ := by
    rw [hdec, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
  rw [← matCLM_apply]
  exact ((matCLM n A).le_opNorm v).trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Absorbing a small perturbation of a translation-invariant estimate. -/
lemma cr49_absorb (S : ℝ × ℝ → Mat n) (hSc : Continuous S) (Sinf : ℝ → Mat n)
    (hSinf : Continuous Sinf) (c0 δ : ℝ≥0) (hδ : (c0 : ℝ≥0∞) * δ ≤ 2⁻¹)
    (u : ℝ × ℝ → Vec n) (hu : IsTestSection u)
    (hest : w1pNorm p u ≤ c0 * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure)
    (hpt : ∀ x, ‖Matrix.toEuclideanLin (S x - Sinf x.2) (u x)‖ ≤ δ * ‖u x‖) :
    w1pNorm p u ≤ ((2 * c0 : ℝ≥0) : ℝ≥0∞) * eLpNorm (crOp S u) p cylMeasure := by
  set E : ℝ × ℝ → Vec n := fun x => Matrix.toEuclideanLin (S x - Sinf x.2) (u x) with hE
  have hEc : Continuous E := by
    have : Continuous fun x : ℝ × ℝ => matCLM n (S x - Sinf x.2) :=
      continuous_matCLM.comp (hSc.sub (hSinf.comp continuous_snd))
    exact this.clm_apply hu.continuous
  have hDc : Continuous (crOp S u) := by
    have : Continuous fun x : ℝ × ℝ => matCLM n (S x) := continuous_matCLM.comp hSc
    exact (hu.continuous_partialS.add
      ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT)).add
      (this.clm_apply hu.continuous)
  have hsplit : crOp (fun x : ℝ × ℝ => Sinf x.2) u = crOp S u - E := by
    funext x
    simp only [crOp, hE, Pi.sub_apply, map_sub, LinearMap.sub_apply]
    abel
  have hEb : eLpNorm E p cylMeasure ≤ δ * eLpNorm u p cylMeasure := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (Eventually.of_forall fun x => ?_) p
    have h := hpt x
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul δ.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal h
  have hW : w1pNorm p u ≠ ⊤ := by
    unfold w1pNorm
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hu.memLp.eLpNorm_ne_top,
      hu.memLp_partialS.eLpNorm_ne_top⟩, hu.memLp_partialT.eLpNorm_ne_top⟩
  have huW : eLpNorm u p cylMeasure ≤ w1pNorm p u := by
    unfold w1pNorm
    exact le_add_right (le_add_right le_rfl)
  set W := w1pNorm p u
  set a := eLpNorm (crOp S u) p cylMeasure
  have h1 : W ≤ c0 * a + W / 2 := by
    calc W ≤ c0 * (a + δ * W) := by
          refine hest.trans ?_
          gcongr
          rw [hsplit]
          refine (eLpNorm_sub_le hDc.aestronglyMeasurable hEc.aestronglyMeasurable
            Fact.out).trans (add_le_add le_rfl (hEb.trans (by gcongr)))
      _ = c0 * a + (c0 * δ) * W := by rw [mul_add, mul_assoc]
      _ ≤ c0 * a + 2⁻¹ * W := add_le_add le_rfl (by gcongr)
      _ = c0 * a + W / 2 := by rw [ENNReal.div_eq_inv_mul]
  have hhalf : W / 2 ≠ ⊤ := ENNReal.div_ne_top hW two_ne_zero
  have h2 : W / 2 ≤ c0 * a := by
    refine ENNReal.le_of_add_le_add_right hhalf ?_
    rw [ENNReal.add_halves]
    exact h1
  calc W = 2 * (W / 2) := by rw [two_mul, ENNReal.add_halves]
    _ ≤ 2 * (c0 * a) := by gcongr
    _ = ((2 * c0 : ℝ≥0) : ℝ≥0∞) * a := by push_cast; ring

/-- A choice of `δ > 0` with `c0 δ ≤ 1/2`. -/
lemma cr49_delta (c0 : ℝ≥0) : ∃ δ : ℝ≥0, 0 < δ ∧ (c0 : ℝ≥0∞) * δ ≤ 2⁻¹ := by
  refine ⟨(2 * (c0 + 1))⁻¹, by positivity, ?_⟩
  have h : c0 * (2 * (c0 + 1))⁻¹ ≤ (2 : ℝ≥0)⁻¹ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [mul_inv, ← mul_assoc, mul_comm (c0 : ℝ), mul_assoc]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [mul_inv_le_iff₀ (by positivity)]
    linarith
  have := (ENNReal.coe_le_coe.2 h)
  rw [ENNReal.coe_mul, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat] at this
  exact this

/-- One end: the estimate for test sections supported where `S` is `δ`-close to `Sinf`. -/
lemma cr49_end (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (S : ℝ × ℝ → Mat n) (hSc : Continuous S) (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) (P : ℝ → Prop)
    (hclose : ∀ ε > 0, ∃ R : ℝ, ∀ s t, P (s - R) → ∀ i j, |S (s, t) i j - Sinf t i j| ≤ ε) :
    ∃ (R : ℝ) (c : ℝ≥0), ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      (∀ s t, ¬ P (s - R) → u (s, t) = 0) →
        w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure := by
  obtain ⟨c0, hc0⟩ := translationInvariant_estimate n p hp hp' Sinf hSinf hnd
  obtain ⟨K, hK0, hK⟩ := cr49_entry_bound n
  obtain ⟨δ, hδ0, hδ⟩ := cr49_delta c0
  obtain ⟨R, hR⟩ := hclose ((δ : ℝ) / (K + 1)) (by positivity)
  refine ⟨R, 2 * c0, fun u hu hvan => cr49_absorb S hSc Sinf hSinf.1 c0 δ hδ u hu (hc0 u hu) ?_⟩
  rintro ⟨s, t⟩
  by_cases hs : P (s - R)
  · refine (hK (S (s, t) - Sinf t) ((δ : ℝ) / (K + 1)) (fun i j => ?_) (u (s, t))).trans ?_
    · exact hR s t hs i j
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [δ.coe_nonneg]
  · simp [hvan s t hs]

end

end CauchyRiemannIndex

open CauchyRiemannIndex MeasureTheory
open scoped ENNReal NNReal

theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) :
    (IsNondegenerate Splus → ∃ (R : ℝ) (c : ℝ≥0), ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      (∀ s t, s ≤ R → u (s, t) = 0) → w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure) ∧
    (IsNondegenerate Sminus → ∃ (R : ℝ) (c : ℝ≥0), ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      (∀ s t, -R ≤ s → u (s, t) = 0) → w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure) := by
  refine ⟨fun hnd => ?_, fun hnd => ?_⟩
  · obtain ⟨R, c, h⟩ := cr49_end n p hp hp' S hS.1 Splus hSplus hnd (fun x => 0 ≤ x)
      (fun ε hε => by
        obtain ⟨R, hR⟩ := hS.2.2 ε hε
        exact ⟨R, fun s t hs i j => (hR s t i j).1 (by linarith)⟩)
    exact ⟨R, c, fun u hu hv => h u hu fun s t hs => hv s t (by push_neg at hs; linarith)⟩
  · obtain ⟨R, c, h⟩ := cr49_end n p hp hp' S hS.1 Sminus hSminus hnd (fun x => x ≤ 0)
      (fun ε hε => by
        obtain ⟨R, hR⟩ := hS.2.2 ε hε
        exact ⟨-R, fun s t hs i j => (hR s t i j).2 (by linarith)⟩)
    exact ⟨-R, c, fun u hu hv => h u hu fun s t hs => hv s t (by push_neg at hs; linarith)⟩
