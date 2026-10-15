-- Prove2me | solution 1 for CauchyRiemannIndex.eq_zero_of_sConv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T19:31:15.294854+00:00
-- url     : https://prove2.me/submissions/5c2d485d-17c1-4a09-9fe1-57f4d2456820

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Prod

-- ===== Scratch/CRSConvZero.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

noncomputable section

theorem eq_zero_of_sConv_eq_zero_aux (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (g : LpCyl n q)
    (h : ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) =ᵐ[cylMeasure] 0) :
    g = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hsm := Lp.stronglyMeasurable g
  have hmem := Lp.memLp g
  generalize (⇑g : ℝ × ℝ → Vec n) = f at hsm hmem h ⊢
  set ν : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1) with hν
  have hμ : cylMeasure = (volume : Measure ℝ).prod ν := by
    rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  -- bump functions
  let ψ : ℕ → ContDiffBump (0 : ℝ) := fun k =>
    { rIn := 1 / ((k : ℝ) + 2)
      rOut := 2 / ((k : ℝ) + 2)
      rIn_pos := by positivity
      rIn_lt_rOut := by gcongr; norm_num }
  have hψ : Tendsto (fun k => (ψ k).rOut) atTop (𝓝 0) := by
    simp only [ψ]
    have : Tendsto (fun k : ℕ => ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using this.const_div_atTop 2
  have hψK : ∀ᶠ k in atTop, (ψ k).rOut ≤ 2 * (ψ k).rIn :=
    Eventually.of_forall fun k => by simp only [ψ]; rw [mul_one_div]
  -- the hypothesis, slice-wise
  have hG : ∀ᵐ t ∂ν, ∀ k, ∀ᵐ s ∂(volume : Measure ℝ),
      ∫ σ, (ψ k).normed volume σ • f (s - σ, t) = 0 := by
    rw [ae_all_iff]
    intro k
    have h1 := h ((ψ k).normed volume) (ψ k).contDiff_normed (ψ k).hasCompactSupport_normed
    rw [hμ] at h1
    have h2 := (Measure.measurePreserving_swap (μ := ν) (ν := (volume : Measure ℝ))
      ).quasiMeasurePreserving.ae h1
    exact Measure.ae_ae_of_ae_prod h2
  -- slices are locally integrable
  have hloc : ∀ᵐ t ∂ν, LocallyIntegrable (fun s => f (s, t)) volume := by
    have hR : ∀ R : ℕ, ∀ᵐ t ∂ν,
        IntegrableOn (fun s => f (s, t)) (Set.Icc (-(R : ℝ)) R) volume := by
      intro R
      have hm : MemLp f q ((volume.restrict (Set.Icc (-(R : ℝ)) R)).prod ν) := by
        have := hmem.restrict (Set.Icc (-(R : ℝ)) R ×ˢ Set.univ)
        rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ] at this
        exact this
      haveI : IsFiniteMeasure (volume.restrict (Set.Icc (-(R : ℝ)) R)) := by
        rw [isFiniteMeasure_restrict]; exact measure_Icc_lt_top.ne
      haveI : IsFiniteMeasure ν := by
        rw [hν, isFiniteMeasure_restrict]; exact measure_Ico_lt_top.ne
      exact (hm.integrable (Fact.out)).prod_left_ae
    rw [← ae_all_iff] at hR
    filter_upwards [hR] with t ht
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨R, hRK⟩ : ∃ R : ℕ, K ⊆ Set.Icc (-(R : ℝ)) R := by
      obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
      obtain ⟨R, hR⟩ := exists_nat_ge r
      refine ⟨R, fun x hx => ?_⟩
      have := hr hx
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      exact abs_le.mp (this.trans hR)
    exact (ht R).mono_set hRK
  -- conclude on each slice
  have hslice : ∀ᵐ t ∂ν, ∀ᵐ s ∂(volume : Measure ℝ), f (s, t) = 0 := by
    filter_upwards [hG, hloc] with t hGt hlt
    have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (volume : Measure ℝ)) hψ hψK hlt
    rw [← ae_all_iff] at hGt
    filter_upwards [hconv, hGt] with s hs hs0
    have : (fun k => ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun s => f (s, t))) s) = fun _ => 0 := by
      funext k
      rw [convolution_def]
      simpa using hs0 k
    rw [this] at hs
    exact (tendsto_nhds_unique hs tendsto_const_nhds)
  -- back to the product
  have hmeas : MeasurableSet {x : ℝ × ℝ | f x = 0} :=
    hsm.measurable (measurableSet_singleton 0)
  have hmeas' : MeasurableSet {x : ℝ × ℝ | (fun s t => f (s, t) = 0) x.1 x.2} := hmeas
  rw [← Measure.ae_ae_comm hmeas', ← Measure.ae_prod_iff_ae_ae hmeas, ← hμ] at hslice
  exact hslice

end

end CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal NNReal ContDiff

theorem solution (n : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] (g : CauchyRiemannIndex.LpCyl n q)
    (h : ∀ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) =ᵐ[CauchyRiemannIndex.cylMeasure] 0) :
    g = 0 :=
  CauchyRiemannIndex.eq_zero_of_sConv_eq_zero_aux n q g h
