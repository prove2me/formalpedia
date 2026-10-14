-- Prove2me | solution 1 for DistCov.Hilbert.ext_of_finite_projections
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T18:45:21.190977+00:00
-- url     : https://prove2.me/submissions/a330b14b-35ab-4053-9c83-f69d661d19cb

import Definitions.Def_DistCov_Hilbert_Setting

set_option autoImplicit false
open MeasureTheory Filter TopologicalSpace
open scoped Topology

noncomputable section

namespace DistCovCW

abbrev H := DistCov.Indep.L2N

def e (n : ℕ) : H := lp.single 2 n (1 : ℝ)

def trunc (N : ℕ) (u : H) : H := ∑ n ∈ Finset.range N, lp.single 2 n (u n)

lemma trunc_tendsto (u : H) : Tendsto (fun N => trunc N u) atTop (𝓝 u) :=
  (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u).tendsto_sum_nat

lemma single_eq_smul (u : H) (n : ℕ) : lp.single 2 n (u n) = u n • e n := by
  simpa [e] using (lp.single_smul (E := fun _ : ℕ => ℝ) 2 n (u n) (1 : ℝ))

lemma separable_H : SeparableSpace H := by
  let S := Submodule.span ℝ (Set.range e)
  have hs : IsSeparable (closure (S : Set H)) := (Set.countable_range e).isSeparable.span.closure
  apply isSeparable_univ_iff.mp
  apply hs.mono
  intro u hu
  apply mem_closure_of_tendsto (trunc_tendsto u)
  exact Eventually.of_forall fun N => S.sum_mem fun n hn => by
    rw [single_eq_smul]
    exact S.smul_mem _ (Submodule.subset_span ⟨n, rfl⟩)

lemma continuous_scalar (v : ℕ →₀ ℝ) :
    Continuous (fun u : H => ∑ i ∈ v.support, u i * v i) := by
  apply continuous_finsetSum
  intro i hi
  exact (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 i).continuous.mul continuous_const

lemma scalar_laws (μ₁ μ₂ : Measure H) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (v : ℕ →₀ ℝ) (s : ℝ),
      μ₁ {u : H | ∑ i ∈ v.support, u i * v i ≤ s} =
      μ₂ {u : H | ∑ i ∈ v.support, u i * v i ≤ s}) (v : ℕ →₀ ℝ) :
    μ₁.map (fun u : H => ∑ i ∈ v.support, u i * v i) =
    μ₂.map (fun u : H => ∑ i ∈ v.support, u i * v i) := by
  apply Measure.ext_of_Iic
  intro s
  rw [Measure.map_apply (continuous_scalar v).measurable measurableSet_Iic,
      Measure.map_apply (continuous_scalar v).measurable measurableSet_Iic]
  exact h v s

lemma integral_scalar (μ₁ μ₂ : Measure H) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (v : ℕ →₀ ℝ) (s : ℝ),
      μ₁ {u : H | ∑ i ∈ v.support, u i * v i ≤ s} =
      μ₂ {u : H | ∑ i ∈ v.support, u i * v i ≤ s}) (v : ℕ →₀ ℝ) :
    (∫ u, Complex.exp ((∑ i ∈ v.support, u i * v i : ℝ) * Complex.I) ∂μ₁) =
    ∫ u, Complex.exp ((∑ i ∈ v.support, u i * v i : ℝ) * Complex.I) ∂μ₂ := by
  have hc : Continuous (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) := by fun_prop
  rw [← integral_map (continuous_scalar v).measurable.aemeasurable hc.aestronglyMeasurable,
      ← integral_map (continuous_scalar v).measurable.aemeasurable hc.aestronglyMeasurable,
      scalar_laws μ₁ μ₂ h v]

lemma trunc_scalar (L : StrongDual ℝ H) (N : ℕ) (u : H) :
    L (trunc N u) = ∑ i ∈ Finset.range N, u i * L (e i) := by
  simp only [trunc, map_sum, single_eq_smul, map_smul, smul_eq_mul]

lemma integral_trunc_eq (μ₁ μ₂ : Measure H) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (v : ℕ →₀ ℝ) (s : ℝ),
      μ₁ {u : H | ∑ i ∈ v.support, u i * v i ≤ s} =
      μ₂ {u : H | ∑ i ∈ v.support, u i * v i ≤ s})
    (L : StrongDual ℝ H) (N : ℕ) :
    (∫ u, Complex.exp ((L (trunc N u) : ℂ) * Complex.I) ∂μ₁) =
    ∫ u, Complex.exp ((L (trunc N u) : ℂ) * Complex.I) ∂μ₂ := by
  classical
  let v : ℕ →₀ ℝ := Finsupp.onFinset (Finset.range N)
    (fun i => if i < N then L (e i) else 0) (by
      intro i hi
      by_contra hn
      simp only [Finset.mem_range, not_lt] at hn
      simp [not_lt.mpr hn] at hi)
  have hv : ∀ u : H, (∑ i ∈ v.support, u i * v i) = L (trunc N u) := by
    intro u
    rw [trunc_scalar]
    calc
      (∑ i ∈ v.support, u i * v i) = ∑ i ∈ Finset.range N, u i * v i := by
        apply Finset.sum_subset Finsupp.support_onFinset_subset
        intro i hi hni
        have hz : v i = 0 := Finsupp.notMem_support_iff.mp hni
        rw [hz, mul_zero]
      _ = ∑ i ∈ Finset.range N, u i * L (e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [v, Finset.mem_range.mp hi]
  simpa only [hv] using integral_scalar μ₁ μ₂ h v

lemma integral_trunc_tendsto (μ : Measure H) [IsFiniteMeasure μ] (L : StrongDual ℝ H) :
    Tendsto (fun N => ∫ u, Complex.exp ((L (trunc N u) : ℂ) * Complex.I) ∂μ)
      atTop (𝓝 (∫ u, Complex.exp ((L u : ℂ) * Complex.I) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro N
    have hc : Continuous (fun u : H => L (trunc N u)) := by
      simp only [trunc_scalar]
      apply continuous_finsetSum
      intro i hi
      exact (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 i).continuous.mul continuous_const
    exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hc).mul continuous_const)).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    exact Eventually.of_forall fun u => (Complex.norm_exp_ofReal_mul_I _).le
  · exact Eventually.of_forall fun u => by
      have ht := L.continuous.continuousAt.tendsto.comp (trunc_tendsto u)
      exact ((Complex.continuous_exp.continuousAt.tendsto).comp
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp ht).mul tendsto_const_nhds))

end DistCovCW

open DistCovCW

theorem solution (μ₁ μ₂ : Measure DistCov.Indep.L2N) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂]
    (h : ∀ (v : ℕ →₀ ℝ) (s : ℝ),
      μ₁ {u : DistCov.Indep.L2N | ∑ i ∈ v.support, u i * v i ≤ s} =
      μ₂ {u : DistCov.Indep.L2N | ∑ i ∈ v.support, u i * v i ≤ s}) :
    μ₁ = μ₂ := by
  let : SeparableSpace H := separable_H
  apply Measure.ext_of_charFunDual
  funext L
  simp only [charFunDual_apply]
  apply tendsto_nhds_unique (integral_trunc_tendsto μ₁ L)
  convert integral_trunc_tendsto μ₂ L using 1
  funext N
  exact integral_trunc_eq μ₁ μ₂ h L N

#print axioms solution
