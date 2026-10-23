-- Prove2me | solution 1 for CorrelatedTrials.Consistency.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T06:16:13.723459+00:00
-- url     : https://prove2.me/submissions/319ea641-1038-4cf3-b489-6695ad44c8ea

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess
import Theorems.Thm_CorrelatedTrials_Consistency_lemma_EC_4
import Theorems.Thm_CorrelatedTrials_Consistency_lemma_EC_5
import Theorems.Thm_CorrelatedTrials_Consistency_posterior_mean_consistency

open MeasureTheory ProbabilityTheory Filter Topology

namespace CorrelatedTrials.Consistency.Thm1Aux

/-- Under `θ ∼ N(µ0, Σ0)` with `Σ0 ≻ 0`, two distinct coordinates of `θ` differ almost surely. -/
lemma theta_ne_ae {M : ℕ} (I : Instance M) {i j : Fin M} (hij : i ≠ j) :
    ∀ᵐ ω ∂(trialMeasure I), theta ω i ≠ theta ω j := by
  classical
  set μ := multivariateGaussian (WithLp.toLp 2 I.mu0) I.Sig0 with hμ
  set v : EuclideanSpace ℝ (Fin M) := EuclideanSpace.single i 1 - EuclideanSpace.single j 1
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin M)) := innerSL ℝ v
  have hL : ∀ x : EuclideanSpace ℝ (Fin M), L x = x i - x j := by
    intro x; simp [L, v, EuclideanSpace.inner_single_left]
  have hvar : Var[L; μ] ≠ 0 := by
    have h1 : Var[L; μ] = covarianceBilin μ v v := by
      rw [covarianceBilin_self IsGaussian.memLp_two_id]; rfl
    rw [h1, covarianceBilin_multivariateGaussian I.posDef.posSemidef]
    have hv : (v : Fin M → ℝ) ≠ 0 := by
      intro h; have := congrFun h i; simp [v, hij] at this
    exact (I.posDef.dotProduct_mulVec_pos hv).ne'
  have hmap := IsGaussian.map_eq_gaussianReal (μ := μ) L
  have hnull : μ {x | x i = x j} = 0 := by
    have : {x : EuclideanSpace ℝ (Fin M) | x i = x j} = L ⁻¹' {0} := by
      ext x; simp [hL, sub_eq_zero]
    rw [this, ← Measure.map_apply L.continuous.measurable (measurableSet_singleton 0), hmap]
    have := nullSingletonClass_gaussianReal (μ := μ[L]) (v := (Var[L; μ]).toNNReal)
      (by simpa [Real.toNNReal_eq_zero, not_le] using
        (lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hvar)))
    exact measure_singleton 0
  have hfst : (trialMeasure I).map Prod.fst = μ := by
    simp [trialMeasure, hμ]
  rw [ae_iff]
  have : {ω : TrialSpace M | ¬ theta ω i ≠ theta ω j} = Prod.fst ⁻¹' {x | x i = x j} := by
    ext ω; simp [theta]
  rw [this, ← Measure.map_apply measurable_fst, hfst, hnull]
  exact measurableSet_eq_fun (by fun_prop) (by fun_prop)

/-- The least-index argmax is an argmax. -/
lemma le_leastArgmax {M : ℕ} (hM : 0 < M) (g : Fin M → ℝ) (j : Fin M) :
    g j ≤ g (leastArgmax hM g) := by
  unfold leastArgmax
  have h := Finset.min'_mem (Finset.univ.filter fun i => ∀ j, g j ≤ g i) (by
    obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ g
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hM⟩⟩)
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hk j (Finset.mem_univ _)⟩⟩)
  exact (Finset.mem_filter.1 h).2 j

/-- The cPDE policy samples an arm whose index is maximal. -/
lemma nuStar_le_alloc {M : ℕ} (I : Instance M) (t : ℕ) (ω : TrialSpace M) (j : Fin M) :
    nuStar I.lam I.c (mu I t ω) (Sig I t ω) j ≤
      nuStar I.lam I.c (mu I t ω) (Sig I t ω) (alloc I t ω) :=
  le_leastArgmax (by have := I.two_le; omega) (fun i => nuStar I.lam I.c (cpdeState I t ω).1 (cpdeState I t ω).2.1 i) j

/-- Pathwise step of the proof of Theorem 1 (XFC's argument): if every arm sampled infinitely
often has index tending to `−1`, then every index is eventually below `−1 + ε`. -/
lemma eventually_nuStar_lt {M : ℕ} (I : Instance M) (ω : TrialSpace M)
    (h4 : ∀ a, (∃ᶠ t in atTop, alloc I t ω = a) →
      Tendsto (fun T => nuStar I.lam I.c (mu I T ω) (Sig I T ω) a) atTop (𝓝 (-1)))
    (i : Fin M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T in atTop, nuStar I.lam I.c (mu I T ω) (Sig I T ω) i < -1 + ε := by
  have hA : ∀ᶠ t in atTop, ∀ a, ¬ (∃ᶠ s in atTop, alloc I s ω = a) → alloc I t ω ≠ a := by
    rw [eventually_all]
    intro a
    by_cases ha : ∃ᶠ s in atTop, alloc I s ω = a
    · exact Eventually.of_forall fun t h => absurd ha h
    · have : ∀ᶠ s in atTop, alloc I s ω ≠ a := by
        simpa [Filter.Frequently] using ha
      exact this.mono fun t ht _ => ht
  have hB : ∀ᶠ t in atTop, ∀ a, (∃ᶠ s in atTop, alloc I s ω = a) →
      nuStar I.lam I.c (mu I t ω) (Sig I t ω) a < -1 + ε := by
    rw [eventually_all]
    intro a
    by_cases ha : ∃ᶠ s in atTop, alloc I s ω = a
    · exact ((h4 a ha).eventually (gt_mem_nhds (by linarith))).mono fun t ht _ => ht
    · exact Eventually.of_forall fun t h => absurd h ha
  filter_upwards [hA, hB] with t hAt hBt
  have hfreq : ∃ᶠ s in atTop, alloc I s ω = alloc I t ω := by
    by_contra hc
    exact hAt _ hc rfl
  exact lt_of_le_of_lt (nuStar_le_alloc I t ω i) (hBt _ hfreq)

end CorrelatedTrials.Consistency.Thm1Aux

open CorrelatedTrials.Consistency CorrelatedTrials.Consistency.Thm1Aux in
theorem solution {M : ℕ} (I : Instance M) :
    (∀ i, ∀ᵐ ω ∂(trialMeasure I), Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0)) ∧
      (∀ i, ∀ᵐ ω ∂(trialMeasure I),
        Tendsto (fun T => nuStar I.lam I.c (mu I T ω) (Sig I T ω) i) atTop (𝓝 (-1))) ∧
      (∀ i, (∀ᵐ ω ∂(trialMeasure I), Tendsto (fun T => mu I T ω i) atTop (𝓝 (theta ω i))) ∧
        (∀ T, MemLp (fun ω => mu I T ω i - theta ω i) 2 (trialMeasure I)) ∧
        Tendsto (fun T => eLpNorm (fun ω => mu I T ω i - theta ω i) 2 (trialMeasure I))
          atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂(trialMeasure I), ∃ i, (∀ j, j ≠ i → theta ω j < theta ω i) ∧
        ∀ᶠ T in atTop, ∀ j, j ≠ i → mu I T ω j < mu I T ω i) := by
  -- Part i): all posterior variances vanish, almost surely.
  have hSig : ∀ᵐ ω ∂(trialMeasure I), ∀ i, Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) := by
    filter_upwards [lemma_EC_5 I] with ω h5
    apply h5
    intro i ε hε
    have h4 : ∀ a, (∃ᶠ t in atTop, alloc I t ω = a) →
        Tendsto (fun T => nuStar I.lam I.c (mu I T ω) (Sig I T ω) a) atTop (𝓝 (-1)) :=
      fun a ha => (lemma_EC_4 I).2 ω a ((lemma_EC_4 I).1 ω a ha)
    exact (eventually_nuStar_lt I ω h4 i ε hε).frequently
  have h1 : ∀ i, ∀ᵐ ω ∂(trialMeasure I), Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) :=
    fun i => hSig.mono fun ω h => h i
  have h3 := fun i => posterior_mean_consistency I i (h1 i)
  refine ⟨h1, fun i => (h1 i).mono fun ω h => (lemma_EC_4 I).2 ω i h, h3, ?_⟩
  -- Part iv).
  have hconv : ∀ᵐ ω ∂(trialMeasure I), ∀ i,
      Tendsto (fun T => mu I T ω i) atTop (𝓝 (theta ω i)) :=
    ae_all_iff.2 fun i => (h3 i).1
  have hne : ∀ᵐ ω ∂(trialMeasure I), ∀ i j, i ≠ j → theta ω i ≠ theta ω j := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun ω h => absurd hij h
    · exact (theta_ne_ae I hij).mono fun ω h _ => h
  filter_upwards [hconv, hne] with ω hc hn
  have hM : (Finset.univ : Finset (Fin M)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, by have := I.two_le; omega⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun k => theta ω k) hM
  have hlt : ∀ j, j ≠ i → theta ω j < theta ω i := fun j hj =>
    lt_of_le_of_ne (hi j (Finset.mem_univ j)) (hn j i hj)
  refine ⟨i, hlt, ?_⟩
  rw [eventually_all]
  intro j
  by_cases hj : j = i
  · exact Eventually.of_forall fun T h => absurd hj h
  · have hd : Tendsto (fun T => mu I T ω i - mu I T ω j) atTop
        (𝓝 (theta ω i - theta ω j)) := (hc i).sub (hc j)
    have hpos : 0 < theta ω i - theta ω j := sub_pos.2 (hlt j hj)
    exact (hd.eventually (lt_mem_nhds hpos)).mono fun T hT _ => by linarith
