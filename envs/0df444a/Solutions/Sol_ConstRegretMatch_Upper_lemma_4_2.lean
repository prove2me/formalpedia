-- Prove2me | solution 1 for ConstRegretMatch.Upper.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T22:57:09.377059+00:00
-- url     : https://prove2.me/submissions/094ccc7e-4e90-4689-a419-6b03fb5d4193

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {S : Type*} [MeasurableSpace S] (P : Kernel S S) [IsMarkovKernel P]
    (f g : S → ℝ) (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x)
    (hg0 : ∀ x, 0 ≤ g x) (hgi : ∀ x, Integrable g (P x)) (c : ℝ)
    (hdrift : ∀ x, ∫ y, g y ∂(P x) - g x ≤ -f x + c)
    (π : Measure S) [IsProbabilityMeasure π] (hπ : P.Invariant π) :
    Integrable f π ∧ ∫ x, f x ∂π ≤ c := by
  -- Step 1: truncated drift inequality for each level K.
  have key : ∀ K : ℝ, 0 ≤ K →
      Integrable ({x | g x ≤ K}.indicator f) π ∧
      ∫ x, {x | g x ≤ K}.indicator f x ∂π ≤ c * π.real {x | g x ≤ K} := by
    intro K hK
    set A := {x | g x ≤ K} with hA
    have hAm : MeasurableSet A := measurableSet_le hg measurable_const
    set φ : S → ℝ := fun y => min (g y) K with hφ
    have hφm : Measurable φ := hg.min measurable_const
    have hφ0 : ∀ y, 0 ≤ φ y := fun y => le_min (hg0 y) hK
    have hφK : ∀ y, φ y ≤ K := fun y => min_le_right _ _
    have hφi : ∀ (μ : Measure S) [IsFiniteMeasure μ], Integrable φ μ := by
      intro μ _
      exact (integrable_const K).mono' hφm.aestronglyMeasurable
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 y)]; exact hφK y)
    set Pφ : S → ℝ := fun x => ∫ y, φ y ∂(P x) with hPφ
    have hPφm : Measurable Pφ := (hφm.stronglyMeasurable.integral_kernel (κ := P)).measurable
    have hPφ0 : ∀ x, 0 ≤ Pφ x := fun x => integral_nonneg hφ0
    have hPφK : ∀ x, Pφ x ≤ K := fun x => by
      have := integral_mono (hφi (P x)) (integrable_const K) hφK
      simpa using this
    have hPφg : ∀ x, Pφ x ≤ ∫ y, g y ∂(P x) := fun x =>
      integral_mono (hφi (P x)) (hgi x) (fun y => min_le_left _ _)
    have hPφi : Integrable Pφ π :=
      (integrable_const K).mono' hPφm.aestronglyMeasurable
        (ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hPφ0 y)]; exact hPφK y)
    have hpt : ∀ x, A.indicator f x + Pφ x ≤ A.indicator (fun _ => c) x + φ x := by
      intro x
      by_cases hx : g x ≤ K
      · have hxA : x ∈ A := hx
        rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxA]
        have : φ x = g x := min_eq_left hx
        rw [this]
        linarith [hdrift x, hPφg x]
      · have hxA : x ∉ A := hx
        rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem hxA]
        have : φ x = K := min_eq_right (le_of_lt (not_le.mp hx))
        rw [this]
        linarith [hPφK x]
    have hIf : Integrable (A.indicator f) π := by
      refine (integrable_const (|c| + K)).mono' (hf.indicator hAm).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      have h0 : 0 ≤ A.indicator f x := Set.indicator_nonneg (fun y _ => hf0 y) x
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      have h1 := hpt x
      have h2 : A.indicator (fun _ => c) x ≤ |c| := by
        by_cases hx : x ∈ A
        · rw [Set.indicator_of_mem hx]; exact le_abs_self c
        · rw [Set.indicator_of_notMem hx]; exact abs_nonneg c
      linarith [hPφ0 x, hφK x]
    have hinv : ∫ x, Pφ x ∂π = ∫ x, φ x ∂π := by
      have h1 : ∀ x, ENNReal.ofReal (Pφ x) = ∫⁻ y, ENNReal.ofReal (φ y) ∂(P x) := fun x =>
        ofReal_integral_eq_lintegral_ofReal (hφi _) (ae_of_all _ hφ0)
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hPφ0) hPφm.aestronglyMeasurable,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hφ0) hφm.aestronglyMeasurable]
      congr 1
      simp_rw [h1]
      rw [← Measure.lintegral_bind (Kernel.aemeasurable _)
        hφm.ennreal_ofReal.aemeasurable]
      rw [hπ.def]
    have hci : Integrable (A.indicator (fun _ => c)) π := (integrable_const c).indicator hAm
    have hmono := integral_mono (hIf.add hPφi) (hci.add (hφi π)) hpt
    simp only [Pi.add_apply] at hmono
    rw [integral_add hIf hPφi, integral_add hci (hφi π), hinv, integral_indicator_const _ hAm,
      smul_eq_mul] at hmono
    refine ⟨hIf, ?_⟩
    linarith
  -- Step 2: let K → ∞ along the naturals.
  set F : ℕ → S → ℝ := fun n => {x | g x ≤ (n : ℝ)}.indicator f with hF
  have hFm : ∀ n, Measurable (F n) := fun n =>
    hf.indicator (measurableSet_le hg measurable_const)
  have hF0 : ∀ n x, 0 ≤ F n x := fun n x => Set.indicator_nonneg (fun y _ => hf0 y) x
  have hFle : ∀ n x, F n x ≤ f x := fun n x =>
    Set.indicator_le_self' (fun y _ => hf0 y) x
  have hFmono : ∀ x, Monotone (fun n => F n x) := by
    intro x a b hab
    simp only [hF]
    apply Set.indicator_le_indicator_of_subset _ (fun y => hf0 y)
    intro y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    exact hy.trans (by exact_mod_cast hab)
  have hFlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    intro x
    apply tendsto_atTop_of_eventually_const (i₀ := ⌈g x⌉₊)
    intro n hn
    simp only [hF]
    rw [Set.indicator_of_mem]
    simp only [Set.mem_ofPred_eq]
    exact (Nat.le_ceil (g x)).trans (by exact_mod_cast hn)
  have hkey : ∀ n : ℕ, Integrable (F n) π ∧ ∫ x, F n x ∂π ≤ c * π.real {x | g x ≤ (n : ℝ)} :=
    fun n => key n (Nat.cast_nonneg n)
  have hbound : ∀ n : ℕ, c * π.real {x | g x ≤ (n : ℝ)} ≤ |c| := by
    intro n
    have h1 : π.real {x | g x ≤ (n : ℝ)} ≤ 1 := measureReal_le_one
    have h0 : 0 ≤ π.real {x | g x ≤ (n : ℝ)} := measureReal_nonneg
    nlinarith [le_abs_self c, neg_abs_le c, abs_nonneg c]
  have hlint : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂π) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂π)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · exact fun n => (hFm n).ennreal_ofReal.aemeasurable
    · exact ae_of_all _ fun x a b hab => ENNReal.ofReal_le_ofReal (hFmono x hab)
    · exact ae_of_all _ fun x => (ENNReal.continuous_ofReal.tendsto _).comp (hFlim x)
  have hle : ∫⁻ x, ENNReal.ofReal (f x) ∂π ≤ ENNReal.ofReal |c| := by
    apply le_of_tendsto' hlint
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hkey n).1 (ae_of_all _ (hF0 n))]
    exact ENNReal.ofReal_le_ofReal ((hkey n).2.trans (hbound n))
  have hfi : Integrable f π := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  refine ⟨hfi, ?_⟩
  have hint : Tendsto (fun n => ∫ x, F n x ∂π) atTop (𝓝 (∫ x, f x ∂π)) := by
    apply tendsto_integral_of_dominated_convergence f
    · exact fun n => (hFm n).aestronglyMeasurable
    · exact hfi
    · intro n
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n x)]; exact hFle n x
    · exact ae_of_all _ hFlim
  have hmeas : Tendsto (fun n : ℕ => π.real {x | g x ≤ (n : ℝ)}) atTop (𝓝 1) := by
    have hm : Monotone (fun n : ℕ => {x | g x ≤ (n : ℝ)}) := by
      intro a b hab y hy
      simp only [Set.mem_ofPred_eq] at hy ⊢
      exact hy.trans (by exact_mod_cast hab)
    have hU : (⋃ n : ℕ, {x | g x ≤ (n : ℝ)}) = Set.univ := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact ⟨⌈g y⌉₊, Nat.le_ceil _⟩
    have := tendsto_measure_iUnion_atTop (μ := π) hm
    rw [hU, measure_univ] at this
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp this
    simpa [Function.comp_def, measureReal_def] using h2
  have hc : Tendsto (fun n : ℕ => c * π.real {x | g x ≤ (n : ℝ)}) atTop (𝓝 c) := by
    simpa using hmeas.const_mul c
  exact le_of_tendsto_of_tendsto' hint hc (fun n => (hkey n).2)
