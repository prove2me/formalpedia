-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:23:47.174592+00:00
-- url     : https://prove2.me/submissions/9ff35f6e-af8f-40be-a44f-93ff8295c074

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_finite_distribution_measure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_closed_grid_iff
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

lemma S195E_meas {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0) :
    Measurable (X.X s) :=
  (X.adapted s).mono (𝓕.le s) le_rfl

lemma S195E_M {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (φ : ℝ) (hφ : 0 ≤ φ)
    (t : ℝ≥0) :
    Integrable (fun ω => Real.exp (φ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) P ∧
      ∫ ω, Real.exp (φ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν φ) ∂P = 1 := by
  have h := X.laplace t φ hφ
  simp_rw [Real.exp_sub]
  exact ⟨h.1.div_const _, by rw [integral_div, h.2, div_self (Real.exp_pos _).ne']⟩

/-- grid -/
noncomputable def S195E_g (T : ℝ≥0) (N k : ℕ) : ℝ≥0 :=
  min ((k : ℝ≥0) * ((N.factorial : ℕ) : ℝ≥0)⁻¹) T

noncomputable def S195E_m (T : ℝ≥0) (N : ℕ) : ℕ := N.factorial * (⌈T⌉₊ + 1)

lemma S195E_g_mono (T : ℝ≥0) (N : ℕ) : Monotone (S195E_g T N) := by
  intro i j hij
  unfold S195E_g
  apply min_le_min_right
  gcongr

lemma S195E_g_le (T : ℝ≥0) (N k : ℕ) : S195E_g T N k ≤ T := min_le_right _ _

lemma S195E_g_succ (T : ℝ≥0) (N k : ℕ) :
    S195E_g T (N + 1) (k * (N + 1)) = S195E_g T N k := by
  unfold S195E_g
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  have h1 : ((N.factorial : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
  have h2 : ((N : ℝ≥0) + 1) ≠ 0 := by positivity
  field_simp

lemma S195E_cover {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (T : ℝ≥0) (ω : Ω)
    (hω : ¬ ∀ s : ℝ≥0, s ≤ T → 0 ≤ b + X.X s ω) :
    ∃ N k, k ≤ S195E_m T N ∧ X.X (S195E_g T N k) ω ≤ -b := by
  rw [chat04_random_reserve_lower_survival_closed_grid_iff X (fun _ => b) ω T] at hω
  simp only [not_and_or, not_forall, not_le, exists_prop] at hω
  rcases hω with ⟨n, hn, k, hk, hlt⟩ | hlt
  · refine ⟨n, k * (n.factorial / n), ?_, ?_⟩
    · have hd : n ∣ n.factorial := Nat.dvd_factorial hn le_rfl
      have hnr : ((n : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
      have hf : ((n.factorial : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      have hc : ((k * (n.factorial / n) : ℕ) : ℝ≥0) = (k : ℝ≥0) * (n : ℝ≥0)⁻¹ * n.factorial := by
        rw [Nat.cast_mul, Nat.cast_div hd hnr]
        field_simp
      have : ((k * (n.factorial / n) : ℕ) : ℝ≥0) < ((S195E_m T n : ℕ) : ℝ≥0) := by
        rw [hc]
        unfold S195E_m
        push_cast
        have hT : T < (⌈T⌉₊ : ℝ≥0) + 1 := lt_of_le_of_lt (Nat.le_ceil T) (by simp)
        calc (k : ℝ≥0) * (n : ℝ≥0)⁻¹ * n.factorial < T * n.factorial := by
              gcongr
          _ ≤ ((⌈T⌉₊ : ℝ≥0) + 1) * n.factorial := by gcongr
          _ = _ := by ring
      exact_mod_cast this.le
    · have hd : n ∣ n.factorial := Nat.dvd_factorial hn le_rfl
      have hnr : ((n : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
      have hf : ((n.factorial : ℕ) : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      have hg : S195E_g T n (k * (n.factorial / n)) = (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by
        unfold S195E_g
        rw [min_eq_left]
        · rw [Nat.cast_mul, Nat.cast_div hd hnr]
          field_simp
        · rw [Nat.cast_mul, Nat.cast_div hd hnr]
          field_simp
          field_simp at hk
          exact hk.le
      rw [hg]; linarith
  · refine ⟨0, S195E_m T 0, le_rfl, ?_⟩
    have : S195E_g T 0 (S195E_m T 0) = T := by
      unfold S195E_g S195E_m
      rw [min_eq_right]
      simp only [Nat.factorial_zero, one_mul, Nat.cast_one, inv_one, mul_one]
      push_cast
      exact (Nat.le_ceil T).trans (by simp)
    rw [this]; linarith

lemma S195E_lower {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) (b : ℝ) (T : ℝ≥0) :
    1 - Real.exp (-(φ / 2) * b) ≤
      ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ T → 0 ≤ b + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X T ω -
              (T : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P := by
  set M : Ω → ℝ := fun ω => Real.exp (φ * X.X T ω - (T : ℝ) * laplaceExponent X.c X.σ X.ν φ)
    with hMdef
  obtain ⟨hMi, hM1⟩ := S195E_M X φ hφ.le T
  have hMnn : ∀ ω, 0 ≤ M ω := fun ω => (Real.exp_pos _).le
  set S := {ω | ∀ s : ℝ≥0, s ≤ T → 0 ≤ b + X.X s ω} with hSdef
  -- measurability of S
  have hS : MeasurableSet S := by
    have : S = (⋂ n : ℕ, ⋂ (_ : 0 < n), ⋂ k : ℕ, ⋂ (_ : (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T),
        {ω | 0 ≤ b + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω}) ∩ {ω | 0 ≤ b + X.X T ω} := by
      ext ω
      simp only [hSdef, mem_ofPred_eq,
        chat04_random_reserve_lower_survival_closed_grid_iff X (fun _ => b) ω T, mem_inter_iff,
        mem_iInter]
    rw [this]
    refine MeasurableSet.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => ?_) ?_
    · exact measurableSet_le measurable_const (measurable_const.add (S195E_meas X _))
    · exact measurableSet_le measurable_const (measurable_const.add (S195E_meas X _))
  -- the covering sets
  let A : ℕ → Set Ω := fun N => {ω | ∃ k : ℕ, k ≤ S195E_m T N ∧ X.X (S195E_g T N k) ω ≤ -b}
  have hAm : ∀ N, MeasurableSet (A N) := by
    intro N
    have : A N = ⋃ k : ℕ, ⋃ (_ : k ≤ S195E_m T N), {ω | X.X (S195E_g T N k) ω ≤ -b} := by
      ext ω; simp [A]
    rw [this]
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      measurableSet_le (S195E_meas X _) measurable_const
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun N => ?_
    rintro ω ⟨k, hk, hX⟩
    refine ⟨k * (N + 1), ?_, ?_⟩
    · unfold S195E_m at hk ⊢
      rw [Nat.factorial_succ]
      calc k * (N + 1) ≤ N.factorial * (⌈T⌉₊ + 1) * (N + 1) := Nat.mul_le_mul_right _ hk
        _ = _ := by ring
    · rw [S195E_g_succ]; exact hX
  set AU := ⋃ N, A N with hAU
  have hAUm : MeasurableSet AU := MeasurableSet.iUnion hAm
  have hcov : Sᶜ ⊆ AU := by
    intro ω hω
    obtain ⟨N, k, hk, hX⟩ := S195E_cover X b T ω hω
    exact mem_iUnion.2 ⟨N, k, hk, hX⟩
  -- Q bound
  set ε := Real.exp (-(φ / 2) * b) with hε
  set Q := P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ))) with hQ
  have hQA : ∀ N, Q (A N) ≤ ENNReal.ofReal ε := by
    intro N
    have h := chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound X q φ b hq hφ
      hroot T (S195E_g T N) (S195E_g_mono T N) (S195E_g_le T N)
      (Real.toNNReal (Real.exp ((φ / 2) * b))) (Real.coe_toNNReal _ (Real.exp_pos _).le)
      (S195E_m T N)
    have he : ENNReal.ofReal ε = ((Real.toNNReal (Real.exp ((φ / 2) * b)) : ℝ≥0∞))⁻¹ := by
      rw [hε, neg_mul, Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
      rfl
    rw [he, ENNReal.le_inv_iff_mul_le, mul_comm]
    exact h
  have hQAU : Q AU ≤ ENNReal.ofReal ε := by
    rw [hAU, hAmono.measure_iUnion]
    exact iSup_le hQA
  have hMi' : Integrable M P := hMi
  have hM1' : ∫ ω, M ω ∂P = 1 := hM1
  have hIA : ∫ ω, AU.indicator M ω ∂P ≤ ε := by
    rw [integral_indicator hAUm]
    have h1 : ENNReal.ofReal (∫ ω in AU, M ω ∂P) = Q AU := by
      rw [ofReal_integral_eq_lintegral_ofReal hMi'.integrableOn (ae_of_all _ hMnn), hQ,
        withDensity_apply _ hAUm]
      rfl
    rw [← h1] at hQAU
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 hQAU
  calc 1 - ε ≤ ∫ ω, M ω ∂P - ∫ ω, AU.indicator M ω ∂P := by rw [hM1']; linarith
    _ = ∫ ω, (M ω - AU.indicator M ω) ∂P := (integral_sub hMi' (hMi'.indicator hAUm)).symm
    _ ≤ ∫ ω, S.indicator M ω ∂P := by
      refine integral_mono (hMi'.sub (hMi'.indicator hAUm)) (hMi'.indicator hS) (fun ω => ?_)
      by_cases h : ω ∈ S
      · simp only [indicator_of_mem h]
        have := Set.indicator_nonneg (s := AU) (fun ω _ => hMnn ω) ω
        linarith
      · have h' : ω ∈ AU := hcov h
        simp [indicator_of_notMem h, indicator_of_mem h']

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      (∀ x : ℝ, ν (Iic x) =
        (⨅ t : ℝ≥0, ENNReal.ofReal
          (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P))) ∧
      ∀ b : ℝ, 0 < b →
        ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b)) ≤ ν (Iic b) := by
  obtain ⟨ν, hfin, hν⟩ := chat04_esscher_perpetual_infimum_finite_distribution_measure X φ hφ.le
  have hlow : ∀ b : ℝ, 0 < b → ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b)) ≤ ν (Iic b) := by
    intro b hb
    rw [hν]
    exact le_iInf fun t => ENNReal.ofReal_le_ofReal (S195E_lower X q φ hq hφ hroot b t)
  have hup : ∀ x : ℝ, ν (Iic x) ≤ 1 := by
    intro x
    rw [hν]
    refine (iInf_le _ 0).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨hMi, hM1⟩ := S195E_M X φ hφ.le 0
    rw [← hM1]
    refine integral_mono_of_nonneg (ae_of_all _ fun ω => ?_) hMi (ae_of_all _ fun ω => ?_)
    · exact Set.indicator_nonneg (fun ω _ => (Real.exp_pos _).le) ω
    · exact Set.indicator_le_self' (fun ω _ => (Real.exp_pos _).le) ω
  have ht := tendsto_measure_Iic_atTop ν
  refine ⟨ν, ⟨le_antisymm ?_ ?_⟩, hν, hlow⟩
  · exact le_of_tendsto' ht hup
  · have hlim : Tendsto (fun b : ℝ => ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b))) atTop
        (𝓝 (ENNReal.ofReal (1 - 0))) := by
      apply ENNReal.tendsto_ofReal
      apply tendsto_const_nhds.sub
      apply Real.tendsto_exp_atBot.comp
      exact Filter.tendsto_id.const_mul_atTop_of_neg (by linarith : -(φ / 2) < 0)
    rw [sub_zero, ENNReal.ofReal_one] at hlim
    exact le_of_tendsto_of_tendsto hlim ht ((eventually_gt_atTop 0).mono hlow)

