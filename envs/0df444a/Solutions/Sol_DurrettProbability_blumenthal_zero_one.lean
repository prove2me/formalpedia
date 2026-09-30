-- Prove2me | solution 1 for DurrettProbability.blumenthal_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T07:50:19.735422+00:00
-- url     : https://prove2.me/submissions/9452a8d4-b77e-4e34-b4ac-6fe30e79da6f

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory DurrettProbability in open scoped NNReal Topology in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {A : Set Ω} (hA : MeasurableSet[germSigma B] A) :
    P A = 0 ∨ P A = 1 := by
  -- a sequence of positive times decreasing to `0`
  obtain ⟨ε, hεpos, hεanti, hεlim⟩ : ∃ ε : ℕ → ℝ≥0,
      (∀ n, 0 < ε n) ∧ Antitone ε ∧ Tendsto ε atTop (𝓝 0) := by
    refine ⟨fun n => (((n + 1 : ℕ) : ℝ≥0))⁻¹, fun n => ?_, fun i j hij => ?_, ?_⟩
    · exact inv_pos.2 (Nat.cast_pos.2 n.succ_pos)
    · have hi : (0 : ℝ≥0) < ((i + 1 : ℕ) : ℝ≥0) := Nat.cast_pos.2 i.succ_pos
      have hij' : ((i + 1 : ℕ) : ℝ≥0) ≤ ((j + 1 : ℕ) : ℝ≥0) := by
        exact_mod_cast Nat.succ_le_succ hij
      exact inv_anti₀ hi hij'
    · exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).comp (tendsto_add_atTop_nat 1)
  -- the σ-algebras of the shifted processes after time `ε n`
  obtain ⟨D, hD⟩ : ∃ D : ℕ → MeasurableSpace Ω, ∀ n, D n =
      MeasurableSpace.comap (fun ω (u : ℝ≥0) => B (ε n + u) ω - B (ε n) ω)
        MeasurableSpace.pi := ⟨_, fun _ => rfl⟩
  have hYm : ∀ n v, Measurable[D n] (fun ω => B (ε n + v) ω - B (ε n) ω) := by
    intro n v
    rw [hD n]
    exact (measurable_pi_apply v).comp
      (comap_measurable (fun ω (u : ℝ≥0) => B (ε n + u) ω - B (ε n) ω))
  have hGpast : ∀ s : ℝ≥0, 0 < s → germSigma B ≤ pastSigma B s := fun s hs => iInf₂_le s hs
  have hpast0 : ∀ s, pastSigma B s ≤ ‹MeasurableSpace Ω› :=
    fun s => iSup₂_le fun r _ => measurable_iff_comap_le.1 (hBm r)
  have hGle : germSigma B ≤ ‹MeasurableSpace Ω› := (hGpast 1 one_pos).trans (hpast0 1)
  -- weak Markov property: the germ field is independent of each shifted process
  have hind : ∀ n, Indep (D n) (germSigma B) P := by
    intro n
    have h := hB.toIsPreBrownianReal.indepFun_shift (ε n)
    rw [IndepFun_iff_Indep] at h
    rw [hD n]
    refine indep_of_indep_of_le_right h ?_
    refine (hGpast _ (hεpos n)).trans ?_
    refine iSup₂_le fun r hr => ?_
    rw [← measurable_iff_comap_le]
    exact (measurable_pi_apply (⟨r, hr⟩ : Set.Iic (ε n))).comp
      (comap_measurable (fun ω (t : Set.Iic (ε n)) => B t ω))
  have hDmono : Monotone D := by
    intro i j hij
    rw [hD i, ← measurable_iff_comap_le]
    refine @measurable_pi_lambda Ω ℝ≥0 (fun _ => ℝ) (D j) _ _ fun u => ?_
    have hji : ε j ≤ ε i := hεanti hij
    have e1 : ε j + (ε i - ε j + u) = ε i + u := by
      rw [← add_assoc, add_tsub_cancel_of_le hji]
    have e2 : ε j + (ε i - ε j) = ε i := add_tsub_cancel_of_le hji
    have h1 := (hYm j (ε i - ε j + u)).sub (hYm j (ε i - ε j))
    rw [e1, e2] at h1
    convert h1 using 2 with ω
    rw [Pi.sub_apply]
    ring
  have hDle : ∀ n, D n ≤ ‹MeasurableSpace Ω› := by
    intro n
    rw [hD n, ← measurable_iff_comap_le]
    exact measurable_pi_lambda _ fun u => (hBm _).sub (hBm _)
  have hindH : Indep (⨆ n, D n) (germSigma B) P :=
    indep_iSup_of_directed_le hind hDle hGle hDmono.directed_le
  have hAm0 : MeasurableSet A := hGle _ hA
  -- continuity at time 0
  set C : Set Ω := {ω | Tendsto (fun t => B t ω) (𝓝 0) (𝓝 0)} with hCdef
  have hC : ∀ᵐ ω ∂P, ω ∈ C := hB.tendsto_nhds_zero
  have key : ∃ A', MeasurableSet[⨆ n, D n] A' ∧ A =ᵐ[P] A' := by
    -- the σ-algebra of sets a.e. equal to a set of `⨆ n, D n`
    obtain ⟨M, hM⟩ : ∃ M : MeasurableSpace Ω, ∀ s,
        MeasurableSet[M] s ↔ ∃ t, MeasurableSet[⨆ n, D n] t ∧ s =ᵐ[P] t := by
      refine ⟨{ MeasurableSet' := fun s => ∃ t, MeasurableSet[⨆ n, D n] t ∧ s =ᵐ[P] t
                measurableSet_empty := ⟨∅, @MeasurableSet.empty _ (⨆ n, D n), EventuallyEq.rfl⟩
                measurableSet_compl := fun s ⟨t, ht, hst⟩ => ⟨tᶜ, ht.compl, hst.compl⟩
                measurableSet_iUnion := fun f hf => by
                  choose t ht hft using hf
                  exact ⟨⋃ i, t i, MeasurableSet.iUnion ht, Filter.EventuallyEq.countable_iUnion hft⟩ },
        fun s => Iff.rfl⟩
    have hHM : (⨆ n, D n) ≤ M := fun s hs => (hM s).2 ⟨s, hs, EventuallyEq.rfl⟩
    have hMae : ∀ s t : Set Ω, MeasurableSet[M] t → s =ᵐ[P] t → MeasurableSet[M] s := by
      intro s t ht hst
      obtain ⟨u, hu, htu⟩ := (hM t).1 ht
      exact (hM s).2 ⟨u, hu, hst.trans htu⟩
    have hMfun : ∀ f g : Ω → ℝ, Measurable[M] g → f =ᵐ[P] g → Measurable[M] f := by
      intro f g hg hfg S hS
      exact hMae _ _ (hg hS) (hfg.preimage S)
    have hCM : MeasurableSet[M] C :=
      hMae C Set.univ (@MeasurableSet.univ _ M) (ae_eq_univ.2 (ae_iff.1 hC))
    -- every `B t` is measurable for `M`
    have hBM : ∀ t, Measurable[M] (B t) := by
      intro t
      have hlim : Tendsto (fun n => min t (ε n)) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := t)).min hεlim
        simpa using this
      have hfM : ∀ n, Measurable[M] (C.indicator (fun ω => B t ω - B (min t (ε n)) ω)) := by
        intro n
        have hDn : Measurable[D n] (fun ω => B t ω - B (min t (ε n)) ω) := by
          rcases le_total (ε n) t with h | h
          · rw [min_eq_right h]
            have key := hYm n (t - ε n)
            rw [add_tsub_cancel_of_le h] at key
            exact key
          · rw [min_eq_left h]
            simp only [sub_self]
            exact measurable_const
        exact Measurable.indicator (hDn.mono ((le_iSup D n).trans hHM) le_rfl) hCM
      have hconv : Tendsto (fun n => C.indicator (fun ω => B t ω - B (min t (ε n)) ω)) atTop
          (𝓝 (C.indicator (B t))) := by
        rw [tendsto_pi_nhds]
        intro ω
        by_cases hω : ω ∈ C
        · simp only [Set.indicator_of_mem hω]
          have h0 : Tendsto (fun n => B (min t (ε n)) ω) atTop (𝓝 0) :=
            (show Tendsto (fun t => B t ω) (𝓝 0) (𝓝 0) from hω).comp hlim
          simpa using (tendsto_const_nhds (x := B t ω)).sub h0
        · simp only [Set.indicator_of_notMem hω]
          exact tendsto_const_nhds
      have hIM : Measurable[M] (C.indicator (B t)) :=
        @measurable_of_tendsto_metrizable Ω ℝ M _ _ _ _ _ _ hfM hconv
      refine hMfun (B t) (C.indicator (B t)) hIM ?_
      filter_upwards [hC] with ω hω
      simp [Set.indicator_of_mem hω]
    have hpastM : pastSigma B 1 ≤ M := iSup₂_le fun r _ => measurable_iff_comap_le.1 (hBM r)
    have hAM : MeasurableSet[M] A := hpastM _ (hGpast 1 one_pos _ hA)
    exact (hM A).1 hAM
  obtain ⟨A', hA'H, hAA'⟩ := key
  have hmul : P (A' ∩ A) = P A' * P A := (Indep_iff _ _ P).1 hindH A' A hA'H hA
  have h1 : P (A' ∩ A) = P A := by
    apply measure_congr
    have := hAA'.symm.inter (EventuallyEq.rfl : A =ᵐ[P] A)
    rw [Set.inter_self] at this
    exact this
  have h2 : P A' = P A := measure_congr hAA'.symm
  apply measure_eq_zero_or_one_of_indepSet_self
  rw [indepSet_iff_measure_inter_eq_mul hAm0 hAm0 P, Set.inter_self]
  calc P A = P (A' ∩ A) := h1.symm
    _ = P A' * P A := hmul
    _ = P A * P A := by rw [h2]
