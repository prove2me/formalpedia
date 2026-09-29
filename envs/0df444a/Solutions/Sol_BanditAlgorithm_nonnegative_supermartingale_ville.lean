-- Prove2me | solution 1 for BanditAlgorithm.nonnegative_supermartingale_ville
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T14:27:55.943369+00:00
-- url     : https://prove2.me/submissions/34cef495-9130-4b11-b329-bfb948d16314

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ)
    (hf : Supermartingale f ℱ P)
    (hnonneg : ∀ t : ℕ, 0 ≤ᵐ[P] f t)
    (h0 : ∀ᵐ ω ∂P, f 0 ω ≤ 1)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    P.real {ω | ∃ t : ℕ, 1 / δ ≤ f t ω} ≤ δ := by
  classical
  have hδpos : 0 < δ := hδ.1
  let ε : ℝ := 1 / δ
  have hεpos : 0 < ε := one_div_pos.mpr hδpos
  let E : ℕ → Set Ω := fun n => {ω | ∃ t ≤ n, ε ≤ f t ω}
  have hE_meas : ∀ n, MeasurableSet (E n) := by
    intro n
    change MeasurableSet {ω | ∃ t ≤ n, ε ≤ f t ω}
    rw [show {ω | ∃ t ≤ n, ε ≤ f t ω} =
        ⋃ t ∈ Finset.range (n + 1), {ω | ε ≤ f t ω} by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff]
      aesop]
    exact Finset.measurableSet_biUnion _ fun t _ =>
      measurableSet_le measurable_const
        ((hf.stronglyMeasurable t).measurable.le (ℱ.le t))
  have hE_mono : Monotone E := by
    intro n m hnm ω hω
    rcases hω with ⟨t, htn, ht⟩
    exact ⟨t, htn.trans hnm, ht⟩
  have hEn : ∀ n, P.real (E n) ≤ δ := by
    intro n
    let τ : Ω → ℕ∞ :=
      fun ω => (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)
    have hτ_stop : IsStoppingTime ℱ τ :=
      hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
    have hτ_le : ∀ ω, τ ω ≤ n := fun ω => by
      change (↑(hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω) : ℕ∞) ≤ ↑n
      exact_mod_cast
        (hittingBtwn_le (u := f) (s := {y : ℝ | ε ≤ y}) (n := 0) (m := n) ω)
    have hzero_le_τ : (fun _ : Ω => (0 : ℕ∞)) ≤ τ := by
      intro ω
      exact bot_le
    have hτ_int : Integrable (stoppedValue f τ) P :=
      integrable_stoppedValue ℕ hτ_stop hf.integrable hτ_le
    have hτ_nonneg : 0 ≤ᵐ[P] stoppedValue f τ := by
      have hall : ∀ᵐ ω ∂P, ∀ t : ℕ, 0 ≤ f t ω := ae_all_iff.2 hnonneg
      filter_upwards [hall] with ω hω
      simpa only [Pi.zero_apply, stoppedValue] using hω (τ ω).untopA
    have hτ_expect_le : ∫ ω, stoppedValue f τ ω ∂P ≤ ∫ ω, f 0 ω ∂P := by
      have h :=
        hf.neg.expected_stoppedValue_mono
          (isStoppingTime_const ℱ (0 : ℕ)) hτ_stop hzero_le_τ hτ_le
      have hnegstop : stoppedValue (-f) τ = -stoppedValue f τ := by
        funext ω
        simp [stoppedValue]
      rw [stoppedValue_const, hnegstop] at h
      have hleft :
          (∫ x, (-f) 0 x ∂P) = -(∫ x, f 0 x ∂P) := by
        simpa only [Pi.neg_apply] using
          (integral_neg (μ := P) (f := fun x => f 0 x))
      have hright :
          (∫ x, (-stoppedValue f τ) x ∂P) =
            -(∫ x, stoppedValue f τ x ∂P) := by
        exact integral_neg (μ := P) (f := stoppedValue f τ)
      rw [hleft, hright] at h
      linarith
    have hf0_le_one : ∫ ω, f 0 ω ∂P ≤ 1 := by
      calc
        ∫ ω, f 0 ω ∂P ≤ ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_mono_ae (hf.integrable 0) (integrable_const 1) h0
        _ = 1 := by simp
    have hmarkov :
        ε * P.real {ω | ε ≤ stoppedValue f τ ω} ≤
          ∫ ω, stoppedValue f τ ω ∂P :=
      mul_meas_ge_le_integral_of_nonneg hτ_nonneg hτ_int ε
    have hset : {ω | ε ≤ stoppedValue f τ ω} = E n := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hhit
        by_contra hno
        simp only [E, Set.mem_setOf_eq, not_exists, not_and] at hno
        have hnone : ¬ ∃ t ∈ Set.Icc (0 : ℕ) n, f t ω ∈ {y : ℝ | ε ≤ y} := by
          push Not
          rintro t ⟨_, htn⟩ ht
          exact hno t htn ht
        have hτeq : τ ω = n := by
          change (↑(if ∃ j ∈ Set.Icc (0 : ℕ) n, f j ω ∈ {y : ℝ | ε ≤ y}
            then sInf (Set.Icc 0 n ∩ {i : ℕ | f i ω ∈ {y : ℝ | ε ≤ y}})
            else n) : ℕ∞) = ↑n
          rw [if_neg hnone]
        rw [show stoppedValue f τ ω = f n ω by simp [stoppedValue, hτeq]] at hhit
        exact (hno n le_rfl) hhit
      · rintro ⟨t, htn, ht⟩
        have hex : ∃ j ∈ Set.Icc (0 : ℕ) n, f j ω ∈ {y : ℝ | ε ≤ y} :=
          ⟨t, ⟨Nat.zero_le t, htn⟩, ht⟩
        have hmem := stoppedValue_hittingBtwn_mem hex
        exact hmem
    rw [hset] at hmarkov
    have hprod : ε * P.real (E n) ≤ 1 :=
      hmarkov.trans (hτ_expect_le.trans hf0_le_one)
    calc
      P.real (E n) ≤ 1 / ε := (le_div_iff₀ hεpos).2 (by simpa [mul_comm] using hprod)
      _ = δ := by simp [ε]
  have hUnion :
      {ω | ∃ t : ℕ, 1 / δ ≤ f t ω} = ⋃ n : ℕ, E n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E, ε]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, t, le_rfl, ht⟩
    · rintro ⟨n, t, _, ht⟩
      exact ⟨t, ht⟩
  rw [hUnion]
  rw [measureReal_def, hE_mono.measure_iUnion,
    ENNReal.toReal_iSup (fun n => measure_ne_top P (E n))]
  exact ciSup_le hEn
