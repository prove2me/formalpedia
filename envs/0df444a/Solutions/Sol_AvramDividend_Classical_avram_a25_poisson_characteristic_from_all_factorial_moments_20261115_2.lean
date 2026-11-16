-- Prove2me | solution 2 for AvramDividend.Classical.avram_a25_poisson_characteristic_from_all_factorial_moments_20261115
-- status  : ACCEPTED   (disprove)
-- author  : @garyholm
-- created : 2026-11-15T15:16:50.615914+00:00
-- url     : https://prove2.me/submissions/de48d93f-b2b4-469a-a6b8-9b57acc8e9af

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Nat

lemma inv_not_integrable_aux (g : ℝ → ℝ) (c : ℝ)
    (hg : Integrable g (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hb : ∀ ω ∈ Set.Ioc (0 : ℝ) 1, ω⁻¹ ≤ g ω + c) : False := by
  have hgc : Integrable (fun ω => g ω + c) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hg.add (integrable_const c)
  have hinv : Integrable (fun ω : ℝ => ω⁻¹) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine hgc.mono measurable_inv.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
    intro ω hω
    have h0 : 0 < ω⁻¹ := inv_pos.2 hω.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h0,
      abs_of_pos (lt_of_lt_of_le h0 (hb ω hω))]
    exact hb ω hω
  have hII : IntervalIntegrable (fun ω : ℝ => ω⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hinv
  rw [intervalIntegrable_inv_iff] at hII
  rcases hII with h | h
  · norm_num at h
  · exact h (Set.left_mem_uIcc)

lemma descFact_lower (k n : ℕ) (hn : 1 ≤ n) :
    (k : ℝ) - n + 1 ≤ (k.descFactorial n : ℝ) := by
  by_cases hkn : k < n
  · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    have h0 : (0 : ℝ) ≤ (k.descFactorial n : ℝ) := by positivity
    linarith
  · push_neg at hkn
    have h1 : (k + 1 - n) ^ n ≤ k.descFactorial n := Nat.pow_sub_le_descFactorial k n
    have h2 : k + 1 - n ≤ (k + 1 - n) ^ n := Nat.le_self_pow (by omega) _
    have h3 : ((k + 1 - n : ℕ) : ℝ) = (k : ℝ) - n + 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← h3]
    exact_mod_cast h2.trans h1

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ), Measurable K →
    ∀ (r : ℝ≥0),
    (∀ n : ℕ, (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n) →
    ∀ u : ℝ,
      charFun (P.map (fun ω => (K ω : ℝ))) u =
      charFun ((poissonMeasure r).map (fun n : ℕ => (n : ℝ))) u) := by
  intro H
  let P : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  haveI : IsProbabilityMeasure P := ⟨by simp [P]⟩
  let K : ℝ → ℕ := fun ω => ⌊ω⁻¹⌋₊
  have hK : Measurable K := measurable_inv.nat_floor
  have hKlow : ∀ ω ∈ Set.Ioc (0 : ℝ) 1, ω⁻¹ ≤ (K ω : ℝ) + 1 :=
    fun ω _ => (Nat.lt_floor_add_one ω⁻¹).le
  have hMom : ∀ n : ℕ, (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = ((0 : ℝ≥0) : ℝ) ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [integral_undef]
      · simp [Nat.pos_iff_ne_zero.1 hn]
      · intro hint
        refine inv_not_integrable_aux _ (n : ℝ) hint ?_
        intro ω hω
        have := descFact_lower (K ω) n hn
        have := hKlow ω hω
        linarith
  have hcf := H P K hK 0 hMom
  have hKm : Measurable (fun ω => (K ω : ℝ)) := measurable_from_nat.comp hK
  have heq : P.map (fun ω => (K ω : ℝ)) = (poissonMeasure 0).map (fun n : ℕ => (n : ℝ)) :=
    Measure.ext_of_charFun (funext hcf)
  have h0 := congrArg (fun μ : Measure ℝ => μ {0}) heq
  change (Measure.map (fun ω => (K ω : ℝ)) P) {0} = (Measure.map (fun n : ℕ => (n : ℝ)) (poissonMeasure 0)) {0} at h0
  rw [Measure.map_apply hKm (measurableSet_singleton 0),
    Measure.map_apply measurable_from_nat (measurableSet_singleton 0)] at h0
  have hpre : (fun n : ℕ => (n : ℝ)) ⁻¹' {0} = {0} := by
    ext n; simp
  rw [hpre, poissonMeasure_singleton] at h0
  have hL : P ((fun ω => (K ω : ℝ)) ⁻¹' {0}) = 0 := by
    rw [Measure.restrict_apply (hKm (measurableSet_singleton 0))]
    have : (fun ω => (K ω : ℝ)) ⁻¹' {0} ∩ Set.Ioc (0 : ℝ) 1 = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hk hω
      have := hKlow ω hω
      have h1 : 1 ≤ ω⁻¹ := one_le_inv_iff₀.2 ⟨hω.1, hω.2⟩
      rw [hk] at this
      have h2 : ω⁻¹ ≤ 1 := by linarith
      have h3 : ω⁻¹ = 1 := le_antisymm h2 h1
      have h4 : (1 : ℝ) ≤ K ω := by
        have : (1 : ℕ) ≤ K ω := Nat.le_floor (by simpa [h3])
        exact_mod_cast this
      linarith
    rw [this, measure_empty]
  rw [hL] at h0
  simp at h0
