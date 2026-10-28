-- Prove2me | solution 1 for AvramDividend.Classical.adapted_leftContinuous_isStronglyProgressive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:14:28.752321+00:00
-- url     : https://prove2.me/submissions/a36ec4ba-7e7e-4d79-87f1-b1d0a970d27a

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace S189LC_

lemma S189LC_floor_tendsto (s : ℝ≥0) :
    Tendsto (fun n : ℕ => ((⌊s * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n)) atTop (𝓝[≤] s) := by
  have hle : ∀ n : ℕ, ((⌊s * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n) ≤ s := by
    intro n
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hle⟩
  rw [← NNReal.tendsto_coe]
  have hlow : ∀ n : ℕ, (s : ℝ) - 1 / 2 ^ n ≤ (((⌊s * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := by
    intro n
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    push_cast
    rw [le_div_iff₀ h2, sub_mul, one_div, inv_mul_cancel₀ h2.ne']
    have := Nat.lt_floor_add_one (s * 2 ^ n)
    have h' : ((s * 2 ^ n : ℝ≥0) : ℝ) < ((⌊s * 2 ^ n⌋₊ : ℝ≥0) : ℝ) + 1 := by
      exact_mod_cast this
    push_cast at h'
    linarith
  have hup : ∀ n : ℕ, (((⌊s * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ≤ s := fun n => by
    exact_mod_cast hle n
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlow hup
  have : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    simp only [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using (tendsto_const_nhds (x := (s : ℝ))).sub this

end S189LC_

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (hAdapted : StronglyAdapted 𝓕 D)
    (hLeft : ∀ ω t, ContinuousWithinAt (fun s : ℝ≥0 => D s ω) (Iic t) t) :
    IsStronglyProgressive 𝓕 D := by
  intro i
  let m : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (𝓕 i)
  let g : ℕ → Ω × ℕ → ℝ := fun n q => D (min ((q.2 : ℝ≥0) / 2 ^ n) i) q.1
  have hg : ∀ n, @Measurable _ _ ((𝓕 i).prod Nat.instMeasurableSpace) _ (g n) := by
    intro n
    refine @measurable_from_prod_countable_left _ _ _ (𝓕 i) _ _ _ _ _ ?_
    intro k
    exact ((hAdapted (min ((k : ℝ≥0) / 2 ^ n) i)).mono (𝓕.mono (min_le_right _ _))).measurable
  have hfl : ∀ n : ℕ, @Measurable _ _ m ((𝓕 i).prod Nat.instMeasurableSpace)
      (fun p : Set.Iic i × Ω => (p.2, ⌊(p.1 : ℝ≥0) * 2 ^ n⌋₊)) := by
    intro n
    refine @Measurable.prodMk _ m _ _ (𝓕 i) _ _ _ (@measurable_snd _ _ _ (𝓕 i)) ?_
    exact (((measurable_subtype_coe.comp measurable_fst).mul_const _)).nat_floor
  have hDn : ∀ n : ℕ, StronglyMeasurable[m]
      (fun p : Set.Iic i × Ω => g n (p.2, ⌊(p.1 : ℝ≥0) * 2 ^ n⌋₊)) := fun n =>
    ((hg n).comp (hfl n)).stronglyMeasurable
  refine stronglyMeasurable_of_tendsto atTop hDn ?_
  rw [tendsto_pi_nhds]
  rintro ⟨⟨s, hs⟩, ω⟩
  have hle : ∀ n : ℕ, ((⌊s * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n) ≤ s := by
    intro n
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)
  have hmin : ∀ n : ℕ, min ((⌊s * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n) i = (⌊s * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n :=
    fun n => min_eq_left ((hle n).trans hs)
  simp only [g, hmin]
  exact (hLeft ω s).tendsto.comp (S189LC_.S189LC_floor_tendsto s)
