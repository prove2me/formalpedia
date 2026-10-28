-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_le_of_nat_horizon_bounds
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:49:30.049107+00:00
-- url     : https://prove2.me/submissions/ab5a977b-f31e-4dc8-b782-d9dec4a7a2b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

universe u
/-- A bare copy of `ℕ` carrying no instances. -/
structure S107W : Type u where
  n : ℕ

namespace S107NH

/-- On the trivial σ-algebra a lintegral vanishes as soon as the integrand vanishes at one point
(measurable simple functions are constant). -/
lemma bot_lintegral {α : Type*} (μ : @Measure α ⊥) (f : α → ℝ≥0∞) (a : α) (ha : f a = 0) :
    @lintegral α ⊥ μ f = 0 := by
  letI : MeasurableSpace α := ⊥
  refine le_antisymm ?_ bot_le
  rw [MeasureTheory.lintegral]
  refine iSup₂_le fun g hg => ?_
  have hfib := g.measurableSet_fiber (g a)
  rw [MeasurableSpace.measurableSet_bot_iff] at hfib
  have hg0 : ∀ y, g y = 0 := by
    intro y
    rcases hfib with h | h
    · exact absurd (show a ∈ g ⁻¹' {g a} from rfl) (by rw [h]; exact id)
    · have hy : y ∈ g ⁻¹' {g a} := by rw [h]; trivial
      have : g y = g a := hy
      rw [this]; exact le_antisymm ((hg a).trans ha.le) bot_le
  have : g = 0 := SimpleFunc.ext hg0
  rw [this, SimpleFunc.zero_lintegral]

end S107NH

theorem solution : ¬ (∀ {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ B),
    dividendValue X q x D ≤ B) := by
  intro H
  letI mΩ : MeasurableSpace S107W.{0} := ⊥
  let P : Measure S107W.{0} := Measure.dirac ⟨0⟩
  let 𝓕 : Filtration ℝ≥0 mΩ :=
    { seq := fun _ => ⊥, mono' := fun _ _ _ => le_rfl, le' := fun _ => le_rfl }
  let X : SpectrallyNegativeLevy P 𝓕 :=
    { X := fun _ _ => 0
      c := 0
      σ := 0
      ν := 0
      isProbability := by infer_instance
      σ_nonneg := le_rfl
      ν_Ici := by simp
      ν_integrable := by simp
      X_zero := fun _ => rfl
      rightCont := fun _ _ => continuousWithinAt_const
      leftLim := fun _ _ _ => ⟨0, tendsto_const_nhds⟩
      noPosJumps := by
        intro ω t l ht h
        haveI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
        exact (tendsto_nhds_unique h tendsto_const_nhds).symm.le
      adapted := fun _ => measurable_const
      indepIncrements := fun _ _ _ => ProbabilityTheory.indep_bot_right _
      stationaryIncrements := by
        intro s t _
        simp only [sub_self]
        exact ProbabilityTheory.IdentDistrib.refl aemeasurable_const
      laplace := by
        intro t θ _
        refine ⟨integrable_const _, ?_⟩
        simp [laplaceExponent] }
  -- one dividend of size 1 at time ω + 1/2
  let D : ℝ≥0 → S107W.{0} → ℝ := fun t ω => if (ω.n : ℝ) + 1 / 2 ≤ (t : ℝ) then 1 else 0
  have hDf : ∀ ω (t : ℝ), D t.toNNReal ω = if (ω.n : ℝ) + 1 / 2 ≤ t then 1 else 0 := by
    intro ω t
    have h0 : (0:ℝ) < (ω.n : ℝ) + 1 / 2 := by positivity
    have hiff : (ω.n : ℝ) + 1 / 2 ≤ ((t.toNNReal : ℝ≥0) : ℝ) ↔ (ω.n : ℝ) + 1 / 2 ≤ t := by
      by_cases ht : 0 ≤ t
      · rw [Real.coe_toNNReal t ht]
      · rw [Real.toNNReal_of_nonpos (by linarith)]
        constructor <;> intro h <;> simp at h <;> linarith
    exact if_congr hiff rfl rfl
  have hmono : ∀ ω, Monotone (fun t : ℝ => D t.toNNReal ω) := by
    intro ω a b hab
    simp only [hDf]
    split_ifs with h1 h2 <;> first | exact absurd (h1.trans hab) h2 | exact le_rfl | norm_num
  have hμ : ∀ ω, dividendMeasure D ω = (hmono ω).stieltjesFunction.measure := by
    intro ω; unfold dividendMeasure; rw [dif_pos (hmono ω)]
  -- right limits away from the jump
  have hRL : ∀ ω (a : ℝ) (c : ℝ), (∀ᶠ t in 𝓝[>] a, D t.toNNReal ω = c) →
      (hmono ω).stieltjesFunction a = c := by
    intro ω a c h
    rw [Monotone.stieltjesFunction_eq]
    exact rightLim_eq_of_tendsto (tendsto_const_nhds.congr' (h.mono fun _ h => h.symm))
  have hR_low : ∀ ω (a : ℝ), a < (ω.n : ℝ) + 1 / 2 → (hmono ω).stieltjesFunction a = 0 := by
    intro ω a ha
    refine hRL ω a 0 ?_
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    rw [hDf, if_neg (not_le.2 ht.2)]
  have hR_high : ∀ ω (a : ℝ), (ω.n : ℝ) + 1 / 2 ≤ a → (hmono ω).stieltjesFunction a = 1 := by
    intro ω a ha
    refine hRL ω a 1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hDf, if_pos (ha.trans (le_of_lt ht))]
  -- no ruin
  have hruin : ∀ ω, ruinTime X 2 D ω = ⊤ := by
    intro ω
    unfold ruinTime
    refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun h => ?_
    exfalso
    simp only [riskProcess, X, D] at h
    split_ifs at h <;> linarith
  have hint : ∀ ω (S : Set ℝ), (∫⁻ t in S, ENNReal.ofReal (Real.exp (-((0:ℝ) * t)))
      ∂(dividendMeasure D ω)) = dividendMeasure D ω S := by
    intro ω S
    simp only [zero_mul, neg_zero, Real.exp_zero, ENNReal.ofReal_one]
    rw [setLIntegral_one]
  have key := H X 0 2 D 0 (fun n => by
    refine le_of_eq (S107NH.bot_lintegral P _ ⟨n⟩ ?_)
    simp only [hint, hruin, min_eq_right le_top]
    rw [hμ]
    refine le_antisymm ?_ bot_le
    calc (hmono ⟨n⟩).stieltjesFunction.measure (paymentTimes (n : ℝ≥0∞))
        ≤ (hmono ⟨n⟩).stieltjesFunction.measure (Ioc (-1) (n : ℝ)) := by
          refine measure_mono fun t ht => ⟨by linarith [ht.1], ?_⟩
          rcases ht.2 with h | h
          · rw [h]; exact Nat.cast_nonneg n
          · have : ENNReal.ofReal t < ENNReal.ofReal (n : ℝ) := by simpa using h
            exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1).1 this).le
      _ = 0 := by
          rw [StieltjesFunction.measure_Ioc, hR_low _ _ (by simp), hR_low _ _ (by
            simp only; linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n])]
          simp)
  have hlow : (1 : ℝ≥0∞) ≤ dividendValue X 0 2 D := by
    unfold dividendValue
    calc (1 : ℝ≥0∞) = ∫⁻ _ : S107W.{0}, 1 ∂P := by simp [P]
      _ ≤ _ := by
        refine lintegral_mono fun ω => ?_
        rw [hint, hruin, hμ]
        calc (1 : ℝ≥0∞) = (hmono ω).stieltjesFunction.measure
              (Ioc (ω.n : ℝ) ((ω.n : ℝ) + 1)) := by
              rw [StieltjesFunction.measure_Ioc, hR_high _ _ (by linarith),
                hR_low _ _ (by linarith)]
              simp
          _ ≤ _ := by
              have hn0 : (0:ℝ) ≤ ω.n := Nat.cast_nonneg _
              refine measure_mono fun t ht => ⟨by linarith [ht.1], Or.inr ENNReal.ofReal_lt_top⟩
  have := hlow.trans key
  exact absurd this (by norm_num)
