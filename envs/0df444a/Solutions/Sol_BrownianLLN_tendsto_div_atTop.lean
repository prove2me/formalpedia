-- Prove2me | solution 1 for BrownianLLN.tendsto_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:31:53.276205+00:00
-- url     : https://prove2.me/submissions/ade6f8ae-7bd8-4f1a-a5dd-e00cf74c03e8

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace BMLLNAux

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Exceedance of level `ε` on a finite set of times. -/
def exc (X : ℝ≥0 → Ω → ℝ) (F : Finset ℝ≥0) (ε : ℝ) : Set Ω := {ω | ∃ s : F, ε < |F.restrict (X · ω) s|}

theorem exc_eq {X Y : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (F : Finset ℝ≥0) (ε : ℝ) : P (exc X F ε) = P (exc Y F ε) := by
  have hm : MeasurableSet {f : F → ℝ | ∃ s : F, ε < |f s|} := by
    have : {f : F → ℝ | ∃ s : F, ε < |f s|} = ⋃ s : F, {f | ε < |f s|} := by ext; simp
    rw [this]
    exact MeasurableSet.iUnion fun s => measurableSet_lt measurable_const (measurable_pi_apply s).abs
  have h1 := (hX.hasLaw F).measure_eq hm
  have h2 := (hY.hasLaw F).measure_eq hm
  unfold exc
  rw [h1, h2]

theorem exc_null {X : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X P) (F : Finset ℝ≥0) (ε : ℝ) :
    NullMeasurableSet (exc X F ε) P := by
  have : exc X F ε = ⋃ s : F, {ω | ε < |X s ω|} := by ext; simp [exc]
  rw [this]
  exact NullMeasurableSet.iUnion fun s =>
    nullMeasurableSet_lt aemeasurable_const (hX.aemeasurable s).abs

/-- Finite approximations of the positive rationals below `δ`. -/
noncomputable def Fin_ (q : ℕ → ℚ) (δ : ℝ≥0) (n : ℕ) : Finset ℝ≥0 :=
  ((Finset.range n).image (fun k => ((q k : ℝ)).toNNReal)).filter (fun s => 0 < s ∧ s < δ)

theorem Fin_mono (q : ℕ → ℚ) (δ : ℝ≥0) : Monotone (Fin_ q δ) := by
  intro n m hnm
  unfold Fin_
  apply Finset.filter_subset_filter
  apply Finset.image_subset_image
  exact Finset.range_subset_range.mpr hnm

theorem Fin_anti (q : ℕ → ℚ) (n : ℕ) {δ δ' : ℝ≥0} (h : δ ≤ δ') : Fin_ q δ n ⊆ Fin_ q δ' n := by
  intro s hs
  simp only [Fin_, Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, hs.2.1, lt_of_lt_of_le hs.2.2 h⟩

/-- Exceedance on the positive rationals below `δ`. -/
def excD (X : ℝ≥0 → Ω → ℝ) (q : ℕ → ℚ) (δ : ℝ≥0) (ε : ℝ) : Set Ω := ⋃ n, exc X (Fin_ q δ n) ε

theorem exc_mono {X : ℝ≥0 → Ω → ℝ} {F G : Finset ℝ≥0} (h : F ⊆ G) (ε : ℝ) :
    exc X F ε ⊆ exc X G ε := by
  rintro ω ⟨⟨s, hs⟩, h1⟩
  exact ⟨⟨s, h hs⟩, h1⟩

theorem excD_eq {X Y : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X P) (hY : IsPreBrownianReal Y P)
    (q : ℕ → ℚ) (δ : ℝ≥0) (ε : ℝ) : P (excD X q δ ε) = P (excD Y q δ ε) := by
  unfold excD
  have mX : Monotone fun n => exc X (Fin_ q δ n) ε := fun n m h => exc_mono (Fin_mono q δ h) ε
  have mY : Monotone fun n => exc Y (Fin_ q δ n) ε := fun n m h => exc_mono (Fin_mono q δ h) ε
  rw [mX.measure_iUnion, mY.measure_iUnion]
  simp_rw [exc_eq hX hY]

theorem excD_null {X : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X P) (q : ℕ → ℚ) (δ : ℝ≥0) (ε : ℝ) :
    NullMeasurableSet (excD X q δ ε) P :=
  NullMeasurableSet.iUnion fun n => exc_null hX _ ε

theorem excD_anti {X : ℝ≥0 → Ω → ℝ} (q : ℕ → ℚ) (ε : ℝ) {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    excD X q δ ε ⊆ excD X q δ' ε :=
  Set.iUnion_mono fun n => exc_mono (Fin_anti q n h) ε

/-- For a Brownian motion, exceedances near time `0` have vanishing probability. -/
theorem iInter_excD_null {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (q : ℕ → ℚ) {ε : ℝ}
    (hε : 0 < ε) : P (⋂ n : ℕ, excD B q (1 / (n + 1)) ε) = 0 := by
  apply measure_mono_null _ (measure_eq_zero_iff_ae_notMem.mpr ?_)
  · exact {ω | ¬ Tendsto (B · ω) (𝓝 0) (𝓝 0)}
  · intro ω hω
    simp only [Set.mem_setOf_eq]
    intro hT
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ≥0), |B s ω| < ε := by
      have := hT.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
      filter_upwards [this] with s hs
      simpa [Real.dist_eq] using hs
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨η, hη, hball⟩ := hev
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
    have hmem := Set.mem_iInter.mp hω n
    obtain ⟨k, ⟨⟨s, hs⟩, hgt⟩⟩ := Set.mem_iUnion.mp hmem
    simp only [Fin_, Finset.mem_filter] at hs
    have hs2 : (s : ℝ) < 1 / (n + 1) := by
      have := hs.2.2
      have h' : ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) = 1 / ((n : ℝ) + 1) := by push_cast; ring
      rw [← h']; exact_mod_cast this
    have hd : dist s 0 < η := by
      rw [NNReal.dist_eq]; simp only [NNReal.coe_zero, sub_zero]
      rw [abs_of_nonneg (NNReal.coe_nonneg s)]
      linarith
    have := hball hd
    simp only [Finset.restrict] at hgt
    linarith
  · filter_upwards [hB.tendsto_nhds_zero] with ω hω
    simpa using hω


theorem coe_inv_succ (n : ℕ) : ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) = 1 / ((n : ℝ) + 1) := by
  push_cast; ring

end BMLLNAux

open BMLLNAux

/-- **Law of large numbers for Brownian motion**: `B_t / t → 0` almost surely. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => B t ω / t) atTop (𝓝 0) := by
  obtain ⟨q, hq⟩ := exists_surjective_nat ℚ
  set W : ℝ≥0 → Ω → ℝ := fun t ω => (t : ℝ) * B (1 / t) ω with hWdef
  have hW : IsPreBrownianReal W P := hB.toIsPreBrownianReal.inv
  -- the bad events for `W` are null
  have hnull : ∀ m : ℕ, P (⋂ n : ℕ, excD W q (1 / (n + 1)) (1 / ((m : ℝ) + 1))) = 0 := by
    intro m
    set ε : ℝ := 1 / ((m : ℝ) + 1) with hε
    have hεpos : 0 < ε := by positivity
    have hanti : Antitone fun n : ℕ => excD B q (1 / ((n : ℝ≥0) + 1)) ε := by
      intro n k hnk
      apply excD_anti
      gcongr
    have hB0 := iInter_excD_null hB q hεpos
    have hinf : P (⋂ n : ℕ, excD B q (1 / ((n : ℝ≥0) + 1)) ε) =
        ⨅ n : ℕ, P (excD B q (1 / ((n : ℝ≥0) + 1)) ε) :=
      hanti.measure_iInter (fun n => excD_null hB.toIsPreBrownianReal q _ ε)
        ⟨0, measure_ne_top _ _⟩
    apply le_antisymm _ (zero_le)
    rw [← hB0, hinf]
    refine le_iInf fun n => ?_
    rw [← excD_eq hW hB.toIsPreBrownianReal q _ ε]
    exact measure_mono (Set.iInter_subset _ n)
  have hgood : ∀ᵐ ω ∂P, ∀ m : ℕ, ω ∉ ⋂ n : ℕ, excD W q (1 / (n + 1)) (1 / ((m : ℝ) + 1)) :=
    ae_all_iff.mpr fun m => measure_eq_zero_iff_ae_notMem.mp (hnull m)
  filter_upwards [hgood, hB.cont] with ω hω hcont
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  have hωm := hω m
  rw [Set.mem_iInter, not_forall] at hωm
  obtain ⟨n, hn⟩ := hωm
  -- `W` stays below `1/(m+1)` on `(0, 1/(n+1))`
  have hbound : ∀ s : ℝ≥0, 0 < s → (s : ℝ) < 1 / ((n : ℝ) + 1) →
      |W s ω| ≤ 1 / ((m : ℝ) + 1) := by
    intro s hs hsδ
    by_contra hgt
    push Not at hgt
    have hcW : ContinuousAt (fun s' : ℝ≥0 => |W s' ω|) s := by
      have h1 : ContinuousAt (fun s' : ℝ≥0 => s'⁻¹) s := continuousAt_inv₀ hs.ne'
      have h2 : ContinuousAt (fun s' : ℝ≥0 => B (1 / s') ω) s := by
        simp_rw [one_div]
        exact hcont.continuousAt.comp h1
      exact ((NNReal.continuous_coe.continuousAt).mul h2).abs
    have hev := hcW.eventually (lt_mem_nhds hgt)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨η, hη, hball⟩ := hev
    have hlt : (s : ℝ) < min ((s : ℝ) + η) (1 / ((n : ℝ) + 1)) := lt_min (by linarith) hsδ
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
    obtain ⟨k, hk⟩ := hq r
    set s' : ℝ≥0 := ((r : ℝ)).toNNReal with hs'
    have hrpos : (0 : ℝ) < r := lt_of_le_of_lt (NNReal.coe_nonneg s) hr1
    have hs'r : (s' : ℝ) = r := Real.coe_toNNReal _ hrpos.le
    have hd : dist s' s < η := by
      rw [NNReal.dist_eq, hs'r, abs_of_pos (by linarith)]
      have := min_le_left ((s : ℝ) + η) (1 / ((n : ℝ) + 1))
      linarith
    have hW' := hball hd
    apply hn
    refine Set.mem_iUnion.mpr ⟨k + 1, ⟨⟨s', ?_⟩, ?_⟩⟩
    · simp only [Fin_, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      refine ⟨⟨k, by omega, by rw [hk]⟩, ?_, ?_⟩
      · rw [hs']; exact Real.toNNReal_pos.mpr hrpos
      · rw [← NNReal.coe_lt_coe, hs'r, coe_inv_succ]
        have := min_le_right ((s : ℝ) + η) (1 / ((n : ℝ) + 1))
        linarith
    · simpa [Finset.restrict] using hW'
  refine ⟨((n : ℝ≥0) + 2), fun t ht => ?_⟩
  have htpos : (0 : ℝ) < t := by
    have : (2 : ℝ≥0) ≤ t := le_trans (by simp) ht
    have : (2 : ℝ) ≤ t := by exact_mod_cast this
    linarith
  have htn : (n : ℝ) + 2 ≤ t := by exact_mod_cast ht
  have hs0 : (0 : ℝ≥0) < 1 / t := by
    have : (0 : ℝ≥0) < t := by exact_mod_cast htpos
    positivity
  have hsδ : ((1 / t : ℝ≥0) : ℝ) < 1 / ((n : ℝ) + 1) := by
    rw [NNReal.coe_div, NNReal.coe_one]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have := hbound (1 / t) hs0 hsδ
  have hWt : W (1 / t) ω = B t ω / t := by
    simp only [hWdef, one_div_one_div, NNReal.coe_div, NNReal.coe_one]
    field_simp
  rw [hWt] at this
  rw [Real.dist_eq, sub_zero]
  linarith
