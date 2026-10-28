-- Prove2me | solution 1 for AvramDividend.Classical.levy_positive_root_exact_strict_upcrossing_discount
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:31:10.969266+00:00
-- url     : https://prove2.me/submissions/6bc20bd7-a773-4d0d-8e6e-2a4583025c7d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_moment_one
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_expectation_of_ae_convergence
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_reserve_time_measurable
import Mathlib

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace AV3Exact

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

noncomputable def clk (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / ((n : ℝ≥0) + 1)

lemma clk_coe (n k : ℕ) : ((clk n k : ℝ≥0) : ℝ) = (k : ℝ) / ((n : ℝ) + 1) := by
  simp [clk]

lemma clk_mono (n : ℕ) : Monotone (clk n) := by
  intro a b hab
  rw [← NNReal.coe_le_coe, clk_coe, clk_coe]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hab) (by positivity)

lemma clk_zero (n : ℕ) : clk n 0 = 0 := by simp [clk]

lemma clk_cap (N n : ℕ) : clk n (N * (n + 1)) = (N : ℝ≥0) := by
  rw [← NNReal.coe_inj, clk_coe]; push_cast; field_simp

lemma T_le_of_gt (X : SpectrallyNegativeLevy P 𝓕) (z : ℝ) (ω : Ω) (t : ℝ≥0)
    (h : z < X.X t ω) : twoSidedExitUpTimeCorrected X z ω ≤ (t : ℝ≥0∞) :=
  by unfold twoSidedExitUpTimeCorrected; exact iInf₂_le t h

lemma le_of_lt_T (X : SpectrallyNegativeLevy P 𝓕) (z : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < twoSidedExitUpTimeCorrected X z ω) : X.X t ω ≤ z := by
  by_contra h
  push Not at h
  exact absurd (lt_of_le_of_lt (T_le_of_gt X z ω t h) ht) (lt_irrefl _)

lemma le_of_not_lt_N (X : SpectrallyNegativeLevy P 𝓕) (z : ℝ) (hz : 0 < z) (N : ℕ) (ω : Ω)
    (hTN : ¬ twoSidedExitUpTimeCorrected X z ω < (N : ℝ≥0∞)) :
    ∀ t : ℝ≥0, t ≤ (N : ℝ≥0) → X.X t ω ≤ z := by
  intro t ht
  by_contra h
  push Not at h
  have h1 := T_le_of_gt X z ω t h
  have h2 : twoSidedExitUpTimeCorrected X z ω = (t : ℝ≥0∞) :=
    le_antisymm h1 (le_trans (by exact_mod_cast ht) (not_lt.1 hTN))
  have := firstUpcrossing_value_eq_threshold X z hz.le ω t h2.symm
  linarith

/-- pathwise convergence of the capped grid functional -/
lemma pathwise (X : SpectrallyNegativeLevy P 𝓕) (z : ℝ) (hz : 0 < z) (φ : ℝ) (N : ℕ) (ω : Ω) :
    Tendsto (fun n : ℕ =>
      let K := hittingBtwn (fun k η => X.X (clk n k) η) (Ioi z) 0 (N * (n + 1)) ω
      Real.exp (φ * X.X (clk n K) ω - (clk n K : ℝ) * X.ψ φ)) atTop
      (𝓝 (if twoSidedExitUpTimeCorrected X z ω < (N : ℝ≥0∞) then
          Real.exp (φ * z - (twoSidedExitUpTimeCorrected X z ω).toReal * X.ψ φ)
        else Real.exp (φ * X.X (N : ℝ≥0) ω - (N : ℝ) * X.ψ φ))) := by
  set T := twoSidedExitUpTimeCorrected X z ω with hTdef
  by_cases hTN : T < (N : ℝ≥0∞)
  · rw [if_pos hTN]
    have hTtop : T ≠ ⊤ := ne_top_of_lt hTN
    set τ : ℝ≥0 := T.toNNReal with hτ
    have hTτ : T = (τ : ℝ≥0∞) := (ENNReal.coe_toNNReal hTtop).symm
    have hXτ : X.X τ ω = z := firstUpcrossing_value_eq_threshold X z hz.le ω τ hTτ.symm
    have hτN : τ < (N : ℝ≥0) := by
      have : (τ : ℝ≥0∞) < ((N : ℝ≥0) : ℝ≥0∞) := by rw [← hTτ]; simpa using hTN
      exact_mod_cast this
    have key : ∀ b : ℝ≥0, τ < b → ∀ᶠ n : ℕ in atTop,
        τ ≤ clk n (hittingBtwn (fun k η => X.X (clk n k) η) (Ioi z) 0 (N * (n + 1)) ω) ∧
        clk n (hittingBtwn (fun k η => X.X (clk n k) η) (Ioi z) 0 (N * (n + 1)) ω) < b := by
      intro b hb
      set b' := min b (N : ℝ≥0) with hb'
      have hτb' : τ < b' := lt_min hb hτN
      have hTb' : T < (b' : ℝ≥0∞) := by rw [hTτ]; exact_mod_cast hτb'
      obtain ⟨t, ht⟩ := iInf_lt_iff.1 hTb'
      obtain ⟨hzt, htb⟩ := iInf_lt_iff.1 ht
      have htb' : t < b' := by exact_mod_cast htb
      have hmem : (fun s => X.X s ω) ⁻¹' Ioi z ∈ 𝓝[≥] t :=
        (X.rightCont ω t) (isOpen_Ioi.mem_nhds hzt)
      obtain ⟨u, hu, hIco⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hmem
      set u' := min u b' with hu'
      have htu' : t < u' := lt_min hu htb'
      have hpos : (0 : ℝ) < (u' : ℝ) - t := by
        have : (t : ℝ) < u' := by exact_mod_cast htu'
        linarith
      obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / ((u' : ℝ) - t))
      refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hsmall : 1 / ((n : ℝ) + 1) < (u' : ℝ) - t := by
        rw [div_lt_iff₀ hn1]
        rw [div_lt_iff₀ hpos] at hn₀
        have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      set k := ⌈(t : ℝ) * ((n : ℝ) + 1)⌉₊ with hk
      have hk1 : (t : ℝ) * ((n : ℝ) + 1) ≤ k := Nat.le_ceil _
      have hk2 : (k : ℝ) < (t : ℝ) * ((n : ℝ) + 1) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hclk_ge : t ≤ clk n k := by
        rw [← NNReal.coe_le_coe, clk_coe, le_div_iff₀ hn1]; exact hk1
      have hclk_lt : clk n k < u' := by
        rw [← NNReal.coe_lt_coe, clk_coe, div_lt_iff₀ hn1]
        rw [div_lt_iff₀ hn1] at hsmall
        nlinarith
      have hXk : X.X (clk n k) ω ∈ Ioi z := hIco ⟨hclk_ge, lt_of_lt_of_le hclk_lt (min_le_left _ _)⟩
      have hkm : k ≤ N * (n + 1) := by
        have h1 : clk n k < (N : ℝ≥0) :=
          lt_of_lt_of_le hclk_lt ((min_le_right _ _).trans (min_le_right _ _))
        rw [← NNReal.coe_lt_coe, clk_coe, div_lt_iff₀ hn1] at h1
        have : (k : ℝ) < ((N * (n + 1) : ℕ) : ℝ) := by push_cast; simpa using h1
        exact_mod_cast this.le
      have hKle := hittingBtwn_le_of_mem (u := fun k η => X.X (clk n k) η) (s := Ioi z)
        (ω := ω) (Nat.zero_le k) hkm hXk
      have hKmem : X.X (clk n (hittingBtwn (fun k η => X.X (clk n k) η) (Ioi z) 0
          (N * (n + 1)) ω)) ω ∈ Ioi z :=
        hittingBtwn_mem_set (u := fun k η => X.X (clk n k) η) ⟨k, ⟨Nat.zero_le k, hkm⟩, hXk⟩
      refine ⟨?_, ?_⟩
      · have : T ≤ _ := T_le_of_gt X z ω _ hKmem
        rw [hTτ] at this; exact_mod_cast this
      · exact lt_of_le_of_lt (clk_mono n hKle)
          (lt_of_lt_of_le hclk_lt ((min_le_right _ _).trans (min_le_left _ _)))
    have hc : Tendsto (fun n : ℕ =>
        clk n (hittingBtwn (fun k η => X.X (clk n k) η) (Ioi z) 0 (N * (n + 1)) ω))
        atTop (𝓝[≥] τ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩, ?_⟩
      · exact (key (τ + 1) (by simp)).mono fun n h => lt_of_lt_of_le ha h.1
      · exact (key b hb).mono fun n h => h.2
      · exact (key (τ + 1) (by simp)).mono fun n h => h.1
    have hX : Tendsto (fun n : ℕ => X.X (clk n (hittingBtwn (fun k η => X.X (clk n k) η)
        (Ioi z) 0 (N * (n + 1)) ω)) ω) atTop (𝓝 (X.X τ ω)) :=
      (X.rightCont ω τ).tendsto.comp hc
    have hcR : Tendsto (fun n : ℕ => ((clk n (hittingBtwn (fun k η => X.X (clk n k) η)
        (Ioi z) 0 (N * (n + 1)) ω) : ℝ≥0) : ℝ)) atTop (𝓝 (τ : ℝ)) :=
      (NNReal.continuous_coe.tendsto τ).comp (tendsto_nhdsWithin_iff.1 hc).1
    have := (Real.continuous_exp.tendsto _).comp ((hX.const_mul φ).sub (hcR.mul_const (X.ψ φ)))
    rw [hXτ] at this
    have hTr : T.toReal = (τ : ℝ) := by rw [hTτ]; rfl
    rw [hTr]
    exact this
  · rw [if_neg hTN]
    have hle : ∀ t : ℝ≥0, t ≤ (N : ℝ≥0) → X.X t ω ≤ z := by
      intro t ht
      by_contra h
      push Not at h
      have h1 := T_le_of_gt X z ω t h
      have h2 : T = (t : ℝ≥0∞) := le_antisymm h1 (le_trans (by exact_mod_cast ht) (not_lt.1 hTN))
      have := firstUpcrossing_value_eq_threshold X z hz.le ω t h2.symm
      linarith
    have hK : ∀ n : ℕ, hittingBtwn (fun k η => X.X (clk n k) η) (Ioi z) 0 (N * (n + 1)) ω
        = N * (n + 1) := by
      intro n
      rw [hittingBtwn_def]; dsimp only; rw [if_neg]
      rintro ⟨j, hj, hjs⟩
      have : clk n j ≤ (N : ℝ≥0) := by rw [← clk_cap N n]; exact clk_mono n hj.2
      exact absurd (hle _ this) (not_le.2 hjs)
    simp only [hK, clk_cap]
    simp


lemma ge_part (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 < z) :
    ENNReal.ofReal (Real.exp (-(φ * z))) ≤
    (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
       then ENNReal.ofReal
         (Real.exp (-(q * ENNReal.toReal
           (twoSidedExitUpTimeCorrected X z ω))))
       else 0 ∂P) := by
  have := X.isProbability
  set I := (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
       then ENNReal.ofReal
         (Real.exp (-(q * ENNReal.toReal
           (twoSidedExitUpTimeCorrected X z ω))))
       else 0 ∂P) with hI
  have hN : ∀ N : ℕ, 1 ≤ ENNReal.ofReal (Real.exp (φ * z)) * I +
      ENNReal.ofReal (Real.exp (φ * z - (N : ℝ) * q)) := by
    intro N
    let H : ℕ → Filtration ℕ mΩ := fun n =>
      ⟨fun k => 𝓕 (clk n k), fun a b h => 𝓕.mono (clk_mono n h), fun k => 𝓕.le _⟩
    let Z : Ω → ℝ := fun ω => if twoSidedExitUpTimeCorrected X z ω < (N : ℝ≥0∞) then
          Real.exp (φ * z - (twoSidedExitUpTimeCorrected X z ω).toReal * X.ψ φ)
        else Real.exp (φ * X.X (N : ℝ≥0) ω - (N : ℝ) * X.ψ φ)
    have hmeas : ∀ n : ℕ, Measurable (fun ω =>
        let K := hittingBtwn (fun k η => X.X (clk n k) η) (Ioi z) 0 (N * (n + 1)) ω
        Real.exp (φ * X.X (clk n K) ω - (clk n K : ℝ) * X.ψ φ)) := by
      intro n
      obtain ⟨h1, h2⟩ := levy_upper_grid_stopped_reserve_time_measurable X (clk n) (H n)
        (fun k => rfl) z (N * (n + 1))
        (fun ω => hittingBtwn (fun k η => X.X (clk n k) η) (Ioi z) 0 (N * (n + 1)) ω)
        (fun ω => rfl)
      exact Real.measurable_exp.comp ((h1.const_mul φ).sub (h2.mul_const _))
    have hZm : AEStronglyMeasurable Z P :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hmeas n).aestronglyMeasurable)
        (ae_of_all _ (fun ω => pathwise X z hz φ N ω))
    obtain ⟨hZi, hlim⟩ := levy_capped_upper_grid_exp_expectation_of_ae_convergence X
      clk clk_mono clk_zero H (fun n k => rfl) φ hφ.le z (fun n => N * (n + 1)) (N : ℝ≥0)
      (fun n => (clk_cap N n).le) Z hZm (ae_of_all _ (fun ω => pathwise X z hz φ N ω))
    have hone : ∀ n : ℕ, (∫ ω,
        (let K := hittingBtwn (fun k η => X.X (clk n k) η) (Ioi z) 0 (N * (n + 1)) ω
        Real.exp (φ * X.X (clk n K) ω - (clk n K : ℝ) * X.ψ φ)) ∂P) = 1 := fun n =>
      levy_capped_upper_grid_exp_moment_one X (clk n) (clk_mono n) (clk_zero n) (H n)
        (fun k => rfl) φ hφ.le z (N * (n + 1))
    simp only [hone] at hlim
    have hZ1 : ∫ ω, Z ω ∂P = 1 := tendsto_nhds_unique hlim tendsto_const_nhds
    have hZnn : ∀ ω, 0 ≤ Z ω := by
      intro ω; simp only [Z]; split_ifs <;> positivity
    have hL : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hZi (ae_of_all _ hZnn), hZ1]; simp
    rw [← hL]
    calc ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (φ * z)) *
            (if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
              then ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
                (twoSidedExitUpTimeCorrected X z ω)))) else 0) +
            ENNReal.ofReal (Real.exp (φ * z - (N : ℝ) * q))) ∂P := by
          apply lintegral_mono
          intro ω
          simp only [Z]
          by_cases hTN : twoSidedExitUpTimeCorrected X z ω < (N : ℝ≥0∞)
          · rw [if_pos hTN, if_pos (lt_of_lt_of_le hTN le_top)]
            refine le_trans (le_of_eq ?_) le_self_add
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hroot]
            ring_nf
          · rw [if_neg hTN]
            refine le_trans ?_ le_add_self
            apply ENNReal.ofReal_le_ofReal
            apply Real.exp_le_exp.2
            have := le_of_not_lt_N X z hz N ω hTN (N : ℝ≥0) le_rfl
            rw [hroot]; nlinarith
      _ = ENNReal.ofReal (Real.exp (φ * z)) * I +
            ENNReal.ofReal (Real.exp (φ * z - (N : ℝ) * q)) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const, measure_univ, mul_one]
  have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (Real.exp (φ * z)) * I +
      ENNReal.ofReal (Real.exp (φ * z - (N : ℝ) * q))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (φ * z)) * I + 0)) := by
    refine tendsto_const_nhds.add ?_
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    apply Real.tendsto_exp_atBot.comp
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) * q) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hq
    have h2 := tendsto_atBot_add_const_left atTop (φ * z) (tendsto_neg_atTop_atBot.comp h1)
    refine h2.congr (fun N => ?_)
    simp only [Function.comp]; ring
  have h1 : 1 ≤ ENNReal.ofReal (Real.exp (φ * z)) * I := by
    simpa using ge_of_tendsto' hlim hN
  calc ENNReal.ofReal (Real.exp (-(φ * z)))
      = ENNReal.ofReal (Real.exp (-(φ * z))) * 1 := by simp
    _ ≤ ENNReal.ofReal (Real.exp (-(φ * z))) * (ENNReal.ofReal (Real.exp (φ * z)) * I) := by
        gcongr
    _ = I := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        simp

end AV3Exact

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 < z) :
    (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
       then ENNReal.ofReal
         (Real.exp (-(q * ENNReal.toReal
           (twoSidedExitUpTimeCorrected X z ω))))
       else 0 ∂P) =
    ENNReal.ofReal (Real.exp (-(φ * z))) :=
  le_antisymm
    (levy_positive_root_unrestricted_upcrossing_discount_bound X q hq φ hφ hroot z hz.le)
    (AV3Exact.ge_part X q hq φ hφ hroot z hz)
