-- Prove2me | solution 1 for Avram2004.Exit.mgf_eq_exp_psi
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:24:47.92785+00:00
-- url     : https://prove2.me/submissions/29bf5771-5803-4ddc-8a94-f57e696c8a69

import Mathlib
import Definitions.Def_Avram2004_Exit_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Exit

theorem aux_mgfpsi_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (θ : ℝ) (s u : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (s + u) ω)) ∂P =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P) *
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X u ω)) ∂P := by
  have hind : IndepFun (X s) (X (s + u) - X s) P :=
    hX.indep_increments.indepFun_eval_sub (zero_le (a := s)) le_self_add
      (Filter.Eventually.of_forall hX.start_zero)
  have hf : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x)) := by fun_prop
  have hind2 := hind.comp hf hf
  have h1 : (fun ω => ENNReal.ofReal (Real.exp (θ * X (s + u) ω))) =
      ((fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))) ∘ X s) *
        ((fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x))) ∘ (X (s + u) - X s)) := by
    ext ω
    simp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [h1, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hf.comp (hX.measurable s))
    (hf.comp ((hX.measurable _).sub (hX.measurable s))) hind2]
  congr 1
  exact ((hX.stationary_increments s u).comp hf).lintegral_eq


end Avram2004.Exit

open Avram2004 Avram2004.Exit
open scoped ENNReal

open Filter Topology in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsSNLevy P X) (hS : Shared.Standing P X)
    (t : ℝ≥0) (θ : ℝ) (hint : Integrable (fun ω => Real.exp (θ * X t ω)) P) :
    ∫ ω, Real.exp (θ * X t ω) ∂P = Real.exp ((t : ℝ) * Shared.psi P X θ) := by
  classical
  set G : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P with hGdef
  have hmeas : ∀ s, Measurable fun ω => ENNReal.ofReal (Real.exp (θ * X s ω)) := by
    intro s
    have := hX.measurable s
    fun_prop
  have hmul : ∀ s u, G (s + u) = G s * G u := aux_mgfpsi_mul P X hX θ
  have hpos : ∀ s, G s ≠ 0 := by
    intro s h
    rw [hGdef, lintegral_eq_zero_iff (hmeas s)] at h
    obtain ⟨ω, hω⟩ := h.exists
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hω
    exact absurd hω (not_le.2 (Real.exp_pos _))
  have hG0 : G 0 = 1 := by simp [G, hX.start_zero]
  have hint_eq : ∀ s, ∫ ω, Real.exp (θ * X s ω) ∂P = (G s).toReal := by
    intro s
    refine integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => (Real.exp_pos _).le)) ?_
    have := hX.measurable s
    exact (by fun_prop : Measurable fun ω => Real.exp (θ * X s ω)).aestronglyMeasurable
  have hpsi : Shared.psi P X θ = Real.log (G 1).toReal := by
    simp only [Shared.psi, cgf, mgf]
    rw [hint_eq 1]
  rcases eq_or_ne t 0 with rfl | ht0
  · simp [hX.start_zero]
  have hGt : G t ≠ ⊤ := hint.lintegral_lt_top.ne
  have hpow : ∀ n : ℕ, G (n * t) = G t ^ n := by
    intro n
    induction n with
    | zero => simp [hG0]
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℝ≥0) * t = n * t + t by push_cast; ring, hmul, ih, pow_succ]
  have hfin : ∀ s, G s ≠ ⊤ := by
    intro s hs
    obtain ⟨n, hn⟩ := exists_nat_ge (s / t)
    have hsn : s ≤ n * t := by
      rwa [div_le_iff₀ (pos_iff_ne_zero.2 ht0)] at hn
    have h := hmul s (n * t - s)
    rw [add_tsub_cancel_of_le hsn, hs, ENNReal.top_mul (hpos _), hpow] at h
    exact ENNReal.pow_ne_top hGt h
  set g : ℝ≥0 → ℝ := fun s => Real.log (G s).toReal with hgdef
  have hGpos : ∀ s, 0 < (G s).toReal := fun s => ENNReal.toReal_pos (hpos s) (hfin s)
  have hGg : ∀ s, (G s).toReal = Real.exp (g s) := fun s => (Real.exp_log (hGpos s)).symm
  have hgadd : ∀ s u, g (s + u) = g s + g u := by
    intro s u
    simp only [hgdef, hmul, ENNReal.toReal_mul]
    exact Real.log_mul (hGpos s).ne' (hGpos u).ne'
  have hg0 : g 0 = 0 := by simp [hgdef, hG0]
  have hgnat : ∀ n : ℕ, ∀ s, g (n * s) = n * g s := by
    intro n s
    induction n with
    | zero => simp [hg0]
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℝ≥0) * s = n * s + s by push_cast; ring, hgadd, ih]
      push_cast; ring
  have hgrid : ∀ k m : ℕ, g ((k : ℝ≥0) / ((m : ℝ≥0) + 1)) = ((k : ℝ) / ((m : ℝ) + 1)) * g 1 := by
    intro k m
    have h1 := hgnat (m + 1) ((k : ℝ≥0) / ((m : ℝ≥0) + 1))
    have h2 := hgnat k 1
    rw [show ((m + 1 : ℕ) : ℝ≥0) * ((k : ℝ≥0) / ((m : ℝ≥0) + 1)) = k by
      push_cast; field_simp] at h1
    rw [mul_one] at h2
    rw [h2] at h1
    push_cast at h1
    field_simp
    linarith
  have hup : ∀ s : ℝ≥0, g s ≤ s * g 1 := by
    intro s
    let sn : ℕ → ℝ≥0 := fun n => (⌈((n : ℝ≥0) + 1) * s⌉₊ : ℝ≥0) / ((n : ℝ≥0) + 1)
    have hsn_ge : ∀ n, s ≤ sn n := by
      intro n
      simp only [sn]
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact Nat.le_ceil _
    have hsn_le : ∀ n, sn n ≤ s + 1 / ((n : ℝ≥0) + 1) := by
      intro n
      have e : (s + 1 / ((n : ℝ≥0) + 1)) * ((n : ℝ≥0) + 1) = ((n : ℝ≥0) + 1) * s + 1 := by
        field_simp
      simp only [sn]
      rw [div_le_iff₀ (by positivity), e]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hsn_tend : Tendsto sn atTop (𝓝 s) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hsn_ge hsn_le
      have : Tendsto (fun n : ℕ => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
      simpa using tendsto_const_nhds.add this
    have hsn_within : Tendsto sn atTop (𝓝[Set.Ici s] s) :=
      tendsto_nhdsWithin_iff.2 ⟨hsn_tend, Eventually.of_forall hsn_ge⟩
    have hcont : Continuous fun x : ℝ => ENNReal.ofReal (Real.exp (θ * x)) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hptw : ∀ ω, Tendsto (fun n => ENNReal.ofReal (Real.exp (θ * X (sn n) ω))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (θ * X s ω)))) := by
      intro ω
      exact (hcont.tendsto _).comp ((hX.right_continuous ω s).tendsto.comp hsn_within)
    have hfatou := lintegral_liminf_le (μ := P) (u := atTop)
      (f := fun n ω => ENNReal.ofReal (Real.exp (θ * X (sn n) ω))) (fun n => hmeas _)
    simp_rw [(hptw _).liminf_eq] at hfatou
    have hGsn : ∀ n, G (sn n) = ENNReal.ofReal (Real.exp ((sn n : ℝ) * g 1)) := by
      intro n
      rw [← ENNReal.ofReal_toReal (hfin (sn n)), hGg]
      congr 2
      simp only [sn]
      rw [hgrid]
      push_cast
      ring
    have hlim : Tendsto (fun n => G (sn n)) atTop (𝓝 (ENNReal.ofReal (Real.exp (s * g 1)))) := by
      simp_rw [hGsn]
      have hc : Continuous fun x : ℝ≥0 => ENNReal.ofReal (Real.exp ((x : ℝ) * g 1)) :=
        ENNReal.continuous_ofReal.comp
          (Real.continuous_exp.comp (NNReal.continuous_coe.mul continuous_const))
      exact (hc.tendsto s).comp hsn_tend
    have hfatou' : G s ≤ ENNReal.ofReal (Real.exp (s * g 1)) := by
      rw [← hlim.liminf_eq]
      exact hfatou
    have := (ENNReal.toReal_le_toReal (hfin s) ENNReal.ofReal_ne_top).2 hfatou'
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, hGg] at this
    exact Real.exp_le_exp.1 this
  have hgt : g t = t * g 1 := by
    refine le_antisymm (hup t) ?_
    set N : ℝ≥0 := (⌈t⌉₊ : ℝ≥0) with hN
    have htN : t ≤ N := Nat.le_ceil t
    have h1 := hgadd t (N - t)
    rw [add_tsub_cancel_of_le htN] at h1
    have h2 := hup (N - t)
    have h3 : g N = N * g 1 := by
      have := hgnat ⌈t⌉₊ 1
      rw [mul_one] at this
      rw [hN, this]
      simp
    rw [NNReal.coe_sub htN] at h2
    nlinarith
  rw [hint_eq t, hGg, hgt, hpsi]
