-- Prove2me | solution 1 for CarbonPolicy.TaxVsCap.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:12:26.928002+00:00
-- url     : https://prove2.me/submissions/763cc253-e590-4b7f-a9bf-f77905e9f593

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting
set_option autoImplicit false
open ProbabilityTheory MeasureTheory
open CarbonPolicy.TaxVsCap

theorem kk_profit_q (b w γ a k : ℝ) (hb : 0 < b) :
    profit b w γ a k (qStar b γ a k) = (a - γ * k) ^ 2 / (4 * b) + w * k := by
  unfold profit qStar
  field_simp
  ring

theorem kk_int_sq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → ℝ) (ha : MemLp a 2 P) (c : ℝ) :
    ∫ ω, (a ω - c) ^ 2 ∂P = Var[a; P] + (∫ ω, a ω ∂P - c) ^ 2 := by
  have h1 : Integrable a P := ha.integrable (by norm_num)
  have h2 : Integrable (fun ω => a ω ^ 2) P := ha.integrable_sq
  have hv := variance_eq_sub ha
  have e : ∀ ω, (a ω - c) ^ 2 = a ω ^ 2 - 2 * c * a ω + c ^ 2 := fun ω => by ring
  simp_rw [e]
  have h3 : Integrable (fun ω => 2 * c * a ω) P := h1.const_mul _
  have h4 : Integrable (fun ω => a ω ^ 2 - 2 * c * a ω) P := h2.sub h3
  rw [integral_add h4 (integrable_const _), integral_sub h2 h3, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hv' : Var[a; P] = ∫ ω, a ω ^ 2 ∂P - (∫ ω, a ω ∂P) ^ 2 := by
    rw [hv]; simp [Pi.pow_apply]
  rw [hv']
  ring

theorem kk_int_main {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → ℝ) (ha : MemLp a 2 P) (c d b : ℝ) :
    ∫ ω, ((a ω - c) ^ 2 / (4 * b) + d) ∂P = (Var[a; P] + (∫ ω, a ω ∂P - c) ^ 2) / (4 * b) + d := by
  have hi : Integrable (fun ω => (a ω - c) ^ 2) P := (ha.sub (memLp_const c)).integrable_sq
  rw [integral_add (hi.div_const _) (integrable_const _), integral_div, kk_int_sq P a ha c]
  simp

theorem kk_moment_tax {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (γ : ℝ) :
    PiT M b β γp w γ =
      ((abar M.P M.a) - γ * (kbar M.P M.k)) ^ 2 / (4 * b) +
        (sigmaD M.P M.a) ^ 2 / (4 * b) - β * (γp - γ) ^ 2 + w * (kbar M.P M.k) := by
  haveI := M.prob
  unfold PiT
  simp_rw [kk_profit_q b w γ _ _ hb]
  have hs : sigmaD M.P M.a ^ 2 = Var[M.a; M.P] := by
    unfold sigmaD
    rw [Real.sq_sqrt (variance_nonneg _ _)]
  rw [hs, kk_int_main M.P M.a M.a_L2 (γ * kbar M.P M.k) (w * kbar M.P M.k) b]
  unfold abar
  ring


theorem solution {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (hγp : 0 < γp)
    (hA : Assumption1 M b β γp) :
    OptimalTax M b β γp w (gammaT0 b β γp (abar M.P M.a) (kbar M.P M.k)) ∧
    ∀ γ : ℝ, OptimalTax M b β γp w γ → γ = gammaT0 b β γp (abar M.P M.a) (kbar M.P M.k) := by
  haveI := M.prob
  obtain ⟨h1, h2, h3⟩ := hA
  have hk : 0 < kbar M.P M.k := M.kbar_pos
  have hs2 : 0 ≤ sigma M.P M.k ^ 2 := sq_nonneg _
  set k := kbar M.P M.k with hkdef
  set ā := abar M.P M.a with hadef
  have hD : 0 < 4 * b * β - k ^ 2 := by nlinarith
  have hN : ā * k < 4 * b * β * γp := lt_of_le_of_lt (le_max_left _ _) h2
  have hag : γp * k ≤ ā := by
    have i1 : Integrable M.a M.P := M.a_L2.integrable (by norm_num)
    have i2 : Integrable M.k M.P := M.k_L2.integrable (by norm_num)
    have := integral_mono_ae (i2.const_mul γp) i1 (h3.mono (fun ω h => h.le))
    rw [integral_const_mul] at this
    exact this
  set g0 := gammaT0 b β γp ā k with hg0
  have hg0e : g0 = (4 * b * β * γp - ā * k) / (4 * b * β - k ^ 2) := rfl
  have hg0mem : g0 ∈ Set.Icc (0 : ℝ) γp := by
    refine ⟨?_, ?_⟩
    · rw [hg0e]; exact div_nonneg (by linarith) hD.le
    · rw [hg0e, div_le_iff₀ hD]
      nlinarith
  have hform := kk_moment_tax M b β γp w hb
  have key : ∀ γ, PiT M b β γp w γ = PiT M b β γp w g0 - (4 * b * β - k ^ 2) / (4 * b) * (γ - g0) ^ 2 := by
    intro γ
    rw [hform γ, hform g0, hg0e]
    field_simp
    ring
  have hpos : 0 < (4 * b * β - k ^ 2) / (4 * b) := div_pos hD (by linarith)
  refine ⟨⟨hg0mem, ?_⟩, ?_⟩
  · intro γ _
    show PiT M b β γp w γ ≤ PiT M b β γp w g0
    rw [key γ]
    nlinarith [mul_nonneg hpos.le (sq_nonneg (γ - g0))]
  · rintro γ ⟨hγ, hmax⟩
    have h := hmax hg0mem
    have h' : PiT M b β γp w g0 ≤ PiT M b β γp w γ := h
    rw [key γ] at h'
    have : (4 * b * β - k ^ 2) / (4 * b) * (γ - g0) ^ 2 ≤ 0 := by linarith
    have h0 : (γ - g0) ^ 2 ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith [mul_pos hpos hc]
    nlinarith [sq_nonneg (γ - g0)]
