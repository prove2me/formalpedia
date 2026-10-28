-- Prove2me | solution 1 for FracPSG.Abstract.lemma_5_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:15:48.282384+00:00
-- url     : https://prove2.me/submissions/e105c0ff-8cfb-4f72-a1cc-8fe071a06d00

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

open FracPSG.Abstract NonconvexSplitting.Shared NonconvexSplitting.ADMMKL in
theorem solution {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH3 : H3 h z) (hz₀ : h (z 0) ≠ ⊤)
    {a : ℝ} (ha : 0 < a) (hαa : ∀ n, a ≤ α n) :
    ∀ zbar ∈ omega0 h z,
      Summable (fun n : ℕ => Δ n ^ 2) ∧
      ∑' n : ℕ, Δ n ^ 2 ≤ ((h (z 0)).toReal - (h zbar).toReal) / a ∧
      Tendsto (fun n : ℕ => Δ n) atTop (𝓝 0) := by
  intro zbar hzbar
  have hbot : ∀ y, h y ≠ ⊥ := hset.proper.1
  have hαpos := hset.alpha_pos
  -- all values finite
  have htop : ∀ n, h (z n) ≠ ⊤ := by
    intro n
    induction n with
    | zero => exact hz₀
    | succ n ih =>
      intro htp
      have := hH1 n
      rw [htp, EReal.top_add_coe] at this
      exact ih (top_le_iff.mp this)
  set r : ℕ → ℝ := fun n => (h (z n)).toReal with hr
  have hcoe : ∀ n, h (z n) = (r n : EReal) := fun n => (EReal.coe_toReal (htop n) (hbot _)).symm
  have hstep : ∀ n, r (n + 1) + α n * Δ n ^ 2 ≤ r n := by
    intro n
    have := hH1 n
    rw [hcoe (n + 1), hcoe n, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    exact this
  have hanti : Antitone r := by
    apply antitone_nat_of_succ_le
    intro n
    have := hstep n
    have : 0 ≤ α n * Δ n ^ 2 := mul_nonneg (hαpos n).le (sq_nonneg _)
    linarith
  -- the limit value
  have hlim : Tendsto (fun n => h (z n)) atTop (𝓝 (h zbar)) := hzbar.2
  have hle : ∀ N, h zbar ≤ h (z N) := by
    intro N
    apply le_of_tendsto hlim
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    rw [hcoe n, hcoe N, EReal.coe_le_coe_iff]
    exact hanti hn
  have hzbartop : h zbar ≠ ⊤ := by
    intro htp
    have := hle 0
    rw [htp] at this
    exact htop 0 (top_le_iff.mp this)
  set rbar := (h zbar).toReal with hrbar
  have hcoebar : h zbar = (rbar : EReal) := (EReal.coe_toReal hzbartop (hbot _)).symm
  have hrle : ∀ N, rbar ≤ r N := by
    intro N
    have := hle N
    rw [hcoebar, hcoe N, EReal.coe_le_coe_iff] at this
    exact this
  -- telescoping
  have htel : ∀ N, a * ∑ n ∈ Finset.range N, Δ n ^ 2 ≤ r 0 - r N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add]
      have h1 := hstep N
      have h2 : a * Δ N ^ 2 ≤ α N * Δ N ^ 2 :=
        mul_le_mul_of_nonneg_right (hαa N) (sq_nonneg _)
      linarith
  have hbound : ∀ N, ∑ n ∈ Finset.range N, Δ n ^ 2 ≤ (r 0 - rbar) / a := by
    intro N
    rw [le_div_iff₀ ha, mul_comm]
    have := htel N
    have := hrle N
    linarith
  have hnn : ∀ n : ℕ, 0 ≤ Δ n ^ 2 := fun n => sq_nonneg _
  have hsum : Summable (fun n : ℕ => Δ n ^ 2) := summable_of_sum_range_le hnn hbound
  refine ⟨hsum, Real.tsum_le_of_sum_range_le hnn hbound, ?_⟩
  have hsq : Tendsto (fun n : ℕ => Δ n ^ 2) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (Δ n ^ 2)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at this
    exact this
  apply squeeze_zero_norm _ hsqrt
  intro n
  rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
