-- Prove2me | solution 1 for FBMStrongSim.RecordBreak.last_record_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:36:44.229273+00:00
-- url     : https://prove2.me/submissions/7b80f4b5-a31f-484d-be5b-c281e61dd888

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model
import Theorems.Thm_FBMStrongSim_RecordBreak_theorem_3_1

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace FBMBCAux
open FBMStrongSim.RecordBreak

/-- Real tail estimate: `e^{tk} · 2e^{-X} ≤ 2 e^{(t+1)^2/(4a)} (e^{-1})^k` when `X ≥ a k^2`. -/
theorem tail_real (t a : ℝ) (ha : 0 < a) (k : ℕ) (X : ℝ) (hX : a * (k : ℝ) ^ 2 ≤ X) :
    Real.exp (t * k) * (2 * Real.exp (-X))
      ≤ 2 * Real.exp ((t + 1) ^ 2 / (4 * a)) * Real.exp (-1) ^ k := by
  have hq : (t + 1) * k - a * (k : ℝ) ^ 2 ≤ (t + 1) ^ 2 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * k - (t + 1))]
  have h1 : Real.exp (t * k) * (2 * Real.exp (-X)) = 2 * Real.exp (t * k - X) := by
    rw [Real.exp_sub, Real.exp_neg]; field_simp
  have h2 : Real.exp (-1) ^ k = Real.exp (-(k : ℝ)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h1, h2, mul_assoc, ← Real.exp_add]
  gcongr
  nlinarith

/-- Lower bound `ν*² · 2^{2kδ-2} ≥ a k²` with `a = ν*² (2 log 2 · δ)² / 8`. -/
theorem quad_lower (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ) (k : ℕ) :
    c * (2 * Real.log 2 * δ) ^ 2 / 8 * (k : ℝ) ^ 2 ≤ c * (2 : ℝ) ^ (2 * (k : ℝ) * δ - 2) := by
  have hsplit : (2 : ℝ) ^ (2 * (k : ℝ) * δ - 2) = (2 : ℝ) ^ (2 * (k : ℝ) * δ) / 4 := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]; norm_num
  rw [hsplit, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  set z : ℝ := Real.log 2 * (2 * (k : ℝ) * δ) with hz
  have hz0 : 0 ≤ z := by
    rw [hz]; apply mul_nonneg (Real.log_nonneg (by norm_num)); positivity
  have he := Real.quadratic_le_exp_of_nonneg hz0
  have hzz : z ^ 2 = (2 * Real.log 2 * δ) ^ 2 * (k : ℝ) ^ 2 := by rw [hz]; ring
  have : z ^ 2 / 8 ≤ Real.exp z / 4 := by nlinarith
  calc c * (2 * Real.log 2 * δ) ^ 2 / 8 * (k : ℝ) ^ 2 = c * (z ^ 2 / 8) := by rw [hzz]; ring
    _ ≤ c * (Real.exp z / 4) := mul_le_mul_of_nonneg_left this hc

end FBMBCAux

open FBMStrongSim.RecordBreak FBMBCAux

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {H delta rho : ℝ} (hH0 : 0 < H) (hH1 : H < 1) (hdelta0 : 0 < delta)
    (hdeltaH : delta < H) (hrho : 0 < rho) {B : ℝ → Ω → ℝ} (hB : IsFBM H B P) :
    ∀ᵐ ω ∂P, lastRecord rho H delta (fun s => B s ω) < ⊤ := by
  set nu : ℝ := rho / 4 with hnudef
  have hnu : 0 < nu := by rw [hnudef]; linarith
  set K0 : ℕ := Knu nu delta with hK0
  set c : ℝ := nu ^ 2 with hc
  set a : ℝ := c * (2 * Real.log 2 * delta) ^ 2 / 8 with ha
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ha0 : 0 < a := by rw [ha, hc]; positivity
  set A : ℕ → Set Ω := fun k => {ω | rho * ell H delta k ≤ maxDisp (fun s => B s ω) k} with hAdef
  have hA : ∀ k : ℕ, K0 < k →
      P (A k) ≤ ENNReal.ofReal (2 * Real.exp (-c * (2 : ℝ) ^ (2 * (k : ℝ) * delta - 2))) := by
    intro k hk
    have h31 := FBMStrongSim.RecordBreak.theorem_3_1 hH0 hH1 hdelta0 hdeltaH hB hnu hnu hk
    have e : 2 * (nu + nu) = rho := by rw [hnudef]; ring
    rw [e] at h31
    exact h31
  set f : ℕ → ℝ := fun k => 2 * Real.exp ((0 + 1) ^ 2 / (4 * a)) * Real.exp (-1) ^ k with hfdef
  have hf0 : ∀ k, 0 ≤ f k := fun k => by rw [hfdef]; positivity
  have hsum : Summable f :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by norm_num))).mul_left _
  have hterm : ∀ k, K0 < k → P (A k) ≤ ENNReal.ofReal (f k) := by
    intro k hk
    refine le_trans (hA k hk) (ENNReal.ofReal_le_ofReal ?_)
    have := tail_real 0 a ha0 k _ (quad_lower c delta (by rw [hc]; positivity) hdelta0 k)
    simp only [zero_mul, Real.exp_zero, one_mul] at this
    rw [hfdef]
    simpa [neg_mul] using this
  have hfin : ∑' k, P (A k) ≠ ⊤ := by
    rw [← (ENNReal.summable).sum_add_tsum_nat_add' (k := K0 + 1)]
    · apply ENNReal.add_ne_top.2
      constructor
      · exact ENNReal.sum_ne_top.2 (fun k _ => measure_ne_top P _)
      · apply ne_top_of_le_ne_top (b := ∑' i, ENNReal.ofReal (f (i + (K0 + 1))))
        · rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hf0 _)
            ((summable_nat_add_iff (K0 + 1)).2 hsum)]
          exact ENNReal.ofReal_ne_top
        · exact ENNReal.tsum_le_tsum (fun i => hterm _ (by omega))
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  obtain ⟨M, hM⟩ := eventually_atTop.1 hω
  have hle : lastRecord rho H delta (fun s => B s ω) ≤ (M : ℕ∞) := by
    rw [lastRecord]
    refine iSup₂_le (fun k hk => ?_)
    have hkM : k < M := by
      by_contra hcon
      push Not at hcon
      exact hM k hcon hk.2
    exact_mod_cast hkM.le
  exact lt_of_le_of_lt hle (ENat.coe_lt_top M)
