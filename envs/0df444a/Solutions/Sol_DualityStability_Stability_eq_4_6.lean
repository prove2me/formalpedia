-- Prove2me | solution 1 for DualityStability.Stability.eq_4_6
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:56:33.226797+00:00
-- url     : https://prove2.me/submissions/b0f813f1-7f14-44ef-aa4a-f57eb1ebab45

import Mathlib
import Definitions.Def_DualityStability_Stability_ConvexFunction
import Definitions.Def_DualityStability_Stability_StablySet

open Filter Set DualityStability.Stability
open scoped Topology

private lemma ereal_upper (a b : EReal) (h : ∀ r : ℝ, b < r → a ≤ r) : a ≤ b := by
  by_contra hab
  obtain ⟨r, hr, hr'⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hab)
  exact (not_le_of_gt hr') (h r hr)

private lemma quotient_le (v : EReal) (a t b : ℝ) (ht : 0 < t) :
    ((t⁻¹ : ℝ) : EReal) * (v - (a : EReal)) ≤ (b : EReal) ↔
      v ≤ ((a + t * b : ℝ) : EReal) := by
  induction v using EReal.rec with
  | bot => simp [EReal.coe_mul_bot_of_pos (inv_pos.mpr ht)]
  | top => simp [EReal.coe_mul_top_of_pos (inv_pos.mpr ht), ← EReal.coe_add, ← EReal.coe_mul]
  | coe v =>
    norm_cast
    rw [← div_eq_inv_mul, div_le_iff₀ ht]
    constructor <;> intro h <;> linarith

theorem solution {F : Type*} [AddCommGroup F] [Module ℝ F] (h : F → EReal) (hconv : ConvexFn h)
    (h0_bot : h 0 ≠ ⊥) (h0_top : h 0 ≠ ⊤) :
    ∀ z : F, h 0 + dirDeriv0 h z ≤ h z ∧ -dirDeriv0 h (-z) ≤ dirDeriv0 h z := by
  let a := (h 0).toReal
  have ha : (a : EReal) = h 0 := EReal.coe_toReal h0_top h0_bot
  let q := fun (z : F) (t : ℝ) => ((t⁻¹ : ℝ) : EReal) * (h (t • z) - (a : EReal))
  have hd (z : F) : dirDeriv0 h z = liminf (q z) (𝓝[>] (0 : ℝ)) := by
    simp only [dirDeriv0, q, ha]
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := by
    exact self_mem_nhdsWithin
  intro z
  constructor
  · apply ereal_upper
    intro r hr
    have hq : ∀ᶠ t : ℝ in 𝓝[>] 0, q z t ≤ ((r - a : ℝ) : EReal) := by
      filter_upwards [hp, (show ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 from
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds)] with t ht ht1
      have hh := hconv (show (0,a) ∈ {p : F × ℝ | h p.1 ≤ (p.2 : EReal)} by simpa [ha])
        (show (z,r) ∈ {p : F × ℝ | h p.1 ≤ (p.2 : EReal)} from hr.le)
        (show 0 ≤ 1 - t by linarith) ht.le (show (1 - t) + t = 1 by ring)
      have hh' : h (t • z) ≤ (((1 - t) * a + t * r : ℝ) : EReal) := by
        simpa using hh
      apply (quotient_le (h (t • z)) a t (r-a) ht).2
      convert hh' using 1 <;> ring
    have hl : dirDeriv0 h z ≤ ((r - a : ℝ) : EReal) := by
      rw [hd]
      exact liminf_le_of_frequently_le' hq.frequently
    calc
      h 0 + dirDeriv0 h z ≤ (a : EReal) + ((r-a : ℝ) : EReal) := by rw [← ha]; exact add_le_add le_rfl hl
      _ = (r : EReal) := by rw [← EReal.coe_add]; congr 1; ring
  · have pair (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
        -q (-z) s ≤ q z t := by
      apply ereal_upper
      intro r hr
      apply EReal.neg_le.mpr
      apply le_of_not_gt
      intro hbad
      obtain ⟨u, hu, hu'⟩ := EReal.lt_iff_exists_real_btwn.mp hbad
      have hz : h (t • z) ≤ ((a + t * r : ℝ) : EReal) :=
        (quotient_le _ a t r ht).mp hr.le
      have hn : h (s • (-z)) ≤ ((a + s * u : ℝ) : EReal) :=
        (quotient_le _ a s u hs).mp hu.le
      have hsum : 0 < t + s := by linarith
      have hh := hconv
        (show (t • z, a + t * r) ∈ {p : F × ℝ | h p.1 ≤ (p.2 : EReal)} from hz)
        (show (s • (-z), a + s * u) ∈ {p : F × ℝ | h p.1 ≤ (p.2 : EReal)} from hn)
        (show 0 ≤ s / (t+s) by positivity) (show 0 ≤ t / (t+s) by positivity)
        (show s / (t+s) + t / (t+s) = 1 by field_simp; ring)
      have hv : (s / (t+s)) • (t • z) + (t / (t+s)) • (s • (-z)) = (0 : F) := by
        rw [smul_smul, smul_smul, smul_neg]
        have he : s / (t+s) * t = t / (t+s) * s := by ring
        rw [he, add_neg_cancel]
      change h ((s / (t+s)) • (t • z) + (t / (t+s)) • (s • (-z))) ≤
        ((s / (t+s) * (a+t*r) + t / (t+s) * (a+s*u) : ℝ) : EReal) at hh
      have hh' : (a : EReal) ≤
          ((s / (t+s) * (a+t*r) + t / (t+s) * (a+s*u) : ℝ) : EReal) := by
        simpa only [hv, ← ha] using hh
      have hnreal : a ≤ s / (t+s) * (a+t*r) + t / (t+s) * (a+s*u) := by exact_mod_cast hh'
      have he : s / (t+s) * (a+t*r) + t / (t+s) * (a+s*u) = a + (t*s/(t+s))*(r+u) := by
        field_simp
        <;> ring
      have hc : 0 < t*s/(t+s) := by positivity
      have hu'' : u < -r := by exact_mod_cast hu'
      rw [he] at hnreal
      nlinarith
    have lower (t : ℝ) (ht : 0 < t) : -dirDeriv0 h (-z) ≤ q z t := by
      apply EReal.neg_le.mpr
      rw [hd]
      refine le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hp] with s hs
      exact EReal.neg_le.mp (pair t s ht hs)
    rw [hd]
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hp] with t ht
    simpa only [hd, q, ha] using lower t ht

#print axioms solution
