-- Prove2me | solution 1 for CrowdfundRM.Identical.proposition_6_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:42:47.650863+00:00
-- url     : https://prove2.me/submissions/b2c32b8c-0778-438e-899a-eae2eb2a2056

import Mathlib
import Definitions.Def_CrowdfundRM_Identical_Setting

open MeasureTheory

namespace C6iiAux
open CrowdfundRM.Identical

lemma int_exp_neg (k t : ℝ) (hk : 0 < k) :
    ∫ x in (0:ℝ)..t, Real.exp (-k * x) = (1 - Real.exp (-k * t)) / k := by
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) t,
      HasDerivAt (fun x => -Real.exp (-k * x) / k) (Real.exp (-k * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => -k * x) (-k) x := by
      simpa using (hasDerivAt_id x).const_mul (-k)
    have h2 := h1.exp.neg.div_const k
    exact h2.congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x => Real.exp (-k * x)).intervalIntegrable _ _)]
  simp
  field_simp
  ring

lemma int_exp_shift (c T a : ℝ) (hc : c ≠ 0) :
    ∫ τ in a..T, Real.exp (c * (T - τ)) = (Real.exp (c * (T - a)) - 1) / c := by
  have hd : ∀ x ∈ Set.uIcc a T,
      HasDerivAt (fun x => -Real.exp (c * (T - x)) / c) (Real.exp (c * (T - x))) x := by
    intro x _
    have h1 : HasDerivAt (fun x => c * (T - x)) (-c) x := by
      simpa using ((hasDerivAt_id x).const_sub T).const_mul c
    have h2 := h1.exp.neg.div_const c
    exact h2.congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun x => Real.exp (c * (T - x))).intervalIntegrable _ _)]
  simp
  field_simp
  ring

lemma inner_i (M : Campaign) (vi p T t : ℝ) (hF : M.Fbi = stepBar vi) (hr : 0 < M.r)
    (hk : 0 < M.k) (hp : 0 < p) (hpT : p * Real.exp (M.r * T) ≤ vi) (ht0 : 0 ≤ t)
    (htT : t ≤ T) :
    ∫ x in (0:ℝ)..t, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x))) =
      (1 - Real.exp (-M.k * t)) / M.k := by
  rw [hF]
  have h1 : ∫ x in (0:ℝ)..t, Real.exp (-M.k * x) * stepBar vi (p * Real.exp (M.r * (T - x))) =
      ∫ x in (0:ℝ)..t, Real.exp (-M.k * x) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le ht0] at hx
    have : stepBar vi (p * Real.exp (M.r * (T - x))) = 1 := by
      unfold stepBar
      rw [if_pos]
      calc p * Real.exp (M.r * (T - x)) < p * Real.exp (M.r * T) := by
            apply mul_lt_mul_of_pos_left _ hp
            apply Real.exp_lt_exp.mpr
            nlinarith [hx.1]
        _ ≤ vi := hpT
    rw [this, mul_one]
  rw [h1, int_exp_neg _ _ hk]

lemma npi_eq (M : Campaign) (vi p T : ℝ) (hF : M.Fbi = stepBar vi) (hr : 0 < M.r)
    (hk : 0 < M.k) (hp : 0 < p) (hpT : p * Real.exp (M.r * T) ≤ vi) (hT : 0 ≤ T) :
    npi M p T T = M.Ihat * (1 - Real.exp (-M.k * T)) := by
  unfold npi
  rw [inner_i M vi p T T hF hr hk hp hpT hT le_rfl]
  field_simp

lemma nph_zero (M : Campaign) (vh p T : ℝ) (hF : M.Fbh = stepBar vh) (hr : 0 < M.r)
    (hp : vh ≤ p) (hp0 : 0 < p) (hT : 0 ≤ T) : nph M p T T = 0 := by
  unfold nph
  have : ∫ τ in (0:ℝ)..T,
      Real.exp (M.Lh * M.q * p * ∫ u in τ..T, M.Fbh (p * Real.exp (M.r * (T - u)))) *
        M.Fbh (p * Real.exp (M.r * (T - τ))) *
        ∫ x in (0:ℝ)..τ, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x))) =
      ∫ τ in (0:ℝ)..T, (0:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hT] at hx
    have : M.Fbh (p * Real.exp (M.r * (T - x))) = 0 := by
      rw [hF]; unfold stepBar
      rw [if_neg]
      push Not
      have : 1 ≤ Real.exp (M.r * (T - x)) := Real.one_le_exp (by nlinarith [hx.2])
      nlinarith
    rw [this]; ring
  rw [this]; simp


lemma nph_le (M : Campaign) (vi vh p T : ℝ) (hFi : M.Fbi = stepBar vi)
    (hFh : M.Fbh = stepBar vh) (hr : 0 < M.r) (hk : 0 < M.k) (hI : 0 < M.Ihat)
    (hc : 0 < M.Lh * M.q * p) (hp0 : 0 < p) (hpv : p < vh)
    (hpT : p * Real.exp (M.r * T) ≤ vi) (hT : 0 ≤ T) :
    nph M p T T ≤ M.Ihat * (1 - Real.exp (-M.k * T)) *
      (Real.exp (M.Lh * M.q * p * (T - max 0 (T - Real.log (vh / p) / M.r))) - 1) := by
  set c := M.Lh * M.q * p with hcdef
  set L := Real.log (vh / p) / M.r with hL
  have hvp : 1 < vh / p := by rw [lt_div_iff₀ hp0]; linarith
  have hlog : 0 < Real.log (vh / p) := Real.log_pos hvp
  have hLpos : 0 < L := div_pos hlog hr
  have hrL : M.r * L = Real.log (vh / p) := by rw [hL]; field_simp
  have hexpL : Real.exp (Real.log (vh / p)) = vh / p := Real.exp_log (by linarith)
  set s := max 0 (T - L) with hs
  have hs0 : 0 ≤ s := le_max_left _ _
  have hsT : s ≤ T := max_le hT (by linarith)
  have key1 : ∀ τ, 0 < τ → τ ≤ s → M.Fbh (p * Real.exp (M.r * (T - τ))) = 0 := by
    intro τ h0 hτ
    have hτ' : τ ≤ T - L := by
      rcases le_max_iff.mp hτ with h | h
      · linarith
      · exact h
    rw [hFh]; unfold stepBar; rw [if_neg]; push Not
    have h1 : Real.log (vh / p) ≤ M.r * (T - τ) := by rw [← hrL]; nlinarith
    have h2 : vh / p ≤ Real.exp (M.r * (T - τ)) := by
      rw [← hexpL]; exact Real.exp_le_exp.mpr h1
    rw [div_le_iff₀ hp0] at h2; linarith
  have key2 : ∀ u, s < u → M.Fbh (p * Real.exp (M.r * (T - u))) = 1 := by
    intro u hu
    have hu' : T - L < u := lt_of_le_of_lt (le_max_right _ _) hu
    rw [hFh]; unfold stepBar; rw [if_pos]
    have h1 : M.r * (T - u) < Real.log (vh / p) := by rw [← hrL]; nlinarith
    have h2 : Real.exp (M.r * (T - u)) < vh / p := by
      rw [← hexpL]; exact Real.exp_lt_exp.mpr h1
    rw [lt_div_iff₀ hp0] at h2; linarith
  set f : ℝ → ℝ := fun τ =>
    Real.exp (c * ∫ u in τ..T, M.Fbh (p * Real.exp (M.r * (T - u)))) *
      M.Fbh (p * Real.exp (M.r * (T - τ))) *
      ∫ x in (0:ℝ)..τ, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x))) with hf
  set φ : ℝ → ℝ := fun τ => Real.exp (c * (T - τ)) * ((1 - Real.exp (-M.k * τ)) / M.k) with hφ
  have hEq0 : Set.EqOn f (fun _ => (0:ℝ)) (Set.uIoc 0 s) := by
    intro τ hτ
    rw [Set.uIoc_of_le hs0] at hτ
    simp only [hf]
    rw [key1 τ hτ.1 hτ.2]; ring
  have hEq1 : Set.EqOn f φ (Set.uIoc s T) := by
    intro τ hτ
    rw [Set.uIoc_of_le hsT] at hτ
    have hG : ∫ u in τ..T, M.Fbh (p * Real.exp (M.r * (T - u))) = T - τ := by
      have : ∫ u in τ..T, M.Fbh (p * Real.exp (M.r * (T - u))) = ∫ u in τ..T, (1:ℝ) := by
        apply intervalIntegral.integral_congr_ae
        refine Filter.Eventually.of_forall (fun u hu => ?_)
        rw [Set.uIoc_of_le hτ.2] at hu
        exact key2 u (lt_trans hτ.1 hu.1)
      rw [this]; simp
    simp only [hf, hφ]
    rw [hG, key2 τ hτ.1, inner_i M vi p T τ hFi hr hk hp0 hpT (by linarith [hτ.1]) hτ.2]
    ring
  have hφc : Continuous φ := by fun_prop
  have hf1 : IntervalIntegrable f MeasureTheory.volume 0 s :=
    ((by fun_prop : Continuous (fun _ : ℝ => (0:ℝ))).intervalIntegrable _ _).congr hEq0.symm
  have hf2 : IntervalIntegrable f MeasureTheory.volume s T :=
    (hφc.intervalIntegrable _ _).congr hEq1.symm
  have hI0 : ∫ τ in (0:ℝ)..s, f τ = 0 := by
    rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun τ hτ => hEq0 hτ))]
    simp
  have hI1 : ∫ τ in s..T, f τ = ∫ τ in s..T, φ τ :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun τ hτ => hEq1 hτ))
  have hmono : ∫ τ in s..T, φ τ ≤
      ∫ τ in s..T, Real.exp (c * (T - τ)) * ((1 - Real.exp (-M.k * T)) / M.k) := by
    apply intervalIntegral.integral_mono_on hsT (hφc.intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun τ =>
        Real.exp (c * (T - τ)) * ((1 - Real.exp (-M.k * T)) / M.k))).intervalIntegrable _ _)
    intro τ hτ
    simp only [hφ]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply div_le_div_of_nonneg_right _ hk.le
    have : Real.exp (-M.k * T) ≤ Real.exp (-M.k * τ) := Real.exp_le_exp.mpr (by nlinarith [hτ.2])
    linarith
  rw [intervalIntegral.integral_mul_const, int_exp_shift c T s hc.ne'] at hmono
  unfold nph
  show c * (M.k * M.Ihat * ∫ τ in (0:ℝ)..T, f τ) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hf1 hf2, hI0, hI1, zero_add]
  have hfin : c * (M.k * M.Ihat * ((Real.exp (c * (T - s)) - 1) / c *
      ((1 - Real.exp (-M.k * T)) / M.k))) =
      M.Ihat * (1 - Real.exp (-M.k * T)) * (Real.exp (c * (T - s)) - 1) := by
    field_simp
  rw [← hfin]
  apply mul_le_mul_of_nonneg_left _ hc.le
  apply mul_le_mul_of_nonneg_left hmono (by positivity)

lemma keyA (k r T Ts : ℝ) (hk : 0 < k) (hr : 0 < r)
    (hu : Real.exp (-k * Ts) = r / (k + r)) :
    Real.exp (-r * T) * (1 - Real.exp (-k * T)) ≤ Real.exp (-r * Ts) * (1 - Real.exp (-k * Ts)) ∧
    (T ≠ Ts → Real.exp (-r * T) * (1 - Real.exp (-k * T)) <
      Real.exp (-r * Ts) * (1 - Real.exp (-k * Ts))) := by
  set d := T - Ts with hd
  have hsplit : Real.exp (-k * T) = r / (k + r) * Real.exp (-k * d) := by
    rw [← hu, ← Real.exp_add]; congr 1; rw [hd]; ring
  have hkr : 0 < k + r := by linarith
  have h1 : 1 - Real.exp (-k * d) ≤ k * d := by linarith [Real.add_one_le_exp (-k * d)]
  have hbound : 1 - Real.exp (-k * T) ≤ k / (k + r) * (1 + r * d) := by
    rw [hsplit]
    have : 1 - r / (k + r) * Real.exp (-k * d) =
        k / (k + r) * (1 + r / k * (1 - Real.exp (-k * d))) := by field_simp; ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : r / k * (1 - Real.exp (-k * d)) ≤ r / k * (k * d) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h2 : r / k * (k * d) = r * d := by field_simp
    linarith
  have hE : Real.exp (-r * T) * Real.exp (r * d) = Real.exp (-r * Ts) := by
    rw [← Real.exp_add]; congr 1; rw [hd]; ring
  have hR : Real.exp (-r * Ts) * (1 - Real.exp (-k * Ts)) =
      Real.exp (-r * T) * (k / (k + r) * Real.exp (r * d)) := by
    rw [hu, ← hE]; field_simp; ring
  have hpos : 0 < Real.exp (-r * T) * (k / (k + r)) := by positivity
  constructor
  · rw [hR]
    have h3 : 1 + r * d ≤ Real.exp (r * d) := by linarith [Real.add_one_le_exp (r * d)]
    calc Real.exp (-r * T) * (1 - Real.exp (-k * T))
        ≤ Real.exp (-r * T) * (k / (k + r) * (1 + r * d)) :=
          mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
      _ ≤ Real.exp (-r * T) * (k / (k + r) * Real.exp (r * d)) := by
          rw [← mul_assoc, ← mul_assoc]; exact mul_le_mul_of_nonneg_left h3 hpos.le
  · intro hne
    have hd0 : r * d ≠ 0 := mul_ne_zero hr.ne' (by rw [hd]; exact sub_ne_zero.mpr hne)
    rw [hR]
    have h3 : 1 + r * d < Real.exp (r * d) := by linarith [Real.add_one_lt_exp hd0]
    calc Real.exp (-r * T) * (1 - Real.exp (-k * T))
        ≤ Real.exp (-r * T) * (k / (k + r) * (1 + r * d)) :=
          mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
      _ < Real.exp (-r * T) * (k / (k + r) * Real.exp (r * d)) := by
          rw [← mul_assoc, ← mul_assoc]; exact mul_lt_mul_of_pos_left h3 hpos

lemma keyB (k r vi vh p T Lq : ℝ) (hk : 0 < k) (hr : 0 < r) (hp0 : 0 < p) (hpv : p < vh)
    (hvv : vh < vi) (hT : 0 ≤ T) (hTv : r * T ≤ Real.log (vi / p)) (hLq : 0 ≤ Lq)
    (hA : (1 + k / r) * Real.exp (-(k / r) * Real.log (vi / vh)) < 1 - Lq * vh / r) :
    p * (1 - Real.exp (-k * T)) * Real.exp (Lq * p * (Real.log (vh / p) / r)) <
      vi * Real.exp (r / k * Real.log (r / (k + r))) * (k / (k + r)) := by
  have hvh : 0 < vh := lt_trans hp0 hpv
  have hvi : 0 < vi := lt_trans hvh hvv
  set m := k / r with hm
  have hm0 : 0 < m := div_pos hk hr
  set z := Real.log (vh / p) with hz
  set g := Real.log (vi / vh) with hg
  have hz0 : 0 < z := Real.log_pos (by rw [lt_div_iff₀ hp0]; linarith)
  have hgz : Real.log (vi / p) = g + z := by
    rw [hg, hz, Real.log_div hvi.ne' hp0.ne', Real.log_div hvi.ne' hvh.ne',
      Real.log_div hvh.ne' hp0.ne']; ring
  have hpv' : p = vi * Real.exp (-(g + z)) := by
    rw [← hgz, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hpz : p = vh * Real.exp (-z) := by
    rw [hz, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  set A0 := (1 + m) * Real.exp (-m * g) with hA0
  have hA0pos : 0 < A0 := by positivity
  set δ := Lq * vh / r with hδ
  have hδ0 : 0 ≤ δ := by positivity
  -- step 1
  have hs1 : 1 - Real.exp (-k * T) ≤ 1 - Real.exp (-m * (g + z)) := by
    have : -m * (g + z) ≤ -k * T := by
      have hk' : k = m * r := by rw [hm]; field_simp
      rw [hk']; nlinarith
    linarith [Real.exp_le_exp.mpr this]
  set w := (1 - A0 * Real.exp (-m * z)) / m with hw
  have hs2 : 1 - Real.exp (-m * (g + z)) = m / (1 + m) * (1 + w) := by
    have : Real.exp (-m * (g + z)) = Real.exp (-m * g) * Real.exp (-m * z) := by
      rw [← Real.exp_add]; ring_nf
    rw [this, hw, hA0]; field_simp; ring
  have hs3 : 1 + w ≤ Real.exp w := by linarith [Real.add_one_le_exp w]
  have hkm : k / (k + r) = m / (1 + m) := by rw [hm]; field_simp; ring
  have hlogu : r / k * Real.log (r / (k + r)) = -(1 / m) * Real.log (1 + m) := by
    have : r / (k + r) = (1 + m)⁻¹ := by rw [hm]; field_simp; ring
    rw [this, Real.log_inv, hm]; field_simp
  -- herding exponent bound
  have hcL : Lq * p * (z / r) ≤ δ * z := by
    rw [hpz, hδ]
    have : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have : Lq * (vh * Real.exp (-z)) * (z / r) = (Lq * vh / r) * z * Real.exp (-z) := by ring
    rw [this]
    have : 0 ≤ Lq * vh / r * z := by positivity
    nlinarith
  -- w bound
  have hw2 : w ≤ (1 - A0) / m + A0 * z := by
    rw [hw]
    have : 1 - m * z ≤ Real.exp (-m * z) := by linarith [Real.add_one_le_exp (-m * z)]
    rw [div_add' _ _ _ hm0.ne', div_le_div_iff_of_pos_right hm0]
    nlinarith
  set t0 := Real.log (1 + m) - m * g with ht0
  have hA0t : A0 = Real.exp t0 := by
    rw [hA0, ht0, Real.exp_sub, Real.exp_log (by linarith)]
    rw [show -m * g = -(m * g) by ring, Real.exp_neg]; field_simp
  have hA1 : A0 < 1 - δ := hA
  have ht0ne : t0 ≠ 0 := by
    intro h; rw [h, Real.exp_zero] at hA0t; linarith
  have ht0b : t0 + 1 < A0 := by rw [hA0t]; exact Real.add_one_lt_exp ht0ne
  -- exponent inequality
  have hexp : -(g + z) + w + δ * z < -(1 / m) * Real.log (1 + m) := by
    have e1 : -(1 / m) * Real.log (1 + m) = -g - t0 / m := by
      rw [ht0]; field_simp; ring
    rw [e1]
    have : (t0 + 1 - A0) / m < 0 := div_neg_of_neg_of_pos (by linarith) hm0
    have : z * (A0 + δ - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hz0.le (by linarith)
    have : (1 - A0) / m = (t0 + 1 - A0) / m - t0 / m := by field_simp; ring
    nlinarith
  -- assemble
  calc p * (1 - Real.exp (-k * T)) * Real.exp (Lq * p * (z / r))
      ≤ p * (m / (1 + m) * Real.exp w) * Real.exp (δ * z) := by
        apply mul_le_mul _ (Real.exp_le_exp.mpr hcL) (Real.exp_pos _).le (by positivity)
        apply mul_le_mul_of_nonneg_left _ hp0.le
        calc 1 - Real.exp (-k * T) ≤ m / (1 + m) * (1 + w) := hs1.trans hs2.le
          _ ≤ m / (1 + m) * Real.exp w := mul_le_mul_of_nonneg_left hs3 (by positivity)
    _ = vi * (m / (1 + m)) * Real.exp (-(g + z) + w + δ * z) := by
        rw [hpv', Real.exp_add, Real.exp_add]; ring
    _ < vi * (m / (1 + m)) * Real.exp (-(1 / m) * Real.log (1 + m)) := by
        apply mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hexp) (by positivity)
    _ = vi * Real.exp (r / k * Real.log (r / (k + r))) * (k / (k + r)) := by
        rw [hlogu, hkm]; ring

lemma X_ge (M : Campaign) (vh : ℝ) (hk : 0 < M.k) (hr : 0 < M.r) (hLq : 0 < M.Lh * M.q)
    (hvh : 0 < vh) : 1 + M.k / M.r ≤ Xthr M vh := by
  unfold Xthr a6 b6
  have ha : 0 < M.k / (M.Lh * M.q) := div_pos hk hLq
  have h1 : 0 ≤ Real.exp (M.Lh * M.q / M.r * vh / Real.exp 1) * (1 / (4 * (M.k / (M.Lh * M.q)))) *
      (M.k / M.r * vh * Real.exp (-2) + 1 / 2 * (M.Lh * M.q / M.r) * vh ^ 2 * Real.exp (-3) +
        2 * (M.k / (M.Lh * M.q)) + vh) := by positivity
  have h2 : 1 / (M.k / (M.Lh * M.q)) * (M.k / M.r * (vh + M.k / (M.Lh * M.q)) + M.k / (M.Lh * M.q))
      = M.k / M.r * vh / (M.k / (M.Lh * M.q)) + M.k / M.r + 1 := by
    have gen : ∀ a K v : ℝ, a ≠ 0 → 1 / a * (K * (v + a) + a) = K * v / a + K + 1 := by
      intro a K v ha; field_simp
    exact gen _ _ _ ha.ne'
  have h3 : 0 ≤ M.k / M.r * vh / (M.k / (M.Lh * M.q)) := by positivity
  linarith

end C6iiAux

open CrowdfundRM.Identical C6iiAux in
theorem solution (M : Campaign) (hM : M.Standing) (vi vh : ℝ) (hv : IdenticalVals M vi vh)
    (hLh : 0 < M.Lh) (hq : 0 < M.q) (hlt : vh < vi) (hδ : δ6 M vh < 1)
    (hX : (Xthr M vh / (1 - δ6 M vh)) ^ (M.r / M.k) < vi / vh) :
    CrowdfundRM.Triangular.IsUniqueMaxOn₂ (revenue M) (Feasible6 M vi)
      (vi * (M.r / (M.k + M.r)) ^ (M.r / M.k))
      (1 / M.r * Real.log (vi / (vi * (M.r / (M.k + M.r)) ^ (M.r / M.k)))) := by
  obtain ⟨hI, hk, hr, hvb, -, -, -, -⟩ := hM
  obtain ⟨hvi, hvib, hvh, hvhb, hFi, hFh⟩ := hv
  have hLq : 0 < M.Lh * M.q := mul_pos hLh hq
  have hkr : 0 < M.k + M.r := by linarith
  set u0 := M.r / (M.k + M.r) with hu0
  have hu0pos : 0 < u0 := div_pos hr hkr
  have hu0lt : u0 < 1 := by rw [hu0, div_lt_one hkr]; linarith
  have hlogu0 : Real.log u0 < 0 := Real.log_neg hu0pos hu0lt
  set ps := vi * u0 ^ (M.r / M.k) with hps
  set Ts := 1 / M.r * Real.log (vi / ps) with hTs
  have hpsE : ps = vi * Real.exp (M.r / M.k * Real.log u0) := by
    rw [hps, Real.rpow_def_of_pos hu0pos]; ring_nf
  have hps0 : 0 < ps := by rw [hpsE]; positivity
  have hvips : Real.log (vi / ps) = -(M.r / M.k * Real.log u0) := by
    rw [hpsE, div_mul_cancel_left₀ hvi.ne', ← Real.exp_neg, Real.log_exp]
  have hkTs : Real.exp (-M.k * Ts) = u0 := by
    have : -M.k * Ts = Real.log u0 := by rw [hTs, hvips]; field_simp
    rw [this, Real.exp_log hu0pos]
  have hrTs : vi * Real.exp (-M.r * Ts) = ps := by
    have : -M.r * Ts = M.r / M.k * Real.log u0 := by rw [hTs, hvips]; field_simp
    rw [this, hpsE]
  have hTs0 : 0 ≤ Ts := by
    rw [hTs, hvips]
    have : 0 ≤ -(M.r / M.k * Real.log u0) := by
      have : M.r / M.k * Real.log u0 < 0 := mul_neg_of_pos_of_neg (by positivity) hlogu0
      linarith
    positivity
  have hpsvi : ps ≤ vi := by
    rw [hpsE]
    have : Real.exp (M.r / M.k * Real.log u0) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_neg_of_pos_of_neg (by positivity) hlogu0).le
    nlinarith
  -- consequence of (33)
  set g := Real.log (vi / vh) with hg
  have hδ' : δ6 M vh = M.Lh * M.q * vh / M.r := rfl
  have hδ0 : 0 < δ6 M vh := by rw [hδ']; positivity
  have hXg := X_ge M vh hk hr hLq hvh
  have hXpos : 0 < Xthr M vh := by have : 0 < M.k / M.r := by positivity
                                   linarith
  have hQ : 0 < Xthr M vh / (1 - δ6 M vh) := div_pos hXpos (by linarith)
  have hA : (1 + M.k / M.r) * Real.exp (-(M.k / M.r) * g) < 1 - M.Lh * M.q * vh / M.r := by
    have h1 := Real.log_lt_log (by positivity) hX
    rw [Real.log_rpow hQ] at h1
    have h2 : Real.log (Xthr M vh / (1 - δ6 M vh)) < M.k / M.r * g := by
      have := mul_lt_mul_of_pos_left h1 (by positivity : 0 < M.k / M.r)
      rw [← mul_assoc, show M.k / M.r * (M.r / M.k) = 1 by field_simp, one_mul] at this
      exact this
    have h3 : Xthr M vh / (1 - δ6 M vh) < Real.exp (M.k / M.r * g) :=
      (Real.log_lt_iff_lt_exp hQ).mp h2
    rw [div_lt_iff₀ (by linarith)] at h3
    rw [← hδ', show -(M.k / M.r) * g = -(M.k / M.r * g) by ring, Real.exp_neg]
    rw [← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
    nlinarith
  have hpsvh : vh < ps := by
    have hm0 : 0 < M.k / M.r := by positivity
    have h1 : (1 + M.k / M.r) * Real.exp (-(M.k / M.r) * g) < 1 := by linarith
    have h2 : Real.log (1 + M.k / M.r) < M.k / M.r * g := by
      rw [Real.log_lt_iff_lt_exp (by linarith)]
      rw [show -(M.k / M.r) * g = -(M.k / M.r * g) by ring, Real.exp_neg,
        ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)] at h1
      linarith
    have hu0' : u0 = (1 + M.k / M.r)⁻¹ := by rw [hu0]; field_simp; ring
    have h3 : -g < M.r / M.k * Real.log u0 := by
      rw [hu0', Real.log_inv]
      have : M.r / M.k * Real.log (1 + M.k / M.r) < M.r / M.k * (M.k / M.r * g) :=
        mul_lt_mul_of_pos_left h2 (by positivity)
      rw [← mul_assoc, show M.r / M.k * (M.k / M.r) = 1 by field_simp, one_mul] at this
      linarith
    have hvhE : vh = vi * Real.exp (-g) := by
      rw [hg, Real.exp_neg, Real.exp_log (by positivity)]; field_simp
    rw [hvhE, hpsE]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr h3) hvi
  -- revenue in the region p ≥ vh
  have hrevHi : ∀ p T, vh ≤ p → 0 < p → 0 ≤ T → p * Real.exp (M.r * T) ≤ vi →
      revenue M p T = p * (M.Ihat * (1 - Real.exp (-M.k * T))) := by
    intro p T h1 h2 h3 h4
    unfold revenue ntot
    rw [npi_eq M vi p T hFi hr hk h2 h4 h3, nph_zero M vh p T hFh hr h1 h2 h3, add_zero]
  have hpsT : ps * Real.exp (M.r * Ts) ≤ vi := by
    rw [← hrTs, mul_assoc, ← Real.exp_add]; simp
  set V := ps * (M.Ihat * (1 - u0)) with hV
  have hrevS : revenue M ps Ts = V := by
    rw [hrevHi ps Ts hpsvh.le hps0 hTs0 hpsT, hkTs]
  have hA' := keyA M.k M.r
  -- main claim
  have hmain : ∀ p T, Feasible6 M vi p T →
      revenue M p T ≤ V ∧ (revenue M p T = V → p = ps ∧ T = Ts) := by
    rintro p T ⟨⟨hp0, -, hT0, -⟩, hTv⟩
    have hrT : M.r * T ≤ Real.log (vi / p) := by
      rw [le_div_iff₀ hr] at hTv; linarith
    have hpT : p * Real.exp (M.r * T) ≤ vi := by
      have : Real.exp (M.r * T) ≤ vi / p := by
        rw [← Real.exp_log (by positivity : 0 < vi / p)]; exact Real.exp_le_exp.mpr hrT
      rw [le_div_iff₀ hp0] at this; linarith
    have hpe : p ≤ vi * Real.exp (-M.r * T) := by
      rw [show -M.r * T = -(M.r * T) by ring, Real.exp_neg, ← div_eq_mul_inv,
        le_div_iff₀ (Real.exp_pos _)]; exact hpT
    have hfac : 0 ≤ M.Ihat * (1 - Real.exp (-M.k * T)) := by
      have : Real.exp (-M.k * T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have : 0 ≤ 1 - Real.exp (-M.k * T) := by linarith
      positivity
    have hVeq : V = M.Ihat * (vi * (Real.exp (-M.r * Ts) * (1 - Real.exp (-M.k * Ts)))) := by
      rw [hV, ← hrTs, hkTs]; ring
    rcases le_or_gt vh p with hcase | hcase
    · rw [hrevHi p T hcase hp0 hT0 hpT]
      obtain ⟨hA1, hA2⟩ := hA' T Ts hk hr hkTs
      have hle1 : p * (M.Ihat * (1 - Real.exp (-M.k * T))) ≤
          M.Ihat * (vi * (Real.exp (-M.r * T) * (1 - Real.exp (-M.k * T)))) := by
        have := mul_le_mul_of_nonneg_right hpe hfac
        linarith
      have hle2 : M.Ihat * (vi * (Real.exp (-M.r * T) * (1 - Real.exp (-M.k * T)))) ≤ V := by
        rw [hVeq]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA1 hvi.le) hI.le
      refine ⟨hle1.trans hle2, fun heq => ?_⟩
      by_cases hTT : T = Ts
      · refine ⟨?_, hTT⟩
        subst hTT
        rw [hkTs] at heq
        have h1u : 0 < M.Ihat * (1 - u0) := mul_pos hI (by linarith)
        exact mul_right_cancel₀ h1u.ne' heq
      · exfalso
        have hlt2 : M.Ihat * (vi * (Real.exp (-M.r * T) * (1 - Real.exp (-M.k * T)))) < V := by
          rw [hVeq]
          exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left (hA2 hTT) hvi) hI
        linarith
    · -- p < vh
      have hnp := nph_le M vi vh p T hFi hFh hr hk hI (mul_pos hLq hp0) hp0 hcase hpT hT0
      have hB := keyB M.k M.r vi vh p T (M.Lh * M.q) hk hr hp0 hcase hlt hT0 hrT hLq.le hA
      set L := Real.log (vh / p) / M.r with hL
      set c := M.Lh * M.q * p with hc
      have hTs' : T - max 0 (T - L) ≤ L := by
        have := le_max_right 0 (T - L); linarith
      have hexpb : Real.exp (c * (T - max 0 (T - L))) ≤ Real.exp (c * L) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hTs' (by positivity))
      have hrev : revenue M p T ≤
          p * (M.Ihat * (1 - Real.exp (-M.k * T)) * Real.exp (c * L)) := by
        unfold revenue ntot
        rw [npi_eq M vi p T hFi hr hk hp0 hpT hT0]
        apply mul_le_mul_of_nonneg_left _ hp0.le
        have h1 := mul_le_mul_of_nonneg_left hexpb hfac
        have h2 : M.Ihat * (1 - Real.exp (-M.k * T)) + nph M p T T ≤
            M.Ihat * (1 - Real.exp (-M.k * T)) * Real.exp (c * (T - max 0 (T - L))) := by
          linarith
        exact h2.trans h1
      have hlt3 : p * (M.Ihat * (1 - Real.exp (-M.k * T)) * Real.exp (c * L)) < V := by
        have e1 : p * (M.Ihat * (1 - Real.exp (-M.k * T)) * Real.exp (c * L)) =
            M.Ihat * (p * (1 - Real.exp (-M.k * T)) * Real.exp (M.Lh * M.q * p * L)) := by
          rw [hc]; ring
        have e2 : V = M.Ihat * (vi * Real.exp (M.r / M.k * Real.log (M.r / (M.k + M.r))) *
            (M.k / (M.k + M.r))) := by
          rw [hV, hpsE, hu0, show 1 - M.r / (M.k + M.r) = M.k / (M.k + M.r) by field_simp; ring]
          ring
        rw [e1, e2]
        exact mul_lt_mul_of_pos_left hB hI
      exact ⟨hrev.trans hlt3.le, fun h => absurd h (ne_of_lt (hrev.trans_lt hlt3))⟩
  refine ⟨⟨⟨hps0, hpsvi.trans hvib, hTs0, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [hTs, one_div_mul_eq_div]
    apply div_le_div_of_nonneg_right _ hr.le
    exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hvib hps0.le)
  · rw [hTs, one_div_mul_eq_div]
  · intro p T hpT
    rw [hrevS]; exact (hmain p T hpT).1
  · intro p T hpT heq
    rw [hrevS] at heq; exact (hmain p T hpT).2 heq
