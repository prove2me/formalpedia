-- Prove2me | solution 1 for FollowCustomers.SmallCost.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T18:21:37.090014+00:00
-- url     : https://prove2.me/submissions/7e96ec24-8903-4887-ac2a-a8f4f421d2bd

import Mathlib
import Definitions.Def_FollowCustomers_SmallCost_Model
open Filter Topology

set_option autoImplicit false

namespace FCSC35

open FollowCustomers.SmallCost

/-- `N(w) = w(e^w+1) - 2(e^w-1)`. -/
noncomputable def NN (w : ℝ) : ℝ := w * (Real.exp w + 1) - 2 * (Real.exp w - 1)

lemma deriv_pid (P : Params) (x : ℝ) :
    deriv (pid P) x = -(2 * P.δ / 3) * (1 + P.δ * (1 - 2 * x) / 3) := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + P.δ * (1 - 2 * x) / 3) (-(2 * P.δ / 3)) x := by
    have := ((((hasDerivAt_id x).const_mul 2).const_sub 1).const_mul P.δ).div_const 3 |>.const_add 1
    convert this using 1
    all_goals first | rfl | ring1
  have h2 : HasDerivAt (fun y : ℝ => 1 / 2 * (1 + P.δ * (1 - 2 * y) / 3) ^ 2)
      (-(2 * P.δ / 3) * (1 + P.δ * (1 - 2 * x) / 3)) x := by
    have := (h1.pow 2).const_mul (1 / 2 : ℝ)
    convert this using 1
    all_goals first | rfl | (push_cast; ring1)
  exact h2.deriv

lemma NN_bound {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : |NN w - w ^ 3 / 6| ≤ w ^ 4 := by
  have hb := Real.exp_bound (x := w) (by rw [abs_of_nonneg h0]; exact h1) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  rw [abs_of_nonneg h0] at hb
  norm_num at hb
  set E := Real.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6) with hE
  have hEb : |E| ≤ w ^ 4 * (5 / 96) := by
    have : E = Real.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6) := rfl
    rw [this]
    convert hb using 2
  have hN : NN w - w ^ 3 / 6 = w ^ 4 / 6 + (w - 2) * E := by
    simp only [NN, hE]; ring
  rw [hN]
  have hw4 : 0 ≤ w ^ 4 := by positivity
  have h2 : |(w - 2) * E| ≤ 2 * (w ^ 4 * (5 / 96)) := by
    rw [abs_mul]
    have : |w - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    exact mul_le_mul this hEb (abs_nonneg _) (by norm_num)
  calc |w ^ 4 / 6 + (w - 2) * E| ≤ |w ^ 4 / 6| + |(w - 2) * E| := abs_add_le _ _
    _ ≤ w ^ 4 / 6 + 2 * (w ^ 4 * (5 / 96)) := by
        rw [abs_of_nonneg (by positivity)]; linarith
    _ ≤ w ^ 4 := by nlinarith

lemma NN_hasDerivAt (w : ℝ) : HasDerivAt NN (1 + (w - 1) * Real.exp w) w := by
  have h := ((hasDerivAt_id w).mul ((Real.hasDerivAt_exp w).add_const 1)).sub
    (((Real.hasDerivAt_exp w).sub_const 1).const_mul 2)
  convert h using 1
  all_goals first | rfl | (simp only [id]; ring1)

lemma NN_mono : Monotone NN := by
  apply monotone_of_deriv_nonneg
  · intro w; exact (NN_hasDerivAt w).differentiableAt
  · intro w
    rw [(NN_hasDerivAt w).deriv]
    have h := Real.add_one_le_exp (-w)
    have he : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
    have hp := Real.exp_pos w
    nlinarith

lemma NN_zero : NN 0 = 0 := by simp [NN]

lemma NN_nonneg {w : ℝ} (h : 0 ≤ w) : 0 ≤ NN w := NN_zero ▸ NN_mono h

/-- Reduced equations. -/
lemma reduce (P : Params) (hP : P.Standing) (K xl xs : ℝ) (h : IsThresholdPair P K xl xs) :
    (2 - 2 * P.δ / 3 * ((xs - 1 / 2) - (xl - 1 / 2))) * (2 * P.δ / (3 * lam P)) *
        NN (lam P * ((xs - 1 / 2) + (xl - 1 / 2)))
      = 4 * P.r * K * (Real.exp (lam P * ((xs - 1 / 2) + (xl - 1 / 2))) + 1) ∧
    (-(2 * P.δ / 3) * ((xs - 1 / 2) - (xl - 1 / 2))
        + 2 * P.δ ^ 2 / 9 * ((xs - 1 / 2) ^ 2 + (xl - 1 / 2) ^ 2))
        * (Real.exp (lam P * ((xs - 1 / 2) + (xl - 1 / 2))) - 1)
      = (2 * P.δ / (3 * lam P)) ^ 2 * NN (lam P * ((xs - 1 / 2) + (xl - 1 / 2))) := by
  obtain ⟨hr, hs, hd⟩ := hP
  obtain ⟨h14, h15, -⟩ := h
  have hL : 0 < lam P := Real.sqrt_pos.2 (by positivity)
  have hG : Gf P xl xs = Real.exp (lam P * ((xs - 1 / 2) + (xl - 1 / 2))) := by
    simp only [Gf]; congr 1; ring
  have hGpos : 0 < Gf P xl xs := Real.exp_pos _
  unfold Eq14 at h14
  unfold Eq15 at h15
  have E1 : Gf P xl xs * den14 P K xl = num14 P K xs := by
    have hne : den14 P K xl ≠ 0 := by
      intro h0; rw [h0, div_zero] at h14; linarith
    rw [h14]; field_simp
  have E2 : Gf P xl xs * den15 P K xs = num15 P K xl := by
    have hne : den15 P K xs ≠ 0 := by
      intro h0; rw [h0, div_zero] at h15; linarith
    rw [h15]; field_simp
  rw [hG] at E1 E2
  simp only [num14, den14, num15, den15, deriv_pid] at E1 E2
  simp only [pid, pis] at E1 E2
  set G := Real.exp (lam P * ((xs - 1 / 2) + (xl - 1 / 2))) with hGdef
  set b := 2 * P.δ / (3 * lam P) with hb
  have hbL : b * lam P = 2 * P.δ / 3 := by rw [hb]; field_simp
  have e1 : G * ((1 / 2) * (1 + P.δ * (1 - 2 * (1 - xl)) / 3) ^ 2 - 1 / 2
      - b * (1 + P.δ * (1 - 2 * (1 - xl)) / 3) - P.r * K + b ^ 2)
      = (1 / 2) * (1 + P.δ * (1 - 2 * xs) / 3) ^ 2 - 1 / 2
      - b * (1 + P.δ * (1 - 2 * xs) / 3) + P.r * K + b ^ 2 := by
    rw [hb]; linear_combination E1
  have e2 : G * ((1 / 2) * (1 + P.δ * (1 - 2 * xs) / 3) ^ 2 - 1 / 2
      + b * (1 + P.δ * (1 - 2 * xs) / 3) + P.r * K + b ^ 2)
      = (1 / 2) * (1 + P.δ * (1 - 2 * (1 - xl)) / 3) ^ 2 - 1 / 2
      + b * (1 + P.δ * (1 - 2 * (1 - xl)) / 3) - P.r * K + b ^ 2 := by
    rw [hb]; linear_combination E2
  have hNN : NN (lam P * ((xs - 1 / 2) + (xl - 1 / 2)))
      = lam P * ((xs - 1 / 2) + (xl - 1 / 2)) * (G + 1) - 2 * (G - 1) := by
    simp only [NN, hGdef]
  rw [hNN]
  constructor
  · linear_combination 2 * e1 - 2 * e2
      + (G + 1) * (2 - 2 * P.δ / 3 * ((xs - 1 / 2) - (xl - 1 / 2))) * ((xs - 1 / 2) + (xl - 1 / 2)) * hbL
  · linear_combination e1 + e2 - (G + 1) * b * ((xs - 1 / 2) + (xl - 1 / 2)) * hbL

/-- Pointwise consequences of a threshold pair. -/
lemma pt (P : Params) (hP : P.Standing) (K u v : ℝ) (hK : 0 < K)
    (h : IsThresholdPair P K (v + 1 / 2) (u + 1 / 2)) :
    0 < v ∧ v < u ∧ u < 1 / 2 ∧ 0 < lam P * (u + v) ∧ lam P * (u + v) ≤ lam P ∧
    u - v ≤ 2 * P.δ / 3 * u ^ 2 ∧
    NN (lam P * (u + v)) * (2 * P.δ / (3 * lam P)) ≤ 4 * P.r * (Real.exp (lam P) + 1) * K ∧
    u ^ 3 / K = 4 * P.r / (2 * P.δ / (3 * lam P))
        * ((Real.exp (lam P * (u + v)) + 1) / (2 - 2 * P.δ / 3 * (u - v)))
        * (u / (lam P * (u + v))) ^ 3 * ((lam P * (u + v)) ^ 3 / NN (lam P * (u + v))) ∧
    (u - v) / u ^ 2 = 3 / (2 * P.δ) * (2 * P.δ ^ 2 / 9 * (1 + (v / u) ^ 2)
        - (2 * P.δ / (3 * lam P)) ^ 2 * (NN (lam P * (u + v)) / (lam P * (u + v)) ^ 3)
          * ((lam P * (u + v)) / (Real.exp (lam P * (u + v)) - 1))
          * ((lam P * (u + v)) / u) ^ 2) := by
  have hP' := hP
  obtain ⟨hr, hs, hd⟩ := hP'
  obtain ⟨R1, R2⟩ := reduce P hP K (v + 1 / 2) (u + 1 / 2) h
  simp only [add_sub_cancel_right] at R1 R2
  obtain ⟨-, -, ⟨h1, h2, h3, h4⟩⟩ := h
  have hv : 0 < v := by linarith
  have hvu : v < u := by linarith
  have hu : u < 1 / 2 := by linarith
  have hu0 : 0 < u := by linarith
  have hdu : 2 * P.δ / 3 * u < 1 := by nlinarith
  have hL : 0 < lam P := Real.sqrt_pos.2 (by positivity)
  set L := lam P with hLdef
  set w := L * (u + v) with hw
  have hw0 : 0 < w := by positivity
  have hwL : w ≤ L := by rw [hw]; nlinarith
  set b := 2 * P.δ / (3 * L) with hb
  have hb0 : 0 < b := by positivity
  have hE : 1 < Real.exp w := by have := Real.add_one_lt_exp (ne_of_gt hw0); linarith
  have hEL : Real.exp w ≤ Real.exp L := Real.exp_le_exp.2 hwL
  have hNN0 : 0 ≤ NN w := NN_nonneg hw0.le
  set y := 2 - 2 * P.δ / 3 * (u - v) with hy
  have hy1 : 1 ≤ y := by
    have : 2 * P.δ / 3 * (u - v) ≤ 2 * P.δ / 3 * u := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hy0 : 0 < y := by linarith
  have hNNpos : 0 < NN w := by
    by_contra hc
    push Not at hc
    have h0 : NN w = 0 := le_antisymm hc hNN0
    rw [h0, mul_zero] at R1
    have : 0 < 4 * P.r * K * (Real.exp w + 1) := by positivity
    linarith
  have hQ : 0 ≤ -(2 * P.δ / 3) * (u - v) + 2 * P.δ ^ 2 / 9 * (u ^ 2 + v ^ 2) := by
    by_contra hc
    push Not at hc
    have := mul_neg_of_neg_of_pos hc (by linarith : (0:ℝ) < Real.exp w - 1)
    have : 0 ≤ b ^ 2 * NN w := by positivity
    linarith
  refine ⟨hv, hvu, hu, hw0, hwL, ?_, ?_, ?_, ?_⟩
  · have hsq : v ^ 2 ≤ u ^ 2 := by nlinarith
    have : 2 * P.δ / 3 * (u - v) ≤ 2 * P.δ / 3 * (2 * P.δ / 3 * u ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  · have h4 : 0 ≤ 4 * P.r * K := by positivity
    have h5 := mul_le_mul_of_nonneg_left hEL h4
    calc NN w * b = 1 * (b * NN w) := by ring
      _ ≤ y * (b * NN w) := mul_le_mul_of_nonneg_right hy1 (by positivity)
      _ = 4 * P.r * K * (Real.exp w + 1) := by rw [← R1]; ring
      _ ≤ 4 * P.r * (Real.exp L + 1) * K := by linarith
  · have hKe : K = y * b * NN w / (4 * P.r * (Real.exp w + 1)) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [hKe]
    field_simp
  · have hNe : NN w = (-(2 * P.δ / 3) * (u - v) + 2 * P.δ ^ 2 / 9 * (u ^ 2 + v ^ 2))
        * (Real.exp w - 1) / b ^ 2 := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [hNe]
    have : Real.exp w - 1 ≠ 0 := by linarith
    field_simp
    ring

lemma tendsto_of_abs_sub_le {α : Type*} {l : Filter α} {f g : α → ℝ} {c : ℝ}
    (hg : Tendsto g l (𝓝 0)) (h : ∀ᶠ x in l, |f x - c| ≤ g x) : Tendsto f l (𝓝 c) := by
  have h1 : Tendsto (fun x => c - g x) l (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).sub hg
  have h2 : Tendsto (fun x => c + g x) l (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).add hg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 ?_ ?_
  · filter_upwards [h] with x hx
    linarith [(abs_le.1 hx).1]
  · filter_upwards [h] with x hx
    linarith [(abs_le.1 hx).2]

lemma NN_ratio {α : Type*} {l : Filter α} {g : α → ℝ} (hg : Tendsto g l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < g x) : Tendsto (fun x => NN (g x) / g x ^ 3) l (𝓝 (1 / 6)) := by
  apply tendsto_of_abs_sub_le hg
  have h1 : ∀ᶠ x in l, g x < 1 := hg.eventually (gt_mem_nhds one_pos)
  filter_upwards [hpos, h1] with x hx hx1
  have hb := NN_bound hx.le hx1.le
  have hx3 : 0 < g x ^ 3 := pow_pos hx 3
  have : NN (g x) / g x ^ 3 - 1 / 6 = (NN (g x) - g x ^ 3 / 6) / g x ^ 3 := by
    field_simp
  rw [this, abs_div, abs_of_pos hx3, div_le_iff₀ hx3]
  calc _ ≤ g x ^ 4 := hb
    _ = g x * g x ^ 3 := by ring

lemma exp_ratio {α : Type*} {l : Filter α} {g : α → ℝ} (hg : Tendsto g l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < g x) : Tendsto (fun x => g x / (Real.exp (g x) - 1)) l (𝓝 1) := by
  have h : Tendsto (fun x => (Real.exp (g x) - 1) / g x) l (𝓝 1) := by
    apply tendsto_of_abs_sub_le hg
    have h1 : ∀ᶠ x in l, g x < 1 := hg.eventually (gt_mem_nhds one_pos)
    filter_upwards [hpos, h1] with x hx hx1
    have hb := Real.abs_exp_sub_one_sub_id_le (x := g x) (by rw [abs_of_pos hx]; exact hx1.le)
    have : (Real.exp (g x) - 1) / g x - 1 = (Real.exp (g x) - 1 - g x) / g x := by
      field_simp
    rw [this, abs_div, abs_of_pos hx, div_le_iff₀ hx]
    calc _ ≤ g x ^ 2 := hb
      _ = g x * g x := by ring
  have := h.inv₀ one_ne_zero
  simpa [inv_div] using this

lemma core (P : Params) (hP : P.Standing) (xl xs : ℝ → ℝ) (hB : IsBranch P xl xs) :
    (∀ᶠ K in 𝓝[>] (0 : ℝ), 0 < K ∧ 0 < xl K - 1 / 2 ∧ xl K < xs K) ∧
    Tendsto (fun K => xs K - 1 / 2) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun K => (xs K - 1 / 2) ^ 3 / K) (𝓝[>] 0) (𝓝 (9 * P.σ2 / (4 * P.δ))) ∧
    Tendsto (fun K => (xl K - 1 / 2) ^ 3 / K) (𝓝[>] 0) (𝓝 (9 * P.σ2 / (4 * P.δ))) ∧
    Tendsto (fun K => (xs K - xl K) ^ 3 / K ^ 2) (𝓝[>] 0) (𝓝 (P.δ * P.σ2 ^ 2 / 18)) := by
  have hP' := hP
  obtain ⟨hr, hs, hd⟩ := hP'
  have hL : 0 < lam P := Real.sqrt_pos.2 (by positivity)
  have hL2 : lam P ^ 2 = 2 * P.r / P.σ2 := Real.sq_sqrt (by positivity)
  have hev : ∀ᶠ K in 𝓝[>] (0 : ℝ), 0 < K ∧ IsThresholdPair P K (xl K) (xs K) :=
    (eventually_mem_nhdsWithin).and hB
  have hpt := hev.mono fun K hK => And.intro hK.1
    (pt P hP K (xs K - 1 / 2) (xl K - 1 / 2) hK.1 (by rw [sub_add_cancel, sub_add_cancel]; exact hK.2))
  clear hev
  set L := lam P with hLdef
  clear_value L
  set b := 2 * P.δ / (3 * L) with hb
  have hb0 : 0 < b := by positivity
  set F := 𝓝[>] (0 : ℝ) with hF
  set U := fun K => xs K - 1 / 2 with hU
  set V := fun K => xl K - 1 / 2 with hV
  set W := fun K => L * (U K + V K) with hW
  -- Step 1: W → 0
  have hWpos : ∀ᶠ K in F, 0 < W K := hpt.mono fun K hK => hK.2.2.2.2.1
  have hW0 : Tendsto W F (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => hWpos.mono fun K hK => lt_trans ha hK, fun a ha => ?_⟩
    set e := min a (1 / 12) with he
    have he0 : 0 < e := lt_min ha (by norm_num)
    have he1 : e ≤ 1 / 12 := min_le_right _ _
    have hNe : e ^ 3 / 12 ≤ NN e := by
      have := NN_bound he0.le (by linarith)
      have h4 : e ^ 4 ≤ e ^ 3 / 12 := by
        have : e ^ 4 = e * e ^ 3 := by ring
        rw [this]; nlinarith [pow_pos he0 3]
      linarith [(abs_le.1 this).1]
    have hNb : 0 < NN e * b := mul_pos (lt_of_lt_of_le (by positivity) hNe) hb0
    have hlin : Tendsto (fun K => 4 * P.r * (Real.exp L + 1) * K) F (𝓝 0) := by
      have : Tendsto (fun K : ℝ => 4 * P.r * (Real.exp L + 1) * K) (𝓝 0)
          (𝓝 (4 * P.r * (Real.exp L + 1) * 0)) := tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    filter_upwards [hpt, hlin.eventually (gt_mem_nhds hNb)] with K hK hCK
    obtain ⟨-, -, -, -, -, -, -, hNK, -, -⟩ := hK
    by_contra hc
    push Not at hc
    have h1 : NN e ≤ NN (W K) := NN_mono (le_trans (min_le_left _ _) hc)
    have h2 : NN e * b ≤ NN (W K) * b := mul_le_mul_of_nonneg_right h1 hb0.le
    have : NN (W K) * b ≤ 4 * P.r * (Real.exp L + 1) * K := hNK
    linarith
  -- Step 2: U → 0
  have hU0 : Tendsto U F (𝓝 0) := by
    have hWL : Tendsto (fun K => W K / L) F (𝓝 0) := by simpa using hW0.div_const L
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hWL ?_ ?_
    · filter_upwards [hpt] with K hK
      obtain ⟨-, hv, hvu, -⟩ := hK
      exact le_of_lt (lt_trans hv hvu)
    · filter_upwards [hpt] with K hK
      obtain ⟨-, hv, -⟩ := hK
      rw [le_div_iff₀ hL]
      simp only [hW, hU, hV]
      nlinarith
  have hUpos : ∀ᶠ K in F, 0 < U K := hpt.mono fun K hK => lt_trans hK.2.1 hK.2.2.1
  -- Step 3: D/U → 0
  have hDU : Tendsto (fun K => (U K - V K) / U K) F (𝓝 0) := by
    have hup : Tendsto (fun K => 2 * P.δ / 3 * U K) F (𝓝 0) := by
      simpa using hU0.const_mul (2 * P.δ / 3)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hpt] with K hK
      obtain ⟨-, hv, hvu, -⟩ := hK
      apply div_nonneg <;> simp only [hU, hV] <;> linarith
    · filter_upwards [hpt] with K hK
      obtain ⟨-, hv, hvu, -, -, -, hD, -⟩ := hK
      have hu : 0 < U K := lt_trans hv hvu
      rw [div_le_iff₀ hu]
      simp only [hU, hV] at hD hu ⊢
      nlinarith
  have hD0 : Tendsto (fun K => U K - V K) F (𝓝 0) := by
    have := hDU.mul hU0
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [hUpos] with K hK
    field_simp
  -- Step 4: V/U → 1
  have hVU : Tendsto (fun K => V K / U K) F (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hDU
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hUpos] with K hK
    field_simp
    ring
  -- Step 5: W/U → 2L
  have hWU : Tendsto (fun K => W K / U K) F (𝓝 (2 * L)) := by
    have := ((tendsto_const_nhds (x := (2 : ℝ))).sub hDU).const_mul L
    rw [sub_zero, mul_comm L 2] at this
    refine this.congr' ?_
    filter_upwards [hUpos] with K hK
    simp only [hW]
    field_simp
    ring
  have hNNr := NN_ratio hW0 hWpos
  have hEr := exp_ratio hW0 hWpos
  have hEx : Tendsto (fun K => Real.exp (W K)) F (𝓝 1) := by
    have := (Real.continuous_exp.tendsto 0).comp hW0
    rw [Real.exp_zero] at this
    exact this
  -- Step 9: U^3/K
  have hU3 : Tendsto (fun K => U K ^ 3 / K) F (𝓝 (9 * P.σ2 / (4 * P.δ))) := by
    have hy : Tendsto (fun K => (Real.exp (W K) + 1) / (2 - 2 * P.δ / 3 * (U K - V K))) F
        (𝓝 ((1 + 1) / (2 - 2 * P.δ / 3 * 0))) :=
      (hEx.add tendsto_const_nhds).div (tendsto_const_nhds.sub (hD0.const_mul _)) (by norm_num)
    have hUW : Tendsto (fun K => U K / W K) F (𝓝 (2 * L)⁻¹) := by
      have := hWU.inv₀ (by positivity)
      refine this.congr' ?_
      filter_upwards with K
      simp [inv_div]
    have hWN : Tendsto (fun K => W K ^ 3 / NN (W K)) F (𝓝 (1 / 6)⁻¹) := by
      have := hNNr.inv₀ (by norm_num)
      refine this.congr' ?_
      filter_upwards with K
      simp [inv_div]
    have := ((tendsto_const_nhds (x := 4 * P.r / b)).mul hy).mul (hUW.pow 3) |>.mul hWN
    have hval : 4 * P.r / b * ((1 + 1) / (2 - 2 * P.δ / 3 * 0)) * ((2 * L)⁻¹) ^ 3 * (1 / 6)⁻¹
        = 9 * P.σ2 / (4 * P.δ) := by
      have hr' : P.r = L ^ 2 * P.σ2 / 2 := by rw [hL2]; field_simp
      rw [hb, hr']
      field_simp
      ring
    rw [hval] at this
    refine this.congr' ?_
    filter_upwards [hpt] with K hK
    obtain ⟨hK0, -, -, -, -, -, -, -, hid, -⟩ := hK
    exact hid.symm
  -- Step 10: D/U^2
  have hDU2 : Tendsto (fun K => (U K - V K) / U K ^ 2) F (𝓝 (2 * P.δ / 9)) := by
    have := (tendsto_const_nhds (x := 3 / (2 * P.δ))).mul
      (((tendsto_const_nhds (x := 2 * P.δ ^ 2 / 9)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add (hVU.pow 2))).sub
        ((((tendsto_const_nhds (x := b ^ 2)).mul hNNr).mul hEr).mul (hWU.pow 2)))
    have hval : 3 / (2 * P.δ) * (2 * P.δ ^ 2 / 9 * (1 + 1 ^ 2) - b ^ 2 * (1 / 6) * 1 * (2 * L) ^ 2)
        = 2 * P.δ / 9 := by
      rw [hb]
      field_simp
      ring
    rw [hval] at this
    refine this.congr' ?_
    filter_upwards [hpt] with K hK
    obtain ⟨hK0, -, -, -, -, -, -, -, -, hid⟩ := hK
    exact hid.symm
  refine ⟨?_, hU0, hU3, ?_, ?_⟩
  · filter_upwards [hpt] with K hK
    obtain ⟨hK0, hv, hvu, -⟩ := hK
    exact ⟨hK0, hv, by linarith⟩
  · have := hU3.mul (hVU.pow 3)
    rw [one_pow, mul_one] at this
    refine this.congr' ?_
    filter_upwards [hUpos] with K hK
    have hu : U K ^ 3 ≠ 0 := pow_ne_zero 3 hK.ne'
    show U K ^ 3 / K * (V K / U K) ^ 3 = V K ^ 3 / K
    rw [div_pow, div_mul_div_comm, mul_comm (U K ^ 3) (V K ^ 3), mul_div_mul_right _ _ hu]
  · have := (hDU2.pow 3).mul (hU3.pow 2)
    have hval : (2 * P.δ / 9) ^ 3 * (9 * P.σ2 / (4 * P.δ)) ^ 2 = P.δ * P.σ2 ^ 2 / 18 := by
      field_simp
      ring
    rw [hval] at this
    refine this.congr' ?_
    filter_upwards [hpt] with K hK
    obtain ⟨hK0, hv, hvu, -⟩ := hK
    have hu : 0 < U K := lt_trans hv hvu
    have : xs K - xl K = U K - V K := by simp only [hU, hV]; ring
    rw [this]
    field_simp

lemma genA {l : Filter ℝ} {X : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hX : Tendsto X l (𝓝 0))
    (hpos : ∀ᶠ K in l, 0 < K ∧ 0 < X K) (h3 : Tendsto (fun K => X K ^ 3 / K) l (𝓝 c)) :
    Tendsto (fun K => X K / K) l atTop := by
  have hX2 : Tendsto (fun K => X K ^ 2) l (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hpos.mono fun K h => pow_pos h.2 2⟩
    simpa using hX.pow 2
  have hinv := tendsto_inv_nhdsGT_zero.comp hX2
  have := Filter.Tendsto.pos_mul_atTop hc h3 hinv
  refine this.congr' ?_
  filter_upwards [hpos] with K hK
  have h1 : K ≠ 0 := hK.1.ne'
  have h2 : X K ≠ 0 := hK.2.ne'
  simp only [Function.comp]
  field_simp

lemma genB {l : Filter ℝ} {X Y q : ℝ → ℝ} {a c : ℝ} (hac : a < c)
    (hX : Tendsto (fun K => X K ^ 3 / q K) l (𝓝 a)) (hY : Tendsto (fun K => Y K ^ 3 / q K) l (𝓝 c))
    (hpos : ∀ᶠ K in l, 0 < q K ∧ 0 ≤ Y K) : ∀ᶠ K in l, X K < Y K := by
  filter_upwards [hX.eventually_lt hY hac, hpos] with K h1 h2
  have := (div_lt_div_iff_of_pos_right h2.1).1 h1
  exact lt_of_pow_lt_pow_left₀ 3 h2.2 this

lemma genC {l : Filter ℝ} {X Y : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hX : Tendsto (fun K => X K ^ 3 / K) l (𝓝 a)) (hY : Tendsto (fun K => Y K ^ 3 / K) l (𝓝 a))
    (hpos : ∀ᶠ K in l, 0 < K ∧ 0 < X K ∧ 0 < Y K) :
    Tendsto (fun K => (X K - Y K) / X K) l (𝓝 0) := by
  have hr : Tendsto (fun K => (Y K ^ 3 / K) / (X K ^ 3 / K)) l (𝓝 1) := by
    have := hY.div hX ha.ne'
    rwa [div_self ha.ne'] at this
  have hg : Tendsto (fun K => |(Y K ^ 3 / K) / (X K ^ 3 / K) - 1|) l (𝓝 0) := by
    have := (hr.sub_const 1).abs
    simpa using this
  apply tendsto_of_abs_sub_le hg
  filter_upwards [hpos] with K hK
  obtain ⟨hK, hx, hy⟩ := hK
  have hρ : 0 ≤ Y K / X K := by positivity
  have e1 : (Y K ^ 3 / K) / (X K ^ 3 / K) = (Y K / X K) ^ 3 := by
    rw [div_div_div_cancel_right₀ hK.ne', div_pow]
  have e2 : (X K - Y K) / X K - 0 = -(Y K / X K - 1) := by
    field_simp
    ring
  rw [e1, e2, abs_neg]
  set ρ := Y K / X K
  rw [show ρ ^ 3 - 1 = (ρ - 1) * (ρ ^ 2 + ρ + 1) by ring, abs_mul,
    abs_of_pos (by positivity : 0 < ρ ^ 2 + ρ + 1)]
  exact le_mul_of_one_le_right (abs_nonneg _) (by nlinarith)

end FCSC35

open Filter Topology FollowCustomers.SmallCost in
theorem solution :
    (∀ (P : Params) (xl xs : ℝ → ℝ), P.Standing → IsBranch P xl xs →
      Tendsto (fun K => (xs K - 1 / 2) / K) (𝓝[>] 0) atTop ∧
        Tendsto (fun K => (xl K - 1 / 2) / K) (𝓝[>] 0) atTop) ∧
    (∀ (P₁ P₂ : Params) (xl₁ xs₁ xl₂ xs₂ : ℝ → ℝ), P₁.Standing → P₂.Standing →
      P₁.r = P₂.r → P₁.δ = P₂.δ → P₁.σ2 < P₂.σ2 →
      IsBranch P₁ xl₁ xs₁ → IsBranch P₂ xl₂ xs₂ →
      ∀ᶠ K in 𝓝[>] 0, xs₁ K < xs₂ K ∧ xl₁ K < xl₂ K ∧ xs₁ K - xl₁ K < xs₂ K - xl₂ K) ∧
    (∀ (P₁ P₂ : Params) (xl₁ xs₁ xl₂ xs₂ : ℝ → ℝ), P₁.Standing → P₂.Standing →
      P₁.r = P₂.r → P₁.σ2 = P₂.σ2 → P₁.δ < P₂.δ →
      IsBranch P₁ xl₁ xs₁ → IsBranch P₂ xl₂ xs₂ →
      ∀ᶠ K in 𝓝[>] 0, xs₂ K < xs₁ K ∧ xl₂ K < xl₁ K ∧ xs₁ K - xl₁ K < xs₂ K - xl₂ K) ∧
    (∀ (P₁ P₂ : Params) (xl₁ xs₁ xl₂ xs₂ : ℝ → ℝ), P₁.Standing → P₂.Standing →
      P₁.σ2 = P₂.σ2 → P₁.δ = P₂.δ →
      IsBranch P₁ xl₁ xs₁ → IsBranch P₂ xl₂ xs₂ →
      Tendsto (fun K => (xs₁ K - xs₂ K) / (xs₁ K - 1 / 2)) (𝓝[>] 0) (𝓝 0) ∧
        Tendsto (fun K => (xl₁ K - xl₂ K) / (xl₁ K - 1 / 2)) (𝓝[>] 0) (𝓝 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P xl xs hP hB
    obtain ⟨hev, hU0, hU3, hV3, -⟩ := FCSC35.core P hP xl xs hB
    have hc : 0 < 9 * P.σ2 / (4 * P.δ) := by
      obtain ⟨-, hs, hd⟩ := hP; positivity
    have hV0 : Tendsto (fun K => xl K - 1 / 2) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU0 ?_ ?_
      · filter_upwards [hev] with K h; exact h.2.1.le
      · filter_upwards [hev] with K h; linarith [h.2.2]
    constructor
    · exact FCSC35.genA (X := fun K => xs K - 1 / 2) hc hU0
        (hev.mono fun K h => ⟨h.1, by linarith [h.2.1, h.2.2]⟩) hU3
    · exact FCSC35.genA (X := fun K => xl K - 1 / 2) hc hV0 (hev.mono fun K h => ⟨h.1, h.2.1⟩) hV3
  · intro P₁ P₂ xl₁ xs₁ xl₂ xs₂ h1 h2 hr hd hs hB1 hB2
    obtain ⟨ev1, -, U31, V31, D31⟩ := FCSC35.core P₁ h1 xl₁ xs₁ hB1
    obtain ⟨ev2, -, U32, V32, D32⟩ := FCSC35.core P₂ h2 xl₂ xs₂ hB2
    obtain ⟨-, hs1, hd1⟩ := h1
    have hA : 9 * P₁.σ2 / (4 * P₁.δ) < 9 * P₂.σ2 / (4 * P₂.δ) := by
      rw [hd]; apply div_lt_div_of_pos_right _ (by rw [← hd]; positivity); linarith
    have hC : P₁.δ * P₁.σ2 ^ 2 / 18 < P₂.δ * P₂.σ2 ^ 2 / 18 := by
      rw [hd]
      have : P₁.σ2 ^ 2 < P₂.σ2 ^ 2 := by nlinarith
      have hd2 : 0 < P₂.δ := by rw [← hd]; exact hd1
      nlinarith
    have e1 := FCSC35.genB (X := fun K => xs₁ K - 1 / 2) (Y := fun K => xs₂ K - 1 / 2) (q := fun K => K)
      hA U31 U32 (by filter_upwards [ev2] with K b; exact ⟨b.1, by linarith [b.2.1, b.2.2]⟩)
    have e2 := FCSC35.genB (X := fun K => xl₁ K - 1 / 2) (Y := fun K => xl₂ K - 1 / 2) (q := fun K => K)
      hA V31 V32 (by filter_upwards [ev2] with K b; exact ⟨b.1, b.2.1.le⟩)
    have e3 := FCSC35.genB (X := fun K => xs₁ K - xl₁ K) (Y := fun K => xs₂ K - xl₂ K)
      (q := fun K => K ^ 2) hC D31 D32
      (by filter_upwards [ev2] with K b; exact ⟨by have := b.1; positivity, by linarith [b.2.2]⟩)
    filter_upwards [e1, e2, e3] with K a b c
    exact ⟨by linarith, by linarith, c⟩
  · intro P₁ P₂ xl₁ xs₁ xl₂ xs₂ h1 h2 hr hs hd hB1 hB2
    obtain ⟨ev1, -, U31, V31, D31⟩ := FCSC35.core P₁ h1 xl₁ xs₁ hB1
    obtain ⟨ev2, -, U32, V32, D32⟩ := FCSC35.core P₂ h2 xl₂ xs₂ hB2
    obtain ⟨-, hs1, hd1⟩ := h1
    have hA : 9 * P₂.σ2 / (4 * P₂.δ) < 9 * P₁.σ2 / (4 * P₁.δ) := by
      rw [hs]; apply div_lt_div_of_pos_left (by rw [← hs]; positivity) (by positivity); linarith
    have hC : P₁.δ * P₁.σ2 ^ 2 / 18 < P₂.δ * P₂.σ2 ^ 2 / 18 := by
      rw [hs]
      have : 0 < P₂.σ2 ^ 2 := by rw [← hs]; positivity
      nlinarith
    have e1 := FCSC35.genB (X := fun K => xs₂ K - 1 / 2) (Y := fun K => xs₁ K - 1 / 2) (q := fun K => K)
      hA U32 U31 (by filter_upwards [ev1] with K b; exact ⟨b.1, by linarith [b.2.1, b.2.2]⟩)
    have e2 := FCSC35.genB (X := fun K => xl₂ K - 1 / 2) (Y := fun K => xl₁ K - 1 / 2) (q := fun K => K)
      hA V32 V31 (by filter_upwards [ev1] with K b; exact ⟨b.1, b.2.1.le⟩)
    have e3 := FCSC35.genB (X := fun K => xs₁ K - xl₁ K) (Y := fun K => xs₂ K - xl₂ K)
      (q := fun K => K ^ 2) hC D31 D32
      (by filter_upwards [ev2] with K b; exact ⟨by have := b.1; positivity, by linarith [b.2.2]⟩)
    filter_upwards [e1, e2, e3] with K a b c
    exact ⟨by linarith, by linarith, c⟩
  · intro P₁ P₂ xl₁ xs₁ xl₂ xs₂ h1 h2 hs hd hB1 hB2
    obtain ⟨ev1, -, U31, V31, -⟩ := FCSC35.core P₁ h1 xl₁ xs₁ hB1
    obtain ⟨ev2, -, U32, V32, -⟩ := FCSC35.core P₂ h2 xl₂ xs₂ hB2
    have hc : 0 < 9 * P₁.σ2 / (4 * P₁.δ) := by
      obtain ⟨-, hs, hd⟩ := h1; positivity
    rw [hs, hd] at U31 V31 hc
    constructor
    · have := FCSC35.genC (X := fun K => xs₁ K - 1 / 2) (Y := fun K => xs₂ K - 1 / 2) hc U31 U32
        (by filter_upwards [ev1, ev2] with K a b
            exact ⟨a.1, by linarith [a.2.1, a.2.2], by linarith [b.2.1, b.2.2]⟩)
      refine this.congr fun K => ?_
      ring
    · have := FCSC35.genC (X := fun K => xl₁ K - 1 / 2) (Y := fun K => xl₂ K - 1 / 2) hc V31 V32
        (by filter_upwards [ev1, ev2] with K a b
            exact ⟨a.1, a.2.1, b.2.1⟩)
      refine this.congr fun K => ?_
      ring
