-- Prove2me | solution 1 for Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/51c85d21-8427-539d-8169-c2e04357f44d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant

set_option autoImplicit false

namespace SlDigammaSeries

open Filter Topology Finset Set

noncomputable def term (s : ℂ) (k : ℕ) : ℂ := 1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s)

noncomputable def rterm (x : ℝ) (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + x)

theorem term_ofReal (x : ℝ) (k : ℕ) : term (x : ℂ) k = ((rterm x k : ℝ) : ℂ) := by
  simp only [term, rterm]
  push_cast
  rfl

theorem re_natCast_add (s : ℂ) (k : ℕ) : ((k : ℂ) + s).re = (k : ℝ) + s.re := by simp

theorem le_norm_natCast_add (s : ℂ) (k : ℕ) : (k : ℝ) + s.re ≤ ‖(k : ℂ) + s‖ := by
  rw [← re_natCast_add]; exact Complex.re_le_norm _

theorem le_norm_natCast_add_one (k : ℕ) : (k : ℝ) + 1 ≤ ‖(k : ℂ) + 1‖ := by
  have := le_norm_natCast_add 1 k
  simpa using this

theorem natCast_add_ne_zero {s : ℂ} (hs : 0 < s.re) (k : ℕ) : ((k : ℂ) + s) ≠ 0 := fun h => by
  have := le_norm_natCast_add s k
  rw [h, norm_zero] at this
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem norm_term_le_tail {s : ℂ} (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖term s k‖ ≤ ‖s - 1‖ * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hn1 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + 1‖ := le_norm_natCast_add_one k
  have hns : (k : ℝ) ≤ ‖(k : ℂ) + s‖ := le_trans (by linarith) (le_norm_natCast_add s k)
  have hne1 : ((k : ℂ) + 1) ≠ 0 := fun h => by
    have := hn1; rw [h, norm_zero] at this; linarith
  have hnes : ((k : ℂ) + s) ≠ 0 := natCast_add_ne_zero hs k
  have heq : term s k = (s - 1) / (((k : ℂ) + 1) * ((k : ℂ) + s)) := by
    unfold term
    field_simp
    ring
  rw [heq, norm_div, norm_mul]
  calc ‖s - 1‖ / (‖(k : ℂ) + 1‖ * ‖(k : ℂ) + s‖) ≤ ‖s - 1‖ / (((k : ℝ) + 1) * (k : ℝ)) := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        exact mul_le_mul hn1 hns hkpos.le (norm_nonneg _)
    _ = ‖s - 1‖ * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
        field_simp
        ring

theorem sum_Ico_one_div_sub (N : ℕ) (hN : 1 ≤ N) (m : ℕ) (hm : N ≤ m) :
    ∑ k ∈ Ico N m, (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) = 1 / (N : ℝ) - 1 / (m : ℝ) := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hNm ih =>
    rw [Finset.sum_Ico_succ_top hNm, ih]
    push_cast
    ring

theorem summable_norm_term {s : ℂ} (hs : 0 < s.re) : Summable fun k => ‖term s k‖ := by
  refine summable_of_sum_range_le (c := ‖term s 0‖ + ‖s - 1‖) (fun _ => norm_nonneg _) fun n => ?_
  rcases Nat.lt_or_ge n 1 with hn | hn
  · have : n = 0 := by omega
    subst this
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · rw [← Finset.sum_range_add_sum_Ico _ hn, Finset.sum_range_one]
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have htail : ∑ k ∈ Ico 1 n, ‖term s k‖ ≤ ‖s - 1‖ := by
      calc ∑ k ∈ Ico 1 n, ‖term s k‖ ≤ ∑ k ∈ Ico 1 n, ‖s - 1‖ * (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) :=
            Finset.sum_le_sum fun k hk => norm_term_le_tail hs (Finset.mem_Ico.mp hk).1
        _ = ‖s - 1‖ * (1 / ((1 : ℕ) : ℝ) - 1 / (n : ℝ)) := by
            rw [← Finset.mul_sum, sum_Ico_one_div_sub 1 le_rfl n hn]
        _ ≤ ‖s - 1‖ * 1 := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            have : 0 ≤ 1 / (n : ℝ) := by positivity
            push_cast
            linarith
        _ = ‖s - 1‖ := mul_one _
    linarith

theorem summable_term {s : ℂ} (hs : 0 < s.re) : Summable (term s) :=
  (summable_norm_term hs).of_norm

theorem summable_rterm {x : ℝ} (hx : 0 < x) : Summable (rterm x) := by
  have h : Summable (term (x : ℂ)) := summable_term (s := (x : ℂ)) (by simpa using hx)
  have e : (term (x : ℂ)) = fun k => ((rterm x k : ℝ) : ℂ) := funext (term_ofReal x)
  rw [e] at h
  exact Complex.summable_ofReal.mp h

noncomputable def T (x : ℝ) : ℝ := ∑' k, rterm x k

theorem T_one : T 1 = 0 := by
  simp [T, rterm]

theorem T_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : T x ≤ T y := by
  unfold T
  refine (summable_rterm hx).tsum_le_tsum (fun k => ?_) (summable_rterm (lt_of_lt_of_le hx hxy))
  unfold rterm
  have hkx : (0 : ℝ) < (k : ℝ) + x := by positivity
  have : 1 / ((k : ℝ) + y) ≤ 1 / ((k : ℝ) + x) := one_div_le_one_div_of_le hkx (by linarith)
  linarith

theorem T_add_one {x : ℝ} (hx : 0 < x) : T (x + 1) = T x + 1 / x := by
  set b : ℕ → ℝ := fun k => 1 / ((k : ℝ) + x) with hb
  have hb0 : b 0 = 1 / x := by simp [hb]
  have hbt : Tendsto b atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + x) atTop atTop :=
      tendsto_atTop_add_const_right _ x tendsto_natCast_atTop_atTop
    have := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h1
    simpa [hb] using this
  have hnn : ∀ k : ℕ, 0 ≤ b k - b (k + 1) := fun k => by
    simp only [hb]
    have hkx : (0 : ℝ) < (k : ℝ) + x := by positivity
    have : 1 / (((k + 1 : ℕ) : ℝ) + x) ≤ 1 / ((k : ℝ) + x) :=
      one_div_le_one_div_of_le hkx (by push_cast; linarith)
    linarith
  have hsum : HasSum (fun k : ℕ => b k - b (k + 1)) (1 / x) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
    have e : (fun n : ℕ => ∑ i ∈ range n, (b i - b (i + 1))) = fun n => b 0 - b n :=
      funext fun n => Finset.sum_range_sub' b n
    rw [e, ← hb0]
    have := (tendsto_const_nhds (x := b 0)).sub hbt
    simpa using this
  have hterm : ∀ k : ℕ, rterm (x + 1) k = rterm x k + (b k - b (k + 1)) := fun k => by
    simp only [rterm, hb]
    push_cast
    ring
  calc T (x + 1) = ∑' k, (rterm x k + (b k - b (k + 1))) := tsum_congr hterm
    _ = ∑' k, rterm x k + ∑' k, (b k - b (k + 1)) := (summable_rterm hx).tsum_add hsum.summable
    _ = T x + 1 / x := by rw [hsum.tsum_eq]; rfl

theorem T_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) : T (x + n) = T x + ∑ k ∈ range n, 1 / (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x + n := by positivity
    rw [Nat.cast_succ, ← add_assoc, T_add_one hxn, ih, Finset.sum_range_succ]
    ring

theorem T_nat_succ (n : ℕ) : T ((n : ℝ) + 1) = ∑ k ∈ range n, 1 / ((k : ℝ) + 1) := by
  have h := T_add_nat one_pos n
  rw [T_one, zero_add] at h
  rw [add_comm, h]
  exact Finset.sum_congr rfl fun k _ => by ring

noncomputable def ψ (x : ℝ) : ℝ := deriv (Real.log ∘ Real.Gamma) x

theorem ne_neg_nat {x : ℝ} (hx : 0 < x) (m : ℕ) : x ≠ -(m : ℝ) := by
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  intro h; linarith

theorem differentiableAt_logGamma {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x :=
  (Real.differentiableAt_Gamma (ne_neg_nat hx)).log (Real.Gamma_pos_of_pos hx).ne'

theorem logGamma_add_one {x : ℝ} (hx : 0 < x) :
    (Real.log ∘ Real.Gamma) (x + 1) = (Real.log ∘ Real.Gamma) x + Real.log x := by
  simp only [Function.comp_apply, Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne',
    add_comm]

theorem ψ_add_one {x : ℝ} (hx : 0 < x) : ψ (x + 1) = ψ x + 1 / x := by
  unfold ψ
  rw [← deriv_comp_add_const, one_div, ← Real.deriv_log x,
    ← deriv_add (differentiableAt_logGamma hx) (Real.differentiableAt_log hx.ne')]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact logGamma_add_one hy

theorem ψ_one : ψ 1 = -Real.eulerMascheroniConstant := by
  unfold ψ
  rw [Function.comp_def, deriv.log (Real.differentiableAt_Gamma (ne_neg_nat one_pos)) (by positivity),
    Real.Gamma_one, div_one, Real.eulerMascheroniConstant_eq_neg_deriv, neg_neg]

theorem ψ_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) : ψ (x + n) = ψ x + ∑ k ∈ range n, 1 / (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x + n := by positivity
    rw [Nat.cast_succ, ← add_assoc, ψ_add_one hxn, ih, Finset.sum_range_succ]
    ring

theorem ψ_nat_succ (n : ℕ) : ψ ((n : ℝ) + 1) = -Real.eulerMascheroniConstant + ∑ k ∈ range n, 1 / ((k : ℝ) + 1) := by
  have h := ψ_add_nat one_pos n
  rw [ψ_one] at h
  rw [add_comm, h]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ψ_mono : MonotoneOn ψ (Ioi 0) := by
  show MonotoneOn (deriv (Real.log ∘ Real.Gamma)) (Ioi 0)
  exact Real.convexOn_log_Gamma.monotoneOn_deriv fun x hx => differentiableAt_logGamma hx

theorem ψ_add_euler_eq_T {x : ℝ} (hx : 0 < x) : ψ x + Real.eulerMascheroniConstant = T x := by
  set a : ℕ := ⌊x⌋₊ with ha
  have hax : (a : ℝ) ≤ x := Nat.floor_le hx.le
  have hxa : x < (a : ℝ) + 1 := Nat.lt_floor_add_one x
  have key : ∀ n : ℕ, 1 ≤ n → |ψ x + Real.eulerMascheroniConstant - T x| ≤ 1 / ((a : ℝ) + n) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set m : ℕ := a + n with hm
    have hmR : (m : ℝ) = (a : ℝ) + n := by rw [hm]; push_cast; ring
    have hmpos : (0 : ℝ) < (m : ℝ) := by rw [hmR]; linarith [Nat.cast_nonneg (α := ℝ) a]
    have hxn : 0 < x + n := by positivity
    have hxm : (m : ℝ) ≤ x + n := by rw [hmR]; linarith
    have hxm' : x + n ≤ (m : ℝ) + 1 := by rw [hmR]; linarith

    have hTm1 : T ((m : ℝ) + 1) = T m + 1 / (m : ℝ) := T_add_one hmpos
    have hψm1 : ψ ((m : ℝ) + 1) + Real.eulerMascheroniConstant = T ((m : ℝ) + 1) := by
      rw [ψ_nat_succ, T_nat_succ]; ring
    have hψm : ψ (m : ℝ) + Real.eulerMascheroniConstant = T (m : ℝ) := by
      obtain ⟨j, hj⟩ : ∃ j : ℕ, m = j + 1 := ⟨m - 1, by omega⟩
      rw [hj]; push_cast
      rw [ψ_nat_succ, T_nat_succ]; ring

    have h1 : ψ (m : ℝ) ≤ ψ (x + n) := ψ_mono (mem_Ioi.mpr hmpos) (mem_Ioi.mpr hxn) hxm
    have h2 : ψ (x + n) ≤ ψ ((m : ℝ) + 1) := ψ_mono (mem_Ioi.mpr hxn) (mem_Ioi.mpr (by linarith)) hxm'
    have h3 : T (m : ℝ) ≤ T (x + n) := T_mono hmpos hxm
    have h4 : T (x + n) ≤ T ((m : ℝ) + 1) := T_mono hxn hxm'
    have h5 : ψ (x + n) - T (x + n) = ψ x - T x := by
      rw [ψ_add_nat hx, T_add_nat hx]; ring
    rw [← hmR, abs_le]
    constructor <;> linarith
  have hlim : Tendsto (fun n : ℕ => 1 / ((a : ℝ) + n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (a : ℝ) + n) atTop atTop :=
      tendsto_atTop_add_const_left _ (a : ℝ) tendsto_natCast_atTop_atTop
    have := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h1
    simpa using this
  have hle : |ψ x + Real.eulerMascheroniConstant - T x| ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, key⟩)
  have := abs_nonpos_iff.mp hle
  linarith

theorem re_pos_ne_neg_nat {s : ℂ} (hs : 0 < s.re) (m : ℕ) : s ≠ -(m : ℂ) := fun h => by
  have := congrArg Complex.re h
  rw [Complex.neg_re, Complex.natCast_re] at this
  linarith [Nat.cast_nonneg (α := ℝ) m]

theorem deriv_Gamma_ofReal {x : ℝ} (hx : 0 < x) :
    deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hc : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma _ (re_pos_ne_neg_nat (by simpa using hx))
  have hr : DifferentiableAt ℝ Real.Gamma x := Real.differentiableAt_Gamma (ne_neg_nat hx)
  have h1 : HasDerivAt (fun y : ℝ => Complex.Gamma (y : ℂ)) (deriv Complex.Gamma (x : ℂ)) x :=
    hc.hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => Complex.Gamma (y : ℂ)) ((deriv Real.Gamma x : ℝ) : ℂ) x := by
    have h := hr.hasDerivAt.ofReal_comp
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => Complex.Gamma_ofReal y)
  exact h1.unique h2

theorem digamma_ofReal {x : ℝ} (hx : 0 < x) : Complex.digamma (x : ℂ) = ((ψ x : ℝ) : ℂ) := by
  rw [Complex.digamma_def, logDeriv_apply, deriv_Gamma_ofReal hx, Complex.Gamma_ofReal]
  unfold ψ
  rw [Function.comp_def, deriv.log (Real.differentiableAt_Gamma (ne_neg_nat hx)) (Real.Gamma_pos_of_pos hx).ne']
  push_cast
  rfl

theorem real_case {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) + (Real.eulerMascheroniConstant : ℂ) = ∑' k, term (x : ℂ) k := by
  have e : (term (x : ℂ)) = fun k => ((rterm x k : ℝ) : ℂ) := funext (term_ofReal x)
  rw [digamma_ofReal hx, e, ← Complex.ofReal_tsum]
  show ((ψ x : ℝ) : ℂ) + (Real.eulerMascheroniConstant : ℂ) = ((T x : ℝ) : ℂ)
  rw [← ψ_add_euler_eq_T hx]
  push_cast
  rfl

def U : Set ℂ := {s | 0 < s.re}

theorem isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_U : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected

theorem hasDerivAt_term (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z => term z k) (1 / ((k : ℂ) + s) ^ 2) s := by
  have hne : ((k : ℂ) + s) ≠ 0 := natCast_add_ne_zero hs k
  have h : HasDerivAt (fun z => term z k)
      (0 - (0 * ((k : ℂ) + s) - 1 * 1) / ((k : ℂ) + s) ^ 2) s :=
    (hasDerivAt_const s ((1 : ℂ) / ((k : ℂ) + 1))).sub
      ((hasDerivAt_const s (1 : ℂ)).div ((hasDerivAt_id s).const_add (k : ℂ)) hne)
  refine h.congr_deriv ?_
  ring

theorem differentiableAt_T {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (fun z => ∑' k, term z k) s := by
  set δ : ℝ := s.re / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set δ₁ : ℝ := min δ 1 with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min hδpos one_pos
  have hδ₁δ : δ₁ ≤ δ := min_le_left _ _
  have hδ₁1 : δ₁ ≤ 1 := min_le_right _ _
  set t : Set ℂ := {z | δ < z.re} with ht
  have hto : IsOpen t := isOpen_lt continuous_const Complex.continuous_re
  have htc : IsPreconnected t := (convex_halfSpace_re_gt δ).isPreconnected
  have hst : s ∈ t := by show δ < s.re; rw [hδ]; linarith
  have hp : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  have hu : Summable (fun k : ℕ => δ₁⁻¹ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2)) := hp.mul_left _
  refine (hasDerivAt_tsum_of_isPreconnected hu hto htc (fun k z hz => hasDerivAt_term k (lt_trans hδpos hz))
    (fun k z hz => ?_) hst (summable_term hs) hst).differentiableAt
  have hz : δ < z.re := hz
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkz : δ₁ * ((k : ℝ) + 1) ≤ ‖(k : ℂ) + z‖ := by
    have h1 : (k : ℝ) + z.re ≤ ‖(k : ℂ) + z‖ := le_norm_natCast_add z k
    nlinarith [mul_le_of_le_one_right hk0 hδ₁1]
  have hpos : 0 < δ₁ * ((k : ℝ) + 1) := by positivity
  rw [norm_div, norm_one, norm_pow]
  calc 1 / ‖(k : ℂ) + z‖ ^ 2 ≤ 1 / (δ₁ * ((k : ℝ) + 1)) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hkz 2)
    _ = δ₁⁻¹ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
        field_simp

theorem analyticOnNhd_T : AnalyticOnNhd ℂ (fun z => ∑' k, term z k) U :=
  DifferentiableOn.analyticOnNhd (fun s hs => (differentiableAt_T hs).differentiableWithinAt) isOpen_U

theorem analyticOnNhd_digamma_add :
    AnalyticOnNhd ℂ (fun s => Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) U := by
  have hΓ : DifferentiableOn ℂ Complex.Gamma U := fun s hs =>
    (Complex.differentiableAt_Gamma s (re_pos_ne_neg_nat hs)).differentiableWithinAt
  have hA : AnalyticOnNhd ℂ Complex.Gamma U := hΓ.analyticOnNhd isOpen_U
  have hψ : AnalyticOnNhd ℂ (fun s => deriv Complex.Gamma s / Complex.Gamma s) U :=
    hA.deriv.div hA fun s hs => Complex.Gamma_ne_zero_of_re_pos hs
  have e : (fun s => Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) =
      fun s => deriv Complex.Gamma s / Complex.Gamma s + (Real.eulerMascheroniConstant : ℂ) := rfl
  rw [e]
  exact hψ.add analyticOnNhd_const

theorem main (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s))
      (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) := by
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
      Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) = ∑' k, term z k := by
    set u : ℕ → ℂ := fun n => (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ) with hu
    have hut : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
          have := (tendsto_const_nhds (x := (1 : ℝ))).add
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          simpa using this
        have h2 := ((Complex.continuous_ofReal.tendsto (1 : ℝ)).comp h1)
        simpa [hu, Function.comp_def] using h2
      · simp only [hu, mem_compl_iff, mem_singleton_iff]
        intro h
        have h' := congrArg Complex.re h
        simp only [Complex.ofReal_re, Complex.one_re] at h'
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine hut.frequently (Filter.Eventually.of_forall fun n => ?_).frequently
    show Complex.digamma (u n) + (Real.eulerMascheroniConstant : ℂ) = ∑' k, term (u n) k
    simp only [hu]
    exact real_case (by positivity)
  have heq : Set.EqOn (fun s => Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) (fun z => ∑' k, term z k) U :=
    analyticOnNhd_digamma_add.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_T isPreconnected_U
      (show (1 : ℂ) ∈ U by show (0 : ℝ) < (1 : ℂ).re; simp) hfreq
  have h : Complex.digamma s + (Real.eulerMascheroniConstant : ℂ) = ∑' k, term s k := heq hs
  rw [h]
  exact (summable_term hs).hasSum

end SlDigammaSeries

theorem solution
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + s))
      (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) :=
  SlDigammaSeries.main s hs

end S_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
end P2MW
export P2MW.S_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant (solution)
