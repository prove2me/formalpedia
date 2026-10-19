-- Prove2me | solution 1 for CVPricing.Regret.price_near_optimum_taboo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T17:10:51.080878+00:00
-- url     : https://prove2.me/submissions/988c39e2-3b15-4ce0-8482-43d76333454d

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP

set_option autoImplicit false

open KeskinZeevi.SufficientConditions

namespace F1322

open CVPricing.Regret Filter Topology Set

/-- the derivative of the revenue in the price -/
noncomputable def G (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ) : ℝ :=
  M.h (a.1 + a.2 * p) + p * (deriv M.h (a.1 + a.2 * p) * a.2)

/-- the second derivative of the revenue in the price -/
noncomputable def F (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ) : ℝ :=
  2 * a.2 * deriv M.h (a.1 + a.2 * p) + p * a.2 ^ 2 * deriv (deriv M.h) (a.1 + a.2 * p)

theorem hC2 (M : CVPricing.Regret.Model) : ContDiffOn ℝ 2 M.h (Ioi 0) :=
  M.h_contDiffOn.mono Ioi_subset_Ici_self

theorem hC1 (M : CVPricing.Regret.Model) : ContDiffOn ℝ 1 (deriv M.h) (Ioi 0) :=
  (hC2 M).deriv_of_isOpen isOpen_Ioi (by norm_num)

theorem h_diff (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ M.h x :=
  ((hC2 M).contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by norm_num)

theorem dh_diff (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (deriv M.h) x :=
  ((hC1 M).contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by norm_num)

theorem h_cont (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) : ContinuousAt M.h x :=
  (h_diff M x hx).continuousAt

theorem dh_cont (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) :
    ContinuousAt (deriv M.h) x :=
  (dh_diff M x hx).continuousAt

theorem ddh_cont (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) :
    ContinuousAt (deriv (deriv M.h)) x :=
  ((hC1 M).continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).continuousAt (Ioi_mem_nhds hx)

theorem lin_hasDeriv (a : ℝ × ℝ) (p : ℝ) :
    HasDerivAt (fun q : ℝ => a.1 + a.2 * q) a.2 p := by
  have := ((hasDerivAt_id p).const_mul a.2).const_add a.1
  simpa using this

theorem rev_hasDeriv (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ)
    (hx : 0 < a.1 + a.2 * p) : HasDerivAt (revenue M.h a) (G M a p) p := by
  have h1 : HasDerivAt (fun q : ℝ => M.h (a.1 + a.2 * q)) (deriv M.h (a.1 + a.2 * p) * a.2) p :=
    (h_diff M _ hx).hasDerivAt.comp p (lin_hasDeriv a p)
  have h2 := (hasDerivAt_id p).mul h1
  have e : revenue M.h a = fun q : ℝ => id q * M.h (a.1 + a.2 * q) := by
    funext q; simp [CVPricing.Regret.revenue]
  rw [e]
  refine h2.congr_deriv ?_
  unfold G
  simp only [id_eq]
  ring

theorem G_hasDeriv (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ)
    (hx : 0 < a.1 + a.2 * p) : HasDerivAt (fun q => G M a q) (F M a p) p := by
  have h1 : HasDerivAt (fun q : ℝ => M.h (a.1 + a.2 * q)) (deriv M.h (a.1 + a.2 * p) * a.2) p :=
    (h_diff M _ hx).hasDerivAt.comp p (lin_hasDeriv a p)
  have h3 : HasDerivAt (fun q : ℝ => deriv M.h (a.1 + a.2 * q))
      (deriv (deriv M.h) (a.1 + a.2 * p) * a.2) p :=
    by
      have hd : HasDerivAt (deriv M.h) (deriv (deriv M.h) (a.1 + a.2 * p)) (a.1 + a.2 * p) :=
        (dh_diff M _ hx).hasDerivAt
      exact hd.comp p (lin_hasDeriv a p)
  have h4 := (hasDerivAt_id p).mul (h3.mul_const a.2)
  have h5 := h1.add h4
  have e : (fun q => G M a q) =
      fun q : ℝ => M.h (a.1 + a.2 * q) + id q * (deriv M.h (a.1 + a.2 * q) * a.2) := by
    funext q; unfold G; simp only [id_eq]
  rw [e]
  refine h5.congr_deriv ?_
  unfold F
  simp only [id_eq]
  ring

theorem d2_eq (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ) (hx : 0 < a.1 + a.2 * p) :
    deriv (deriv (revenue M.h a)) p = F M a p := by
  have hc : Continuous fun q : ℝ => a.1 + a.2 * q := by fun_prop
  have hev : ∀ᶠ q in 𝓝 p, 0 < a.1 + a.2 * q := (hc.tendsto p).eventually_const_lt hx
  have heq : deriv (revenue M.h a) =ᶠ[𝓝 p] fun q => G M a q :=
    hev.mono fun q hq => (rev_hasDeriv M a q hq).deriv
  rw [heq.deriv_eq]
  exact (G_hasDeriv M a p hx).deriv

theorem rev_cont (M : CVPricing.Regret.Model) (z : ℝ × (ℝ × ℝ)) (hz : 0 < z.2.1 + z.2.2 * z.1) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => revenue M.h z.2 z.1) z := by
  have hin : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => z.2.1 + z.2.2 * z.1) z := by fun_prop
  have hh : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => M.h (z.2.1 + z.2.2 * z.1)) z :=
    ContinuousAt.comp (g := M.h) (h_cont M _ hz) hin
  exact continuousAt_fst.mul hh

theorem F_cont (M : CVPricing.Regret.Model) (z : ℝ × (ℝ × ℝ)) (hz : 0 < z.2.1 + z.2.2 * z.1) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => F M z.2 z.1) z := by
  have hin : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => z.2.1 + z.2.2 * z.1) z := by fun_prop
  have h1 : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => deriv M.h (z.2.1 + z.2.2 * z.1)) z :=
    ContinuousAt.comp (g := deriv M.h) (dh_cont M _ hz) hin
  have h2 : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => deriv (deriv M.h) (z.2.1 + z.2.2 * z.1)) z :=
    ContinuousAt.comp (g := deriv (deriv M.h)) (ddh_cont M _ hz) hin
  have hs : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => z.2.2) z := by fun_prop
  have hf : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => z.1) z := by fun_prop
  exact ((continuousAt_const.mul hs).mul h1).add ((hf.mul (hs.pow 2)).mul h2)

theorem rev_lim (M : CVPricing.Regret.Model) (A : ℕ → ℝ × ℝ) (P : ℕ → ℝ) (a : ℝ × ℝ) (p : ℝ)
    (hA : Tendsto A atTop (𝓝 a)) (hP : Tendsto P atTop (𝓝 p)) (hz : 0 < a.1 + a.2 * p) :
    Tendsto (fun k => revenue M.h (A k) (P k)) atTop (𝓝 (revenue M.h a p)) := by
  have := (rev_cont M (p, a) hz).tendsto.comp (hP.prodMk_nhds hA)
  exact this

theorem opt_eq (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (q : ℝ) (hq : q ∈ Icc M.pl M.ph)
    (hs : ∀ q' ∈ Icc M.pl M.ph, q' ≠ q → revenue M.h a q' < revenue M.h a q) :
    optPriceOf M a = q := by
  have hmax : ∀ q' ∈ Icc M.pl M.ph, revenue M.h a q' ≤ revenue M.h a q := by
    intro q' hq'
    by_cases h : q' = q
    · rw [h]
    · exact (hs q' hq' h).le
  have hex : ∃ q1, ∀ q', IsRevMaxOn M a (Icc M.pl M.ph) q' ↔ q' = q1 := by
    refine ⟨q, fun q' => ⟨fun h => ?_, fun h => ?_⟩⟩
    · by_contra hne
      have := hs q' h.1 hne
      have := h.2 q hq
      linarith
    · subst h
      exact ⟨hq, hmax⟩
  unfold optPriceOf
  rw [dif_pos hex]
  exact ((Classical.choose_spec hex q).1 ⟨hq, hmax⟩).symm

theorem optU (M : CVPricing.Regret.Model) (U : Set (ℝ × ℝ))
    (hU : ∀ a ∈ U, ∃ q ∈ Ioo M.pl M.ph,
      (∀ q' ∈ Icc M.pl M.ph, q' ≠ q → revenue M.h a q' < revenue M.h a q) ∧
      deriv (deriv (revenue M.h a)) q < 0) (a : ℝ × ℝ) (ha : a ∈ U) :
    optPriceOf M a ∈ Ioo M.pl M.ph ∧
      ∀ q' ∈ Icc M.pl M.ph, q' ≠ optPriceOf M a →
        revenue M.h a q' < revenue M.h a (optPriceOf M a) := by
  obtain ⟨q, hq, hs, -⟩ := hU a ha
  rw [opt_eq M a q (Ioo_subset_Icc_self hq) hs]
  exact ⟨hq, hs⟩

theorem euclid_le (a b : ℝ × ℝ) : dist a b ≤ euclidNorm (a - b) := by
  have h1 : |a.1 - b.1| ≤ euclidNorm (a - b) :=
    Real.abs_le_sqrt (by simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.2 - b.2)])
  have h2 : |a.2 - b.2| ≤ euclidNorm (a - b) :=
    Real.abs_le_sqrt (by simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.1 - b.1)])
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le h1 h2

theorem between (Q X m w pl ph : ℝ) (hQ : Q ∈ Ioo (m - w) (m + w)) (hQI : Q ∈ Icc pl ph)
    (hX : X ∈ Icc pl ph \ Ioo (m - w) (m + w)) (hlt : 2 * w < |X - Q|) :
    (if Q < X then m + w else m - w) ∈ Icc pl ph \ Ioo (m - w) (m + w) ∧
      |(if Q < X then m + w else m - w) - Q| ≤ 2 * w ∧
      (if Q < X then m + w else m - w) ∈ Ioo (min Q X) (max Q X) := by
  obtain ⟨hQ1, hQ2⟩ := hQ
  obtain ⟨hQI1, hQI2⟩ := hQI
  obtain ⟨⟨hX1, hX2⟩, hXn⟩ := hX
  simp only [Set.mem_Ioo, not_and_or, not_lt] at hXn
  split_ifs with h
  · have ha : |X - Q| = X - Q := abs_of_pos (by linarith)
    rw [ha] at hlt
    have hX3 : m + w < X := by linarith
    refine ⟨⟨⟨by linarith, by linarith⟩, ?_⟩, ?_, ?_⟩
    · simp only [Set.mem_Ioo, not_and_or, not_lt]
      right; exact le_rfl
    · rw [abs_le]; constructor <;> linarith
    · rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨hQ2, hX3⟩
  · push Not at h
    have ha : |X - Q| = Q - X := by
      rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [ha] at hlt
    have hX3 : X < m - w := by linarith
    refine ⟨⟨⟨by linarith, by linarith⟩, ?_⟩, ?_, ?_⟩
    · simp only [Set.mem_Ioo, not_and_or, not_lt]
      left; exact le_rfl
    · rw [abs_le]; constructor <;> linarith
    · rw [min_eq_right h, max_eq_left h]
      exact ⟨hX3, hQ1⟩

end F1322

namespace F1322

open CVPricing.Regret Filter Topology Set

theorem key (M : CVPricing.Regret.Model) : ∃ ρ : ℝ, 0 < ρ ∧ ∃ W : ℝ, 0 < W ∧
    ∀ a : ℝ × ℝ, euclidNorm (a - M.a0) ≤ ρ → ∀ m w x : ℝ, 0 ≤ w → w ≤ W →
      IsRevMaxOn M a (Icc M.pl M.ph \ Ioo (m - w) (m + w)) x →
      |x - optPriceOf M a| ≤ 2 * w := by
  by_contra H
  push Not at H
  have H' := fun n : ℕ => H (1 / ((n : ℝ) + 1)) (by positivity) (1 / ((n : ℝ) + 1)) (by positivity)
  choose a ha m w x hw0 hwW hx hlt using H'
  obtain ⟨U, hUo, ha0U, hU⟩ := M.nbhd
  obtain ⟨q0, hq0mem, hq0s, hq0d2⟩ := hU M.a0 ha0U
  have hq0I : q0 ∈ Icc M.pl M.ph := Ioo_subset_Icc_self hq0mem
  have hpos0 : ∀ p ∈ Icc M.pl M.ph, 0 < M.a0.1 + M.a0.2 * p := by
    intro p hp
    have := M.a0_ph_pos
    have := M.a01_neg
    nlinarith [hp.2]
  -- a n → a0
  have hA : Tendsto a atTop (𝓝 M.a0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    exact (euclid_le _ _).trans (ha n)
  -- subsequence
  have hfreq : ∃ᶠ n in atTop, (optPriceOf M (a n), x n) ∈ Icc M.pl M.ph ×ˢ Icc M.pl M.ph := by
    refine Eventually.frequently ?_
    filter_upwards [hA.eventually (hUo.mem_nhds ha0U)] with n hn
    exact ⟨Ioo_subset_Icc_self (optU M U hU _ hn).1, (hx n).1.1⟩
  obtain ⟨⟨qb, xb⟩, hmem, φ, hφ, hlim⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq' hfreq
  have hQ : Tendsto (fun k => optPriceOf M (a (φ k))) atTop (𝓝 qb) :=
    (continuous_fst.tendsto (qb, xb)).comp hlim
  have hX : Tendsto (fun k => x (φ k)) atTop (𝓝 xb) :=
    (continuous_snd.tendsto (qb, xb)).comp hlim
  have hAφ : Tendsto (fun k => a (φ k)) atTop (𝓝 M.a0) := hA.comp hφ.tendsto_atTop
  have hWφ : Tendsto (fun k => w (φ k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => hw0 (φ k)) (fun k => hwW (φ k))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  have hUk : ∀ᶠ k in atTop, a (φ k) ∈ U := hAφ.eventually (hUo.mem_nhds ha0U)
  -- qb = q0
  have hqb : qb = q0 := by
    have h1 : ∀ᶠ k in atTop, revenue M.h (a (φ k)) q0 ≤
        revenue M.h (a (φ k)) (optPriceOf M (a (φ k))) := by
      filter_upwards [hUk] with k hk
      obtain ⟨-, hs⟩ := optU M U hU _ hk
      by_cases e : q0 = optPriceOf M (a (φ k))
      · rw [← e]
      · exact (hs q0 hq0I e).le
    have h2 := le_of_tendsto_of_tendsto
      (rev_lim M _ _ _ _ hAφ tendsto_const_nhds (hpos0 q0 hq0I))
      (rev_lim M _ _ _ _ hAφ hQ (hpos0 qb hmem.1)) h1
    by_contra hne
    have := hq0s qb hmem.1 hne
    linarith
  rw [hqb] at hQ
  -- the boundary point E
  set E : ℕ → ℝ := fun k => if optPriceOf M (a (φ k)) < x (φ k) then m (φ k) + w (φ k)
    else m (φ k) - w (φ k) with hEdef
  have hprops : ∀ᶠ k in atTop,
      revenue M.h (a (φ k)) (x (φ k)) ≤ revenue M.h (a (φ k)) (optPriceOf M (a (φ k))) ∧
      x (φ k) ≠ optPriceOf M (a (φ k)) ∧
      revenue M.h (a (φ k)) (E k) ≤ revenue M.h (a (φ k)) (x (φ k)) ∧
      |E k - optPriceOf M (a (φ k))| ≤ 2 * w (φ k) ∧
      E k ∈ Ioo (min (optPriceOf M (a (φ k))) (x (φ k))) (max (optPriceOf M (a (φ k))) (x (φ k))) := by
    filter_upwards [hUk] with k hk
    obtain ⟨hom, hs⟩ := optU M U hU _ hk
    have hxI : x (φ k) ∈ Icc M.pl M.ph := (hx (φ k)).1.1
    have hne : x (φ k) ≠ optPriceOf M (a (φ k)) := by
      intro e
      have := hlt (φ k)
      rw [e, sub_self, abs_zero] at this
      linarith [hw0 (φ k)]
    have hle : revenue M.h (a (φ k)) (x (φ k)) ≤ revenue M.h (a (φ k)) (optPriceOf M (a (φ k))) :=
      (hs _ hxI hne).le
    have hin : optPriceOf M (a (φ k)) ∈ Ioo (m (φ k) - w (φ k)) (m (φ k) + w (φ k)) := by
      by_contra hn
      have h1 := (hx (φ k)).2 _ ⟨Ioo_subset_Icc_self hom, hn⟩
      have h2 := hs _ hxI hne
      linarith
    obtain ⟨hE1, hE2, hE3⟩ := between _ _ _ _ _ _ hin (Ioo_subset_Icc_self hom) (hx (φ k)).1
      (hlt (φ k))
    exact ⟨hle, hne, (hx (φ k)).2 _ hE1, hE2, hE3⟩
  have hE : Tendsto E atTop (𝓝 q0) := by
    have hd : Tendsto (fun k => E k - optPriceOf M (a (φ k))) atTop (𝓝 0) := by
      have h2 : Tendsto (fun k => 2 * w (φ k)) atTop (𝓝 0) := by
        simpa using hWφ.const_mul 2
      refine squeeze_zero_norm' ?_ h2
      filter_upwards [hprops] with k hk
      rw [Real.norm_eq_abs]
      exact hk.2.2.2.1
    have := hd.add hQ
    simpa using this
  -- xb = q0
  have hxb : xb = q0 := by
    have h1 : ∀ᶠ k in atTop, revenue M.h (a (φ k)) (E k) ≤ revenue M.h (a (φ k)) (x (φ k)) := by
      filter_upwards [hprops] with k hk
      exact hk.2.2.1
    have h2 := le_of_tendsto_of_tendsto
      (rev_lim M _ _ _ _ hAφ hE (hpos0 q0 hq0I))
      (rev_lim M _ _ _ _ hAφ hX (hpos0 xb hmem.2)) h1
    by_contra hne
    have := hq0s xb hmem.2 hne
    linarith
  rw [hxb] at hX
  -- local strict concavity near (q0, a0)
  have hF0 : F M M.a0 q0 < 0 := by
    rw [← d2_eq M M.a0 q0 (hpos0 q0 hq0I)]
    exact hq0d2
  have hz0 : 0 < (q0, M.a0).2.1 + (q0, M.a0).2.2 * (q0, M.a0).1 := hpos0 q0 hq0I
  have hin : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => z.2.1 + z.2.2 * z.1) (q0, M.a0) := by fun_prop
  have hev : ∀ᶠ z in 𝓝 (q0, M.a0), 0 < z.2.1 + z.2.2 * z.1 ∧ F M z.2 z.1 < 0 :=
    (hin.tendsto.eventually_const_lt hz0).and ((F_cont M _ hz0).tendsto.eventually_lt_const hF0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hD : Ioo (q0 - ε) (q0 + ε) ∈ 𝓝 q0 := Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := (hprops.and ((hAφ.eventually (Metric.ball_mem_nhds _ hε)).and
    ((hQ.eventually hD).and (hX.eventually hD)))).exists
  have hgood : ∀ p ∈ Ioo (q0 - ε) (q0 + ε),
      0 < (a (φ k)).1 + (a (φ k)).2 * p ∧ F M (a (φ k)) p < 0 := by
    intro p hp
    refine hball (y := (p, a (φ k))) ?_
    rw [Prod.dist_eq]
    refine max_lt ?_ hk2
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hp.1, hp.2]
  have hconc : StrictConcaveOn ℝ (Ioo (q0 - ε) (q0 + ε)) (revenue M.h (a (φ k))) := by
    refine strictConcaveOn_of_deriv2_neg (convex_Ioo _ _) ?_ ?_
    · intro p hp
      exact (rev_hasDeriv M _ p (hgood p hp).1).continuousAt.continuousWithinAt
    · intro p hp
      rw [interior_Ioo] at hp
      show deriv (deriv (revenue M.h (a (φ k)))) p < 0
      rw [d2_eq M _ p (hgood p hp).1]
      exact (hgood p hp).2
  obtain ⟨hle, hne, hEx, -, hEseg⟩ := hk1
  have hseg : E k ∈ openSegment ℝ (optPriceOf M (a (φ k))) (x (φ k)) := by
    rw [openSegment_eq_Ioo' (Ne.symm hne)]
    exact hEseg
  have := hconc.lt_on_openSegment hk3 hk4 (Ne.symm hne) hseg
  rw [min_eq_right hle] at this
  linarith

end F1322

namespace F1322

open CVPricing.Regret

/-- upper Bernoulli-type bound for the increment of a concave power -/
theorem rpow_diff_le (β x : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx : 0 < x) :
    (x + 1) ^ β - x ^ β ≤ β * x ^ (β - 1) := by
  have hs : -1 ≤ 1 / x := by
    have : 0 < 1 / x := by positivity
    linarith
  have key := rpow_one_add_le_one_add_mul_self hs hβ0 hβ1
  have e1 : x + 1 = x * (1 + 1 / x) := by field_simp
  have hnn : 0 ≤ 1 + 1 / x := by linarith
  rw [e1, Real.mul_rpow hx.le hnn, Real.rpow_sub_one hx.ne' β]
  have hxb : 0 ≤ x ^ β := Real.rpow_nonneg hx.le β
  have h3 := mul_le_mul_of_nonneg_left key hxb
  have e3 : x ^ β * (1 + β * (1 / x)) = x ^ β + β * (x ^ β / x) := by field_simp
  linarith

/-- squared half-width of the taboo interval -/
theorem tw_sq_le (α c : ℝ) (h0 : 0 < α) (h1 : α < 1) (hc : 0 < c) (s : ℕ) (hs : 1 ≤ s) :
    (tabooHalfWidth α c s) ^ 2 ≤ 4 * c * ((s : ℝ) + 1) ^ (α - 1) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hmono : (s : ℝ) ^ α ≤ ((s : ℝ) + 1) ^ α :=
    Real.rpow_le_rpow hs0.le (by linarith) h0.le
  have hnn : 0 ≤ c * (((s : ℝ) + 1) ^ α - (s : ℝ) ^ α) * (((s : ℝ) + 1) / s) := by
    have : 0 ≤ ((s : ℝ) + 1) ^ α - (s : ℝ) ^ α := by linarith
    positivity
  unfold tabooHalfWidth
  rw [Real.sq_sqrt hnn]
  have hd := rpow_diff_le α s h0.le h1.le hs0
  have hr : ((s : ℝ) + 1) / s ≤ 2 := by
    rw [div_le_iff₀ hs0]; linarith
  -- s^(α-1) ≤ 2 (s+1)^(α-1)
  have hpow : (s : ℝ) ^ (α - 1) ≤ 2 * ((s : ℝ) + 1) ^ (α - 1) := by
    have e : (s : ℝ) ^ (α - 1) = ((s : ℝ) + 1) ^ (α - 1) * (((s : ℝ) + 1) / s) ^ (1 - α) := by
      have haa : ((s : ℝ) + 1) ^ (α - 1) * ((s : ℝ) + 1) ^ (1 - α) = 1 := by
        rw [← Real.rpow_add (by linarith)]; simp
      have hbb : (s : ℝ) ^ (α - 1) * (s : ℝ) ^ (1 - α) = 1 := by
        rw [← Real.rpow_add hs0]; simp
      have hb' : 0 < (s : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hs0 _
      rw [Real.div_rpow (by linarith) hs0.le, ← mul_div_assoc, haa]
      exact eq_one_div_of_mul_eq_one_left hbb
    have h2 : (((s : ℝ) + 1) / s) ^ (1 - α) ≤ 2 ^ (1 - α) :=
      Real.rpow_le_rpow (by positivity) hr (by linarith)
    have h3 : (2 : ℝ) ^ (1 - α) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - α) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have hp : 0 ≤ ((s : ℝ) + 1) ^ (α - 1) := Real.rpow_nonneg (by linarith) _
    rw [e]
    calc ((s : ℝ) + 1) ^ (α - 1) * (((s : ℝ) + 1) / s) ^ (1 - α)
        ≤ ((s : ℝ) + 1) ^ (α - 1) * 2 := mul_le_mul_of_nonneg_left (h2.trans h3) hp
      _ = 2 * ((s : ℝ) + 1) ^ (α - 1) := by ring
  have hc1 : (0 : ℝ) ≤ ((s : ℝ) + 1) ^ α - (s : ℝ) ^ α := by linarith
  have hd2 : ((s : ℝ) + 1) ^ α - (s : ℝ) ^ α ≤ 2 * ((s : ℝ) + 1) ^ (α - 1) := by
    calc _ ≤ α * (s : ℝ) ^ (α - 1) := hd
      _ ≤ 1 * (s : ℝ) ^ (α - 1) :=
          mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg hs0.le _)
      _ = (s : ℝ) ^ (α - 1) := one_mul _
      _ ≤ _ := hpow
  have hq : 0 ≤ ((s : ℝ) + 1) ^ (α - 1) := Real.rpow_nonneg (by linarith) _
  calc c * (((s : ℝ) + 1) ^ α - (s : ℝ) ^ α) * (((s : ℝ) + 1) / s)
      ≤ c * (2 * ((s : ℝ) + 1) ^ (α - 1)) * 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hd2 hc.le) hr (by positivity)
        positivity
    _ = 4 * c * ((s : ℝ) + 1) ^ (α - 1) := by ring



open CVPricing.Regret KeskinZeevi.SufficientConditions


end F1322

namespace F1322

open CVPricing.Regret Filter Topology Set

theorem prices_mem (M : CVPricing.Regret.Model) (α c : ℝ) (p d : ℕ → ℝ)
    (h : IsCVPPath M α c p d) : ∀ t : ℕ, 1 ≤ t → p t ∈ Set.Icc M.pl M.ph := by
  obtain ⟨h1, h2, -, -, -, -, hstep⟩ := h
  intro t ht
  rcases Nat.lt_or_ge t 3 with hn | hn
  · interval_cases t
    · exact h1
    · exact h2
  · obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    rcases hstep n (by omega) with ⟨-, hF⟩ | ⟨a, -, -, hF⟩ | ⟨a, -, -, hE⟩
    · rcases hF.1 with e | e <;> rw [e] <;> assumption
    · rcases hF.1 with e | e <;> rw [e] <;> assumption
    · rcases hE with ⟨-, hm, -⟩ | ⟨-, hm⟩
      · exact hm.1
      · exact hm.1.1

theorem tw_small (α c W : ℝ) (hW : 0 < W) : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    α ∈ Set.Ioo (0 : ℝ) 1 → 0 < c → tabooHalfWidth α c t ≤ W := by
  by_cases hαc : α ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < c
  · obtain ⟨⟨h0, h1⟩, hc⟩ := hαc
    have hT1 : Tendsto (fun t : ℕ => ((t : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hT2 := (tendsto_rpow_neg_atTop (y := 1 - α) (by linarith)).comp hT1
    have hT3 : Tendsto (fun t : ℕ => 4 * c * ((t : ℝ) + 1) ^ (α - 1)) atTop (𝓝 0) := by
      have := hT2.const_mul (4 * c)
      rw [mul_zero] at this
      refine this.congr (fun t => ?_)
      simp only [Function.comp, neg_sub]
    obtain ⟨t₁, ht₁⟩ := eventually_atTop.1 (hT3.eventually_lt_const (by positivity : (0:ℝ) < W ^ 2))
    refine ⟨max t₁ 1, fun t ht _ _ => ?_⟩
    have hsq := tw_sq_le α c h0 h1 hc t (le_trans (le_max_right _ _) ht)
    have hlt := ht₁ t (le_trans (le_max_left _ _) ht)
    have hnn : 0 ≤ tabooHalfWidth α c t := Real.sqrt_nonneg _
    by_contra hcon
    push Not at hcon
    nlinarith
  · exact ⟨0, fun t _ hα hc => absurd ⟨hα, hc⟩ hαc⟩

theorem main (M : CVPricing.Regret.Model) (hU : MQLEUnique M) (α c : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ p d : ℕ → ℝ, IsCVPPath M α c p d →
      ∀ a, IsMQLE M p d t a → euclidNorm (a - M.a0) ≤ ρ →
        |p (t + 1) - optPriceOf M a| ≤ 2 * tabooHalfWidth α c t := by
  obtain ⟨ρ1, hρ1, W, hW, hkey⟩ := key M
  have hK : 0 < M.a0.1 + M.a0.2 * M.ph := M.a0_ph_pos
  have hph : 0 < M.ph := lt_trans M.pl_pos M.pl_lt_ph
  set ρ := min ρ1 (min (M.a0.1 / 2) (min (-M.a0.2 / 2)
    ((M.a0.1 + M.a0.2 * M.ph) / (2 * (1 + M.ph))))) with hρdef
  have hρ : 0 < ρ := by
    have := M.a00_pos
    have := M.a01_neg
    have : 0 < (M.a0.1 + M.a0.2 * M.ph) / (2 * (1 + M.ph)) := by positivity
    simp only [hρdef, lt_min_iff]
    refine ⟨hρ1, by linarith, by linarith, this⟩
  have hρ1' : ρ ≤ ρ1 := min_le_left _ _
  have hρ2 : ρ ≤ M.a0.1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ ≤ -M.a0.2 / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ4 : ρ ≤ (M.a0.1 + M.a0.2 * M.ph) / (2 * (1 + M.ph)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hgood : ∀ a : ℝ × ℝ, euclidNorm (a - M.a0) ≤ ρ → GoodEst M a := by
    intro a ha
    have h1 : |a.1 - M.a0.1| ≤ ρ := le_trans (Real.abs_le_sqrt (by
      simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.2 - M.a0.2)])) ha
    have h2 : |a.2 - M.a0.2| ≤ ρ := le_trans (Real.abs_le_sqrt (by
      simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.1 - M.a0.1)])) ha
    rw [abs_le] at h1 h2
    have := M.a00_pos
    have := M.a01_neg
    refine ⟨by linarith, by linarith, fun q hq => ?_⟩
    have hq0 : 0 < q := lt_of_lt_of_le M.pl_pos hq.1
    have e1 : -(ρ * q) ≤ (a.2 - M.a0.2) * q := by nlinarith
    have e2 : ρ * q ≤ ρ * M.ph := mul_le_mul_of_nonneg_left hq.2 hρ.le
    have e3 : M.a0.2 * M.ph ≤ M.a0.2 * q := by nlinarith [hq.2]
    have e4 : ρ * (2 * (1 + M.ph)) ≤ M.a0.1 + M.a0.2 * M.ph := by
      rw [← le_div_iff₀ (by positivity)]; exact hρ4
    nlinarith
  obtain ⟨t₀, ht₀⟩ := tw_small α c W hW
  refine ⟨ρ, hρ, max t₀ 2, ?_⟩
  intro t ht p d hpath a hmq hnorm
  have ht2 : 2 ≤ t := le_trans (le_max_right _ _) ht
  have htw : tabooHalfWidth α c t ≤ W :=
    ht₀ t (le_trans (le_max_left _ _) ht) hpath.2.2.2.1 hpath.2.2.2.2.1
  have hw0 : 0 ≤ tabooHalfWidth α c t := Real.sqrt_nonneg _
  have hmem := prices_mem M α c p d hpath
  have huniq : ∀ b, IsMQLE M p d t b → b = a := fun b hb =>
    hU p d t ht2 (fun i hi => hmem i (Finset.mem_Icc.1 hi).1) hpath.2.2.1 hb hmq
  have hnorm1 : euclidNorm (a - M.a0) ≤ ρ1 := hnorm.trans hρ1'
  obtain ⟨-, -, -, -, -, -, hstep⟩ := hpath
  rcases hstep t ht2 with ⟨hno, -⟩ | ⟨b, hb, hng, -⟩ | ⟨b, hb, -, hE⟩
  · exact absurd hmq (hno a)
  · rw [huniq b hb] at hng
    exact absurd (hgood a hnorm) hng
  · rw [huniq b hb] at hE
    rcases hE with ⟨-, hm, -⟩ | ⟨-, hm⟩
    · have hm' : IsRevMaxOn M a (Icc M.pl M.ph \ Ioo (0 - 0) (0 + 0)) (p (t + 1)) := by
        simpa using hm
      have := hkey a hnorm1 0 0 (p (t + 1)) le_rfl hW.le hm'
      linarith
    · exact hkey a hnorm1 (avgPriceOf p t) (tabooHalfWidth α c t) (p (t + 1)) hw0 htw hm

end F1322

open CVPricing.Regret KeskinZeevi.SufficientConditions in
theorem solution (M : CVPricing.Regret.Model) (hU : MQLEUnique M) (α c : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ p d : ℕ → ℝ, IsCVPPath M α c p d →
      ∀ a, IsMQLE M p d t a → euclidNorm (a - M.a0) ≤ ρ →
        |p (t + 1) - optPriceOf M a| ≤ 2 * tabooHalfWidth α c t := by
  exact F1322.main M hU α c
