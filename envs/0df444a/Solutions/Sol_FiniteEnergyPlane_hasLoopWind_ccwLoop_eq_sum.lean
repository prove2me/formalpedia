-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_ccwLoop_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T11:23:04.438905+00:00
-- url     : https://prove2.me/submissions/eac73a22-ec93-4b18-aeb3-0ee3cde0a182

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_zero_of_forall_ne_ray
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_re_conj_mul_pos
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_conj
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_of_continuousOn_family



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

lemma c1w_ccwLoop_periodic (R : ℝ) : Function.Periodic (ccwLoop R) 1 := by
  intro t
  simp only [ccwLoop]
  congr 1
  rw [show (((2 * π * (t + 1) : ℝ)) : ℂ) * Complex.I =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma c1w_ccwLoop_continuous (R : ℝ) : Continuous (ccwLoop R) := by
  unfold ccwLoop
  fun_prop

lemma c1w_norm_ccwLoop (R t : ℝ) (hR : 0 ≤ R) : ‖ccwLoop R t‖ = R := by
  simp only [ccwLoop, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]

lemma c1w_ccwLoop_pow (R t : ℝ) (m : ℕ) :
    ccwLoop R t ^ m = ((R ^ m : ℝ) : ℂ) * Complex.exp (((2 * π * m * t : ℝ) : ℂ) * Complex.I) := by
  simp only [ccwLoop, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- The loop `t ↦ a ρ^m e^{2πimt}` (`a ≠ 0`, `ρ > 0`) has winding number `m`. -/
lemma c1w_hasLoopWind_const_mul_pow (a : ℂ) (ha : a ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) :
    HasLoopWind (fun t => a * ccwLoop ρ t ^ m) m := by
  have hc : Continuous (fun t => a * ccwLoop ρ t ^ m) :=
    continuous_const.mul ((c1w_ccwLoop_continuous ρ).pow m)
  refine ⟨hc, fun t => by simp only [c1w_ccwLoop_periodic ρ t], fun t => ?_, ?_⟩
  · refine mul_ne_zero ha (pow_ne_zero _ ?_)
    intro h
    have := c1w_norm_ccwLoop ρ t hρ.le
    rw [h, norm_zero] at this
    linarith
  · refine ⟨fun t => Complex.arg a + 2 * π * m * t, by fun_prop, fun t => ?_, by push_cast; ring⟩
    have hn : ‖a * ccwLoop ρ t ^ m‖ = ‖a‖ * ρ ^ m := by
      rw [norm_mul, norm_pow, c1w_norm_ccwLoop ρ t hρ.le]
    dsimp only
    rw [hn, c1w_ccwLoop_pow]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a]
    push_cast
    rw [show ((Complex.arg a : ℂ) + 2 * π * m * t) * Complex.I =
        (Complex.arg a : ℂ) * Complex.I + 2 * π * m * t * Complex.I by ring, Complex.exp_add]
    ring

lemma c1w_alg (w p q : ℂ) : (w.re : ℂ) * p + (w.im : ℂ) * q =
    (p - Complex.I * q) / 2 * w + (p + Complex.I * q) / 2 * starRingEnd ℂ w := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have h2 : starRingEnd ℂ w = (w.re : ℂ) - (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(p - Complex.I * q) / 2) * hw + (-(p + Complex.I * q) / 2) * h2 +
    (q * (w.im : ℂ)) * Complex.I_sq

/-- Let `p, q` be continuous on `B(z₀, R)` with `Im(conj p(z₀) · q(z₀)) > 0` (so that
`w ↦ Re(w) p(z₀) + Im(w) q(z₀)` is an orientation-preserving real-linear isomorphism of `ℂ`), and let
`F(z) = Re((z - z₀)^m) p(z) + Im((z - z₀)^m) q(z)` on `B(z₀, R)`. Then on some smaller disc
`B(z₀, r)`, `F` has no zero other than `z₀`, and `F` has winding number `m` along every
counterclockwise circle `t ↦ z₀ + ρ e^{2πit}`, `0 < ρ < r`. -/
theorem exists_ball_hasLoopWind_re_mul_add_im_mul_aux (F p q : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hp : ContinuousOn p (ball z₀ R)) (hq : ContinuousOn q (ball z₀ R))
    (hpq : 0 < (starRingEnd ℂ (p z₀) * q z₀).im)
    (hF : ∀ z ∈ ball z₀ R,
      F z = (((z - z₀) ^ m).re : ℂ) * p z + (((z - z₀) ^ m).im : ℂ) * q z) :
    ∃ r > (0 : ℝ), r ≤ R ∧ (∀ z ∈ ball z₀ r, z ≠ z₀ → F z ≠ 0) ∧
      ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => F (z₀ + ccwLoop ρ t)) m := by
  set A : ℂ → ℂ := fun z => (p z - Complex.I * q z) / 2 with hA
  set B : ℂ → ℂ := fun z => (p z + Complex.I * q z) / 2 with hB
  have hFAB : ∀ z ∈ ball z₀ R, F z = A z * (z - z₀) ^ m + B z * starRingEnd ℂ ((z - z₀) ^ m) := by
    intro z hz
    rw [hF z hz]
    exact c1w_alg _ _ _
  -- `‖B z₀‖ < ‖A z₀‖`
  have hAB : ‖B z₀‖ < ‖A z₀‖ := by
    have key : Complex.normSq (A z₀) - Complex.normSq (B z₀) =
        (starRingEnd ℂ (p z₀) * q z₀).im := by
      simp only [hA, hB, Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.sub_re,
        Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
      norm_num
      ring
    have h2 : ‖B z₀‖ ^ 2 < ‖A z₀‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2
  set κ := ‖A z₀‖ - ‖B z₀‖ with hκ
  have hκ0 : 0 < κ := by linarith
  have hA0 : A z₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hAB; exact absurd hAB (not_lt.2 (norm_nonneg _))
  have hzR : ball z₀ R ∈ 𝓝 z₀ := isOpen_ball.mem_nhds (mem_ball_self hR)
  have hAc : ContinuousAt A z₀ :=
    ((hp.continuousAt hzR).sub (continuousAt_const.mul (hq.continuousAt hzR))).div_const _
  have hBc : ContinuousAt B z₀ :=
    ((hp.continuousAt hzR).add (continuousAt_const.mul (hq.continuousAt hzR))).div_const _
  have hev : ∀ᶠ z in 𝓝 z₀, ‖A z - A z₀‖ < κ / 2 ∧ ‖B z - B z₀‖ < κ / 2 ∧ z ∈ ball z₀ R := by
    refine ((hAc.sub continuousAt_const).norm.eventually (gt_mem_nhds ?_)).and
      (((hBc.sub continuousAt_const).norm.eventually (gt_mem_nhds ?_)).and hzR)
    · simp only [Pi.sub_apply, hA, sub_self, norm_zero]; exact half_pos hκ0
    · simp only [Pi.sub_apply, hB, sub_self, norm_zero]; exact half_pos hκ0
  obtain ⟨r, hr, hrs⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set r' := min r R
  have hr' : 0 < r' := lt_min hr hR
  -- the key estimate `‖F z - A z₀ w‖ < ‖A z₀‖ ‖w‖` for `w = (z - z₀)^m ≠ 0`
  have hest : ∀ z ∈ ball z₀ r', z ≠ z₀ →
      ‖F z - A z₀ * (z - z₀) ^ m‖ < ‖A z₀ * (z - z₀) ^ m‖ := by
    intro z hz hne
    obtain ⟨h1, h2, h3⟩ := hrs z (ball_subset_ball (min_le_left _ _) hz)
    have hw : 0 < ‖(z - z₀) ^ m‖ := norm_pos_iff.2 (pow_ne_zero _ (sub_ne_zero.2 hne))
    rw [hFAB z h3, show A z * (z - z₀) ^ m + B z * starRingEnd ℂ ((z - z₀) ^ m) -
        A z₀ * (z - z₀) ^ m = (A z - A z₀) * (z - z₀) ^ m +
          B z * starRingEnd ℂ ((z - z₀) ^ m) by ring]
    have hBz : ‖B z‖ < ‖B z₀‖ + κ / 2 := by
      have := norm_sub_norm_le (B z) (B z₀)
      linarith
    calc _ ≤ ‖(A z - A z₀) * (z - z₀) ^ m‖ + ‖B z * starRingEnd ℂ ((z - z₀) ^ m)‖ :=
          norm_add_le _ _
      _ = (‖A z - A z₀‖ + ‖B z‖) * ‖(z - z₀) ^ m‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]; ring
      _ < ‖A z₀‖ * ‖(z - z₀) ^ m‖ := by
          refine mul_lt_mul_of_pos_right ?_ hw; linarith
      _ = _ := (norm_mul _ _).symm
  refine ⟨r', hr', min_le_right _ _, fun z hz hne h0 => ?_, fun ρ hρ => ?_⟩
  · have := hest z hz hne
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  · obtain ⟨hρ0, hρr⟩ := hρ
    set γ : ℝ → ℂ := fun t => z₀ + ccwLoop ρ t with hγ
    have hγb : ∀ t, γ t ∈ ball z₀ r' := fun t => by
      rw [mem_ball, dist_eq_norm, hγ, add_sub_cancel_left, c1w_norm_ccwLoop ρ t hρ0.le]
      exact hρr
    have hγne : ∀ t, γ t ≠ z₀ := fun t h => by
      have := c1w_norm_ccwLoop ρ t hρ0.le
      rw [show ccwLoop ρ t = γ t - z₀ by simp [hγ], h, sub_self, norm_zero] at this
      linarith
    have hγR : ∀ t, γ t ∈ ball z₀ R := fun t => ball_subset_ball (min_le_right _ _) (hγb t)
    have hγc : Continuous γ := continuous_const.add (c1w_ccwLoop_continuous ρ)
    have hFγ : (fun t => F (γ t)) = fun t => (((γ t - z₀) ^ m).re : ℂ) * p (γ t) +
        (((γ t - z₀) ^ m).im : ℂ) * q (γ t) := funext fun t => hF _ (hγR t)
    have hFc : Continuous (fun t => F (γ t)) := by
      rw [hFγ]
      have hpc : Continuous (fun t => p (γ t)) := hp.comp_continuous hγc hγR
      have hqc : Continuous (fun t => q (γ t)) := hq.comp_continuous hγc hγR
      have hw : Continuous (fun t => (γ t - z₀) ^ m) := (hγc.sub continuous_const).pow m
      exact ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp hw)).mul hpc).add
        ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp hw)).mul hqc)
    set L : ℝ → ℂ := fun t => A z₀ * ccwLoop ρ t ^ m with hL
    have hLw : HasLoopWind L m := c1w_hasLoopWind_const_mul_pow _ hA0 ρ hρ0 m
    have hL0 : ∀ t, L t ≠ 0 := hLw.2.2.1
    have hLγ : ∀ t, L t = A z₀ * (γ t - z₀) ^ m := fun t => by simp [hL, hγ]
    set Q : ℝ → ℂ := fun t => F (γ t) / L t with hQ
    have hQre : ∀ t, 0 < (Q t).re := by
      intro t
      have he := hest (γ t) (hγb t) (hγne t)
      rw [← hLγ] at he
      have hd : ‖Q t - 1‖ < 1 := by
        rw [hQ, show F (γ t) / L t - 1 = (F (γ t) - L t) / L t by field_simp [hL0 t],
          norm_div, div_lt_one (norm_pos_iff.2 (hL0 t))]
        exact he
      have := Complex.abs_re_le_norm (Q t - 1)
      rw [Complex.sub_re, Complex.one_re] at this
      have := abs_le.1 this
      linarith [this.1]
    have hQw : HasLoopWind Q 0 := by
      refine hasLoopWind_zero_of_forall_ne_ray Q (hFc.div (continuous_const.mul
        ((c1w_ccwLoop_continuous ρ).pow m)) hL0) ?_ (-1) (by norm_num) ?_
      · intro t
        simp only [hQ, hL, hγ, c1w_ccwLoop_periodic ρ t]
      · intro t s hs h
        have := hQre t
        rw [h] at this
        simp at this
        linarith
    have hprod := hasLoopWind_mul hLw hQw
    rw [add_zero] at hprod
    have heq : (fun t => L t * Q t) = fun t => F (z₀ + ccwLoop ρ t) := funext fun t => by
      simp only [hQ]
      field_simp [hL0 t]
      try rfl
    rw [heq] at hprod
    exact hprod

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

/-- `‖f - g‖ < ‖g‖` forces `Re(conj g · f) > 0`. -/
lemma wph_re_conj_mul_pos {f g : ℂ} (h : ‖f - g‖ < ‖g‖) : 0 < (starRingEnd ℂ g * f).re := by
  have hg : 0 < ‖g‖ := lt_of_le_of_lt (norm_nonneg _) h
  have e : (starRingEnd ℂ g * f).re = ‖g‖ ^ 2 + (starRingEnd ℂ g * (f - g)).re := by
    rw [mul_sub, Complex.sub_re, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  have h1 : |(starRingEnd ℂ g * (f - g)).re| ≤ ‖g‖ * ‖f - g‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 : ‖g‖ * ‖f - g‖ < ‖g‖ ^ 2 := by
    rw [sq]; exact mul_lt_mul_of_pos_left h hg
  have := (abs_le.1 h1).1
  linarith

theorem hasLoopWind_of_continuousOn_family_aux {a b : ℝ} (F : ℝ → ℝ → ℂ)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc a b ×ˢ Set.univ))
    (hper : ∀ l ∈ Set.Icc a b, Function.Periodic (F l) 1)
    (h0 : ∀ l ∈ Set.Icc a b, ∀ t, F l t ≠ 0) {k : ℤ} (hk : HasLoopWind (F a) k) :
    ∀ l ∈ Set.Icc a b, HasLoopWind (F l) k := by
  rcases lt_or_ge b a with hba | hab
  · intro l hl; exact absurd (hl.1.trans hl.2) (not_le.2 hba)
  set G : ℝ × ℝ → ℂ := fun p => F p.1 p.2 with hG
  set K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKs : K ⊆ Set.Icc a b ×ˢ Set.univ := Set.prod_mono le_rfl (Set.subset_univ _)
  have hGK : ContinuousOn G K := hF.mono hKs
  have hKne : K.Nonempty := ⟨(a, 0), ⟨Set.left_mem_Icc.2 hab, Set.left_mem_Icc.2 zero_le_one⟩⟩
  -- a positive lower bound for `‖F‖` on `K`
  obtain ⟨p₀, hp₀K, hp₀⟩ := hKc.exists_isMinOn hKne (continuous_norm.comp_continuousOn hGK)
  set m := ‖G p₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (h0 _ hp₀K.1 _)
  have hmin : ∀ p ∈ K, m ≤ ‖G p‖ := fun p hp => hp₀ hp
  -- uniform continuity on `K`
  obtain ⟨δ, hδ, hδK⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hGK) m hm0
  -- each loop is continuous
  have hcont : ∀ l ∈ Set.Icc a b, Continuous (F l) := fun l hl =>
    hF.comp_continuous (continuous_const.prodMk continuous_id) fun t => ⟨hl, Set.mem_univ _⟩
  -- the step: loops at nearby parameters have the same winding
  have hstep : ∀ l ∈ Set.Icc a b, ∀ l' ∈ Set.Icc a b, |l - l'| < δ →
      HasLoopWind (F l) k → HasLoopWind (F l') k := by
    intro l hl l' hl' hll' hw
    refine hasLoopWind_of_re_conj_mul_pos hw (hcont l' hl') (hper l' hl') fun t => ?_
    set s := Int.fract t
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    have e1 : F l t = F l s := by
      rw [show s = t - ((⌊t⌋ : ℤ) : ℝ) * 1 by rw [mul_one, Int.self_sub_floor]]
      exact ((hper l hl).sub_int_mul_eq _).symm
    have e2 : F l' t = F l' s := by
      rw [show s = t - ((⌊t⌋ : ℤ) : ℝ) * 1 by rw [mul_one, Int.self_sub_floor]]
      exact ((hper l' hl').sub_int_mul_eq _).symm
    rw [e1, e2]
    apply wph_re_conj_mul_pos
    have hd : dist ((l, s) : ℝ × ℝ) (l', s) < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      exact lt_of_le_of_lt (max_le le_rfl (abs_nonneg _)) hll'
    have h1 := hδK (l, s) ⟨hl, hs⟩ (l', s) ⟨hl', hs⟩ hd
    rw [dist_eq_norm, ← norm_neg, neg_sub] at h1
    exact lt_of_lt_of_le h1 (hmin (l, s) ⟨hl, hs⟩ : m ≤ ‖F l s‖)
  -- induction along `[a, b]` in steps of `δ / 2`
  have hind : ∀ n : ℕ, ∀ l ∈ Set.Icc a b, l ≤ a + n * (δ / 2) → HasLoopWind (F l) k := by
    intro n
    induction n with
    | zero =>
      intro l hl hle
      simp only [Nat.cast_zero, zero_mul, add_zero] at hle
      rwa [le_antisymm hle hl.1]
    | succ n ih =>
      intro l hl hle
      by_cases h : l ≤ a + n * (δ / 2)
      · exact ih l hl h
      · push_neg at h
        set l₀ := a + n * (δ / 2) with hl₀def
        have hl₀ : l₀ ∈ Set.Icc a b :=
          ⟨le_add_of_nonneg_right (by positivity), h.le.trans hl.2⟩
        refine hstep l₀ hl₀ l hl ?_ (ih l₀ hl₀ le_rfl)
        rw [abs_sub_comm, abs_of_pos (sub_pos.2 h)]
        push_cast at hle
        rw [hl₀def]
        linarith
  intro l hl
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / (δ / 2))
  refine hind n l hl ?_
  have := (div_lt_iff₀ (half_pos hδ)).1 hn
  have := hl.2
  nlinarith

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

/-- A constant nonzero loop has winding number `0`. -/
lemma wpw_const {a : ℂ} (ha : a ≠ 0) : HasLoopWind (fun _ => a) 0 := by
  refine ⟨continuous_const, fun _ => rfl, fun _ => ha, fun _ => Complex.arg a, continuous_const,
    fun _ => ?_, by simp⟩
  exact (Complex.norm_mul_exp_arg_mul_I a).symm

lemma wpw_inv {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) :
    HasLoopWind (fun t => (f t)⁻¹) (-k) := by
  obtain ⟨hfc, hfp, hf0, -⟩ := id hf
  refine hasLoopWind_of_re_conj_mul_pos (hasLoopWind_conj hf) (hfc.inv₀ hf0)
    (fun t => by simp only [hfp t]) fun t => ?_
  rw [Complex.conj_conj, mul_inv_cancel₀ (hf0 t), Complex.one_re]
  exact one_pos

lemma wpw_npow {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) (n : ℕ) :
    HasLoopWind (fun t => f t ^ n) (n * k) := by
  induction n with
  | zero => simpa using wpw_const (one_ne_zero (α := ℂ))
  | succ n ih =>
    have := hasLoopWind_mul ih hf
    convert this using 1
    · funext t; rw [pow_succ]
    · push_cast; ring

lemma wpw_zpow {f : ℝ → ℂ} {k : ℤ} (hf : HasLoopWind f k) (n : ℤ) :
    HasLoopWind (fun t => f t ^ n) (n * k) := by
  rcases n with n | n
  · simpa using wpw_npow hf n
  · have := wpw_inv (wpw_npow hf (n + 1))
    convert this using 1
    · funext t; rw [zpow_negSucc]
    · rw [Int.negSucc_eq]; push_cast; ring

lemma wpw_ccwLoop (ρ : ℝ) (hρ : 0 < ρ) : HasLoopWind (ccwLoop ρ) 1 := by
  have := c1w_hasLoopWind_const_mul_pow 1 one_ne_zero ρ hρ 1
  simpa using this

/-- `t ↦ p + ρ e^{2πit} - q` winds once around `0` when `‖p - q‖ < ρ`. -/
lemma wpw_circle_sub_inside {p q : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (h : ‖p - q‖ < ρ) :
    HasLoopWind (fun t => p + ccwLoop ρ t - q) 1 := by
  refine hasLoopWind_of_re_conj_mul_pos (wpw_ccwLoop ρ hρ)
    ((continuous_const.add (c1w_ccwLoop_continuous ρ)).sub continuous_const)
    (fun t => by simp only [c1w_ccwLoop_periodic ρ t]) fun t => wph_re_conj_mul_pos ?_
  rw [show p + ccwLoop ρ t - q - ccwLoop ρ t = p - q by ring, c1w_norm_ccwLoop ρ t hρ.le]
  exact h

/-- `t ↦ p + ρ e^{2πit} - q` does not wind around `0` when `ρ < ‖p - q‖`. -/
lemma wpw_circle_sub_outside {p q : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (h : ρ < ‖p - q‖) :
    HasLoopWind (fun t => p + ccwLoop ρ t - q) 0 := by
  have hpq : p - q ≠ 0 := fun h0 => by rw [h0, norm_zero] at h; linarith
  refine hasLoopWind_of_re_conj_mul_pos (wpw_const hpq)
    ((continuous_const.add (c1w_ccwLoop_continuous ρ)).sub continuous_const)
    (fun t => by simp only [c1w_ccwLoop_periodic ρ t]) fun t => wph_re_conj_mul_pos ?_
  rw [show p + ccwLoop ρ t - q - (p - q) = ccwLoop ρ t by ring, c1w_norm_ccwLoop ρ t hρ.le]
  exact h

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

/-- A continuous integer-valued real function is constant. -/
lemma wpe_int_const {g : ℝ → ℝ} (hg : Continuous g) (hint : ∀ t, ∃ n : ℤ, g t = n) (t : ℝ) :
    g t = g 0 := by
  obtain ⟨n₀, hn₀⟩ := hint 0
  obtain ⟨n₁, hn₁⟩ := hint t
  by_contra hne
  have hne' : n₀ ≠ n₁ := fun h => hne (by rw [hn₀, hn₁, h])
  set v : ℝ := (min n₀ n₁ : ℤ) + 1 / 2 with hv
  have hmem : v ∈ Set.uIcc (g 0) (g t) := by
    rw [hn₀, hn₁, Set.mem_uIcc]
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have h1 : (n₀ : ℝ) + 1 ≤ n₁ := by exact_mod_cast hlt
      left; rw [hv, min_eq_left hlt.le]; constructor <;> linarith
    · have h1 : (n₁ : ℝ) + 1 ≤ n₀ := by exact_mod_cast hgt
      right; rw [hv, min_eq_right hgt.le]; constructor <;> linarith
  obtain ⟨s, -, hs⟩ := intermediate_value_uIcc hg.continuousOn hmem
  obtain ⟨m, hm⟩ := hint s
  rw [hm, hv] at hs
  have h2 : (2 : ℝ) * (m - (min n₀ n₁ : ℤ)) = 1 := by linarith
  have h3 : (2 : ℤ) * (m - min n₀ n₁) = 1 := by exact_mod_cast h2
  omega

/-- A loop of winding number `0` has a continuous `1`-periodic argument. -/
lemma wpe_periodic_lift {γ : ℝ → ℂ} (h : HasLoopWind γ 0) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧ Function.Periodic θ 1 ∧
      ∀ t, γ t = (‖γ t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I) := by
  obtain ⟨-, hγp, hγ0, θ, hθc, hθ, hθk⟩ := h
  have hpi := Real.pi_pos
  refine ⟨θ, hθc, fun t => ?_, hθ⟩
  set g : ℝ → ℝ := fun t => (θ (t + 1) - θ t) / (2 * π) with hg
  have hgc : Continuous g :=
    ((hθc.comp (continuous_id.add continuous_const)).sub hθc).div_const _
  have hgint : ∀ t, ∃ n : ℤ, g t = n := by
    intro t
    have hn : (‖γ t‖ : ℂ) ≠ 0 := by simpa using hγ0 t
    have he : Complex.exp ((θ (t + 1) : ℂ) * Complex.I) = Complex.exp ((θ t : ℂ) * Complex.I) := by
      have h1 := hθ (t + 1)
      rw [hγp t] at h1
      exact mul_left_cancel₀ hn (h1.symm.trans (hθ t))
    have he1 : Complex.exp (((θ (t + 1) - θ t : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, he, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he1
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    simp only [hg]
    field_simp
    linarith
  have h0 : g 0 = 0 := by simp only [hg, zero_add, hθk]; simp
  have := wpe_int_const hgc hgint t
  rw [h0] at this
  simp only [hg, div_eq_zero_iff] at this
  rcases this with h | h
  · linarith
  · linarith

/-- `w ↦ Θ(arg w / 2π)` is continuous at every `w ≠ 0` when `Θ` is continuous and `1`-periodic. -/
lemma wpe_continuousAt_arg_comp {X : Type*} [TopologicalSpace X] {Θ : ℝ → X}
    (hΘ : Continuous Θ) (hper : Function.Periodic Θ 1) {v : ℂ} (hv : v ≠ 0) :
    ContinuousAt (fun w => Θ (Complex.arg w / (2 * π))) v := by
  have hpi := Real.pi_pos
  by_cases hs : v ∈ Complex.slitPlane
  · exact hΘ.continuousAt.comp ((Complex.continuousAt_arg hs).div_const _)
  · have hre : v.re < 0 := by
      rw [Complex.mem_slitPlane_iff] at hs
      push_neg at hs
      rcases lt_or_eq_of_le hs.1 with h | h
      · exact h
      · exact absurd (Complex.ext h hs.2) hv
    have hs' : -v ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; simp; linarith
    have hc : ContinuousAt (fun w => Θ ((Complex.arg (-w) + π) / (2 * π))) v :=
      hΘ.continuousAt.comp ((((Complex.continuousAt_arg hs').comp
        continuous_neg.continuousAt).add continuousAt_const).div_const _)
    refine hc.congr ?_
    have hev : ∀ᶠ w in 𝓝 v, w.re < 0 :=
      (Complex.continuous_re.continuousAt).eventually (gt_mem_nhds hre)
    filter_upwards [hev] with w hw
    rcases lt_trichotomy w.im 0 with him | him | him
    · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him]
      have := hper (Complex.arg w / (2 * π))
      rw [← this]
      congr 1
      field_simp
      ring
    · have h1 : Complex.arg w = π := Complex.arg_eq_pi_iff.2 ⟨hw, him⟩
      have h2 : Complex.arg (-w) = 0 := Complex.arg_eq_zero_iff.2 ⟨by simp; linarith, by simp [him]⟩
      rw [h1, h2, zero_add]
    · rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him, sub_add_cancel]

/-- A continuous `1`-periodic real function is bounded. -/
lemma wpe_bdd_of_periodic {θ : ℝ → ℝ} (hθ : Continuous θ) (hper : Function.Periodic θ 1) :
    ∃ B, ∀ t, |θ t| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hθ.continuousOn
  refine ⟨B, fun t => ?_⟩
  have e : θ t = θ (Int.fract t) := by
    rw [show Int.fract t = t - ((⌊t⌋ : ℤ) : ℝ) * 1 by rw [mul_one, Int.self_sub_floor]]
    exact (hper.sub_int_mul_eq _).symm
  rw [e, ← Real.norm_eq_abs]
  exact hB _ ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

/-- Filling a hole: a function whose loop along the circle `‖z - p‖ = ρ` has winding number `0`
agrees on that circle with a continuous nowhere-zero function on the closed disc. -/
lemma wpe_extend (g : ℂ → ℂ) (p : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hw : HasLoopWind (fun t => g (p + ccwLoop ρ t)) 0) :
    ∃ h : ℂ → ℂ, ContinuousOn h (closedBall p ρ) ∧ (∀ z ∈ closedBall p ρ, h z ≠ 0) ∧
      ∀ z ∈ sphere p ρ, h z = g z := by
  have hpi := Real.pi_pos
  set γ : ℝ → ℂ := fun t => g (p + ccwLoop ρ t) with hγ
  obtain ⟨hγc, hγp, hγ0, -⟩ := id hw
  obtain ⟨θ, hθc, hθp, hθ⟩ := wpe_periodic_lift hw
  set s : ℂ → ℝ := fun z => Complex.arg (z - p) / (2 * π) with hs
  set a : ℂ → ℝ := fun z => ‖γ (s z)‖ with ha
  set b : ℂ → ℝ := fun z => θ (s z) with hb
  set r : ℂ → ℝ := fun z => ‖z - p‖ / ρ with hr
  set u : ℂ → ℝ := fun z => r z * a z + (1 - r z) with hu
  set h : ℂ → ℂ := fun z => (u z : ℂ) * Complex.exp (((r z * b z : ℝ) : ℂ) * Complex.I) with hh
  have hsub : ∀ z : ℂ, ContinuousAt (fun w : ℂ => w - p) z := fun z =>
    (continuous_id.sub continuous_const).continuousAt
  have hac : ∀ z, z ≠ p → ContinuousAt a z := fun z hz =>
    ContinuousAt.comp (f := fun w : ℂ => w - p) (x := z)
      (wpe_continuousAt_arg_comp (hγc.norm) (fun t => by simp only [hγp t]) (sub_ne_zero.2 hz))
      (hsub z)
  have hbc : ∀ z, z ≠ p → ContinuousAt b z := fun z hz =>
    ContinuousAt.comp (f := fun w : ℂ => w - p) (x := z)
      (wpe_continuousAt_arg_comp hθc hθp (sub_ne_zero.2 hz)) (hsub z)
  have hrc : Continuous r := (continuous_norm.comp (continuous_id.sub continuous_const)).div_const _
  have hhc_ne : ∀ z, z ≠ p → ContinuousAt h z := by
    intro z hz
    have hu' : ContinuousAt u z :=
      ((hrc.continuousAt.mul (hac z hz)).add (continuousAt_const.sub hrc.continuousAt))
    exact (Complex.continuous_ofReal.continuousAt.comp hu').mul
      (Complex.continuous_exp.continuousAt.comp
        ((Complex.continuous_ofReal.continuousAt.comp (hrc.continuousAt.mul (hbc z hz))).mul
          continuousAt_const))
  -- bounds on `a` and `b`
  obtain ⟨A, hA⟩ := wpe_bdd_of_periodic hγc.norm (fun t => by simp only [hγp t])
  obtain ⟨B, hB⟩ := wpe_bdd_of_periodic hθc hθp
  have hr0 : Tendsto r (𝓝 p) (𝓝 0) := by
    have := hrc.tendsto p
    simpa [hr] using this
  have hu1 : Tendsto u (𝓝 p) (𝓝 1) := by
    have h1 : Tendsto (fun z => r z * (a z - 1)) (𝓝 p) (𝓝 0) := by
      refine squeeze_zero_norm (a := fun z => r z * (A + 1)) (fun z => ?_) ?_
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ r z)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := hA (s z)
        rw [abs_le] at this
        rw [Real.norm_eq_abs, abs_le]; constructor <;> simp only [ha] at * <;> linarith
      · simpa using hr0.mul_const (A + 1)
    have := h1.const_add 1
    simp only [add_zero] at this
    refine this.congr fun z => ?_
    simp only [hu]; ring
  have hv0 : Tendsto (fun z => r z * b z) (𝓝 p) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun z => r z * B) (fun z => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ r z)]
      exact mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact hB _) (by positivity)
    · simpa using hr0.mul_const B
  have hhp : h p = 1 := by simp [hh, hu, hr]
  have hhc_p : ContinuousAt h p := by
    rw [ContinuousAt, hhp]
    have := ((Complex.continuous_ofReal.tendsto 1).comp hu1).mul
      ((Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto 0).comp hv0).mul_const Complex.I))
    have h2 : Tendsto (fun z => (u z : ℂ) * Complex.exp ((r z : ℂ) * (b z : ℂ) * Complex.I))
        (𝓝 p) (𝓝 1) := by simpa using this
    refine h2.congr fun z => ?_
    simp only [hh, Complex.ofReal_mul]
  refine ⟨h, fun z _ => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · by_cases hzp : z = p
    · rw [hzp]; exact hhc_p.continuousWithinAt
    · exact (hhc_ne z hzp).continuousWithinAt
  · have hr1 : r z ≤ 1 := by
      rw [hr, div_le_one hρ, ← dist_eq_norm]; exact hz
    have hr0' : 0 ≤ r z := by positivity
    have ha0 : 0 < a z := norm_pos_iff.2 (hγ0 _)
    have hu0 : 0 < u z := by
      simp only [hu]
      rcases lt_or_eq_of_le hr1 with h1 | h1
      · nlinarith
      · rw [h1]; linarith
    simp only [hh]
    exact mul_ne_zero (by exact_mod_cast hu0.ne') (Complex.exp_ne_zero _)
  · have hn : ‖z - p‖ = ρ := by rw [← dist_eq_norm]; exact hz
    have hr1 : r z = 1 := by simp only [hr, hn, div_self hρ.ne']
    have hzp : z - p ≠ 0 := fun h0 => by rw [h0, norm_zero] at hn; linarith
    simp only [hh, hu, hr1, one_mul, sub_self, add_zero]
    rw [show a z = ‖γ (s z)‖ from rfl, show b z = θ (s z) from rfl, ← hθ (s z)]
    simp only [hγ, ccwLoop, hs]
    congr 1
    rw [show ((2 * π * (Complex.arg (z - p) / (2 * π)) : ℝ) : ℂ) = (Complex.arg (z - p) : ℂ) by
      congr 1; field_simp, ← hn, Complex.norm_mul_exp_arg_mul_I]
    ring

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

lemma wpa_mem_sphere (p : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) : p + ccwLoop ρ t ∈ sphere p ρ := by
  rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, c1w_norm_ccwLoop ρ t hρ]

lemma wpa_dist (p : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) : dist (p + ccwLoop ρ t) p = ρ :=
  wpa_mem_sphere p hρ t

/-- A point outside a finite set is at positive distance from it. -/
lemma wpa_sep (P : Finset ℂ) {p : ℂ} (hp : p ∉ P) : ∃ ε > (0 : ℝ), ∀ q ∈ P, ε ≤ dist q p := by
  have hn : (↑P : Set ℂ)ᶜ ∈ 𝓝 p := P.finite_toSet.isClosed.isOpen_compl.mem_nhds hp
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hn
  refine ⟨ε, hε, fun q hq => ?_⟩
  by_contra h
  push_neg at h
  exact hεs (mem_ball.2 h) hq

lemma wpw_prod (P : Finset ℂ) (f : ℂ → ℝ → ℂ) (k : ℂ → ℤ)
    (h : ∀ q ∈ P, HasLoopWind (f q) (k q)) :
    HasLoopWind (fun t => ∏ q ∈ P, f q t) (∑ q ∈ P, k q) := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa using wpw_const (one_ne_zero (α := ℂ))
  | insert q P hq ih =>
    have := hasLoopWind_mul (h q (Finset.mem_insert_self q P))
      (ih fun q' hq' => h q' (Finset.mem_insert_of_mem hq'))
    simpa [Finset.prod_insert hq, Finset.sum_insert hq] using this

/-- The zero-winding case: no holes contribute. -/
lemma wpa_zero (c : ℂ) (R : ℝ) (hR : 0 < R) (P : Finset ℂ) :
    ∀ g : ℂ → ℂ, (∀ p ∈ P, p ∈ ball c R) → ContinuousOn g (closedBall c R \ ↑P) →
      (∀ z ∈ closedBall c R \ ↑P, g z ≠ 0) →
      (∀ p ∈ P, ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
        HasLoopWind (fun t => g (p + ccwLoop ρ t)) 0) →
      HasLoopWind (fun t => g (c + ccwLoop R t)) 0 := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro g _ hg hg0 _
    simp only [Finset.coe_empty, Set.diff_empty] at hg hg0
    set F : ℝ → ℝ → ℂ := fun l t => g (c + ccwLoop l t) with hF
    have hmaps : ∀ l ∈ Set.Icc 0 R, ∀ t, c + ccwLoop l t ∈ closedBall c R := fun l hl t => by
      rw [mem_closedBall, wpa_dist c hl.1 t]; exact hl.2
    have hFc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc 0 R ×ˢ Set.univ) := by
      refine hg.comp (Continuous.continuousOn ?_) fun p hp => hmaps p.1 hp.1 p.2
      unfold ccwLoop; fun_prop
    have h0 : HasLoopWind (F 0) 0 := by
      have : F 0 = fun _ => g c := funext fun t => by simp [hF, ccwLoop]
      rw [this]
      exact wpw_const (hg0 c (mem_closedBall_self hR.le))
    exact hasLoopWind_of_continuousOn_family F hFc
      (fun l _ t => by simp only [hF, c1w_ccwLoop_periodic l t])
      (fun l hl t => hg0 _ (hmaps l hl t)) h0 R ⟨hR.le, le_rfl⟩
  | insert p P hpP ih =>
    intro g hP hg hg0 hm
    have hpB : p ∈ ball c R := hP p (Finset.mem_insert_self p P)
    obtain ⟨rp, hrp, hrpw⟩ := hm p (Finset.mem_insert_self p P)
    obtain ⟨ε, hε, hεP⟩ := wpa_sep P hpP
    have hdp : dist p c < R := hpB
    set ρ := min (min (rp / 2) ((R - dist p c) / 2)) (ε / 2) with hρdef
    have hρ0 : 0 < ρ := lt_min (lt_min (half_pos hrp) (half_pos (by linarith))) (half_pos hε)
    have hρrp : ρ < rp := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _))
      (half_lt_self hrp)
    have hρR : ρ < R - dist p c := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _))
      (half_lt_self (by linarith))
    have hρε : ρ < ε := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε)
    obtain ⟨h, hhc, hh0, hhg⟩ := wpe_extend g p hρ0 (hrpw ρ ⟨hρ0, hρrp⟩)
    set G : ℂ → ℂ := (ball p ρ).piecewise h g with hG
    have hcoe : (↑(insert p P) : Set ℂ) = insert p ↑P := Finset.coe_insert p P
    -- points outside `ball p ρ` that avoid `P` avoid `insert p P`
    have hout : ∀ z ∈ closedBall c R \ ↑P, z ∉ ball p ρ → z ∈ closedBall c R \ ↑(insert p P) := by
      intro z hz hzb
      refine ⟨hz.1, ?_⟩
      rw [hcoe]
      rintro (h1 | h1)
      · exact hzb (h1 ▸ mem_ball_self hρ0)
      · exact hz.2 h1
    have hGc : ContinuousOn G (closedBall c R \ ↑P) := by
      refine ContinuousOn.piecewise ?_ ?_ ?_
      · intro z hz
        rw [frontier_ball p hρ0.ne'] at hz
        exact hhg z hz.2
      · rw [closure_ball p hρ0.ne']
        exact hhc.mono Set.inter_subset_right
      · rw [isOpen_ball.isClosed_compl.closure_eq]
        exact hg.mono fun z hz => hout z hz.1 hz.2
    have hG0 : ∀ z ∈ closedBall c R \ ↑P, G z ≠ 0 := by
      intro z hz
      by_cases hzb : z ∈ ball p ρ
      · rw [hG, Set.piecewise_eq_of_mem _ _ _ hzb]
        exact hh0 z (ball_subset_closedBall hzb)
      · rw [hG, Set.piecewise_eq_of_notMem _ _ _ hzb]
        exact hg0 z (hout z hz hzb)
    have hGm : ∀ q ∈ P, ∃ r > (0 : ℝ), ∀ ρ' ∈ Set.Ioo 0 r,
        HasLoopWind (fun t => G (q + ccwLoop ρ' t)) 0 := by
      intro q hq
      obtain ⟨rq, hrq, hrqw⟩ := hm q (Finset.mem_insert_of_mem hq)
      have hqp := hεP q hq
      refine ⟨min rq (ε - ρ), lt_min hrq (by linarith), fun ρ' hρ' => ?_⟩
      have h1 : ρ' < rq := lt_of_lt_of_le hρ'.2 (min_le_left _ _)
      have h2 : ρ' < ε - ρ := lt_of_lt_of_le hρ'.2 (min_le_right _ _)
      convert hrqw ρ' ⟨hρ'.1, h1⟩ using 2 with t
      rw [hG, Set.piecewise_eq_of_notMem]
      rw [mem_ball, not_lt]
      have h3 := dist_triangle q (q + ccwLoop ρ' t) p
      have h4 : dist q (q + ccwLoop ρ' t) = ρ' := by rw [dist_comm]; exact wpa_dist q hρ'.1.le t
      linarith
    have hmain := ih G (fun q hq => hP q (Finset.mem_insert_of_mem hq)) hGc hG0 hGm
    convert hmain using 2 with t
    rw [hG, Set.piecewise_eq_of_notMem]
    rw [mem_ball, not_lt]
    have h3 := dist_triangle c p (c + ccwLoop R t)
    have h4 : dist c (c + ccwLoop R t) = R := by rw [dist_comm]; exact wpa_dist c hR.le t
    have h5 : dist c p = dist p c := dist_comm _ _
    have h6 : dist p (c + ccwLoop R t) = dist (c + ccwLoop R t) p := dist_comm _ _
    linarith

theorem hasLoopWind_ccwLoop_eq_sum_aux (g : ℂ → ℂ) (P : Finset ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hP : ∀ p ∈ P, p ∈ ball c R) (hg : ContinuousOn g (closedBall c R \ ↑P))
    (hg0 : ∀ z ∈ closedBall c R \ ↑P, g z ≠ 0) (m : ℂ → ℤ)
    (hm : ∀ p ∈ P, ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => g (p + ccwLoop ρ t)) (m p)) :
    HasLoopWind (fun t => g (c + ccwLoop R t)) (∑ p ∈ P, m p) := by
  classical
  set D := closedBall c R \ (↑P : Set ℂ) with hD
  have hsub0 : ∀ z ∈ D, ∀ q ∈ P, z - q ≠ 0 := fun z hz q hq h =>
    hz.2 (by rw [sub_eq_zero.1 h]; exact hq)
  set g₁ : ℂ → ℂ := fun z => g z * ∏ q ∈ P, (z - q) ^ (-(m q)) with hg₁
  have hg₁c : ContinuousOn g₁ D := by
    refine hg.mul (continuousOn_finset_prod _ fun q hq => ?_)
    exact ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun z hz => Or.inl (hsub0 z hz q hq))
  have hg₁0 : ∀ z ∈ D, g₁ z ≠ 0 := fun z hz =>
    mul_ne_zero (hg0 z hz) (Finset.prod_ne_zero_iff.2 fun q hq => zpow_ne_zero _ (hsub0 z hz q hq))
  -- windings of `g₁` at the holes vanish
  have hg₁m : ∀ p ∈ P, ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => g₁ (p + ccwLoop ρ t)) 0 := by
    intro p hp
    obtain ⟨rp, hrp, hrpw⟩ := hm p hp
    obtain ⟨ε, hε, hεP⟩ := wpa_sep (P.erase p) (Finset.notMem_erase p P)
    refine ⟨min rp ε, lt_min hrp hε, fun ρ hρ => ?_⟩
    have h1 : ρ < rp := lt_of_lt_of_le hρ.2 (min_le_left _ _)
    have h2 : ρ < ε := lt_of_lt_of_le hρ.2 (min_le_right _ _)
    have hw := hrpw ρ ⟨hρ.1, h1⟩
    have hq : ∀ q ∈ P, HasLoopWind (fun t => (p + ccwLoop ρ t - q) ^ (-(m q)))
        (if q = p then -(m p) else 0) := by
      intro q hq
      by_cases hqp : q = p
      · rw [if_pos hqp, hqp]
        have := wpw_zpow (wpw_circle_sub_inside (p := p) (q := p) hρ.1
          (by rw [sub_self, norm_zero]; exact hρ.1)) (-(m p))
        simpa using this
      · have hd : ρ < ‖p - q‖ := by
          have := hεP q (Finset.mem_erase.2 ⟨hqp, hq⟩)
          rw [dist_eq_norm, ← norm_neg, neg_sub] at this
          linarith
        have := wpw_zpow (wpw_circle_sub_outside hρ.1 hd) (-(m q))
        simpa [hqp] using this
    have hprod := hasLoopWind_mul hw (wpw_prod P _ _ hq)
    rw [Finset.sum_ite_eq' P p, if_pos hp, add_neg_cancel] at hprod
    exact hprod
  -- the boundary circle
  have hbig := wpa_zero c R hR P g₁ hP hg₁c hg₁0 hg₁m
  have hq : ∀ q ∈ P, HasLoopWind (fun t => (c + ccwLoop R t - q) ^ (m q)) (m q) := by
    intro q hq
    have hd : ‖c - q‖ < R := by rw [← dist_eq_norm, dist_comm]; exact hP q hq
    simpa using wpw_zpow (wpw_circle_sub_inside hR hd) (m q)
  have hprod := hasLoopWind_mul hbig (wpw_prod P _ _ hq)
  rw [zero_add] at hprod
  convert hprod using 2 with t
  have hzD : c + ccwLoop R t ∈ closedBall c R \ ↑P := by
    refine ⟨by rw [mem_closedBall, wpa_dist c hR.le t], fun hmem => ?_⟩
    have := hP _ hmem
    rw [mem_ball, wpa_dist c hR.le t] at this
    exact lt_irrefl _ this
  simp only [hg₁, mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.prod_eq_one fun q hq => ?_, mul_one]
  rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hsub0 _ hzD q hq))]

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric

theorem solution (g : ℂ → ℂ) (P : Finset ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hP : ∀ p ∈ P, p ∈ ball c R) (hg : ContinuousOn g (closedBall c R \ ↑P))
    (hg0 : ∀ z ∈ closedBall c R \ ↑P, g z ≠ 0) (m : ℂ → ℤ)
    (hm : ∀ p ∈ P, ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => g (p + ccwLoop ρ t)) (m p)) :
    HasLoopWind (fun t => g (c + ccwLoop R t)) (∑ p ∈ P, m p) :=
  hasLoopWind_ccwLoop_eq_sum_aux g P c R hR hP hg hg0 m hm
