-- Prove2me | solution 1 for BroughanRH.liExponentialLower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:41:34.788096+00:00
-- url     : https://prove2.me/submissions/baf30512-3059-417c-8d9b-4936285ff8ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_ConnesRZ_actual_zero_reciprocal_square_summable
import Theorems.Thm_BranchActualCount_concrete_zero_count_bounds

open Complex

lemma zs_unit_re (v : ℂ) (hv : ‖v‖ = 1) : (1 - v).re = ‖1 - v‖ ^ 2 / 2 := by
  have h1 : v.re ^ 2 + v.im ^ 2 = 1 := by
    have := Complex.sq_norm v
    rw [hv, Complex.normSq_apply] at this
    nlinarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith

lemma zs_pow_bound (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) : ‖1 - w ^ n‖ ≤ n * ‖1 - w‖ := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : 1 - w ^ (k + 1) = (1 - w ^ k) + w ^ k * (1 - w) := by ring
    rw [this]
    calc ‖(1 - w ^ k) + w ^ k * (1 - w)‖ ≤ ‖1 - w ^ k‖ + ‖w ^ k * (1 - w)‖ := norm_add_le _ _
      _ ≤ k * ‖1 - w‖ + ‖1 - w‖ := by
          gcongr
          rw [norm_mul, norm_pow, hw]; simp
      _ = ((k + 1 : ℕ) : ℝ) * ‖1 - w‖ := by push_cast; ring

lemma zs_re_bounds (w : ℂ) (hw : ‖w‖ = 1) (n : ℕ) :
    0 ≤ (1 - w ^ n).re ∧ (1 - w ^ n).re ≤ (n : ℝ) ^ 2 * ‖1 - w‖ ^ 2 / 2 := by
  have hwn : ‖w ^ n‖ = 1 := by rw [norm_pow, hw, one_pow]
  rw [zs_unit_re _ hwn]
  refine ⟨by positivity, ?_⟩
  have := zs_pow_bound w hw n
  have h0 : 0 ≤ ‖1 - w ^ n‖ := norm_nonneg _
  have : ‖1 - w ^ n‖ ^ 2 ≤ (n * ‖1 - w‖) ^ 2 := by gcongr
  nlinarith

/-- Under RH, every critical-strip zero lies on the critical line. -/
lemma zs_re_half (s : ℂ) (hs : ConnesRZ.IsCriticalZero s) : s.re = 1 / 2 := by
  obtain ⟨hz, h0, h1⟩ := hs
  refine riemann_hypothesis s hz ?_ ?_
  · rintro ⟨n, rfl⟩
    simp at h0
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · rintro rfl; simp at h1

lemma zs_normSq_shift (s : ℂ) (hs : s.re = 1 / 2) :
    Complex.normSq ((s - 1 / 2) / Complex.I) = s.im ^ 2 := by
  rw [Complex.normSq_div, Complex.normSq_I, div_one, Complex.normSq_apply]
  simp [hs]; ring

lemma zs_analyticAt (s : ℂ) (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)

/-- There are zeta zeros of positive multiplicity at arbitrarily large height. -/
lemma zs_exists_large_zero (M : ℝ) :
    ∃ s : ℂ, riemannZeta s = 0 ∧ M < s.im ∧ analyticOrderNatAt riemannZeta s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set M' := max M 1 with hM'
  obtain ⟨-, hev⟩ := BranchActualCount.concrete_zero_count_bounds
  set f : ℂ → ℝ := fun s => (((meromorphicOrderAt riemannZeta s).untopD 0 : ℤ) : ℝ) with hf
  let S : ℝ → Set ℂ := fun T => {s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z = 0}}
  have hfz : ∀ s : ℂ, riemannZeta s = 0 → M' < s.im → f s = 0 := by
    intro s hz him
    have hs1 : s ≠ 1 := by
      rintro rfl; simp at him; have := le_max_right M 1; linarith
    have han := zs_analyticAt s hs1
    have h0 := hcon s hz (lt_of_le_of_lt (le_max_left M 1) him)
    simp only [hf, han.meromorphicOrderAt_eq]
    unfold analyticOrderNatAt at h0
    by_cases ht : analyticOrderAt riemannZeta s = ⊤
    · rw [ht]; simp
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp ht
      rw [← hk] at h0 ⊢
      simp at h0
      subst h0
      simp
  have hconst : ∀ T ≥ M' + 1, (∑' ρ : S T, f ρ) = ∑' ρ : S (M' + 1), f ρ := by
    intro T hT
    rw [tsum_subtype (S T) f, tsum_subtype (S (M' + 1)) f]
    congr 1
    funext x
    by_cases hx : x ∈ S (M' + 1)
    · have hx' : x ∈ S T := by
        obtain ⟨a, ⟨b, c⟩, d⟩ := hx
        exact ⟨a, ⟨b, by linarith⟩, d⟩
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · rw [Set.indicator_of_notMem hx]
      by_cases hx' : x ∈ S T
      · rw [Set.indicator_of_mem hx']
        obtain ⟨_, ⟨b, _⟩, d⟩ := hx'
        apply hfz x d
        by_contra hle
        push Not at hle
        exact hx ⟨trivial, ⟨b, by linarith⟩, d⟩
      · rw [Set.indicator_of_notMem hx']
  set c := ∑' ρ : S (M' + 1), f ρ
  have hK := (hev.and (Filter.eventually_ge_atTop (max (M' + 1) (max (Real.exp 1)
    (32 * Real.pi * (|c| + 1)))))).exists
  obtain ⟨T, hT1, hT2⟩ := hK
  have hTa : M' + 1 ≤ T := le_trans (le_max_left _ _) hT2
  have hTb : Real.exp 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT2
  have hTc : 32 * Real.pi * (|c| + 1) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT2
  have hNT : (∑' ρ : S T, f ρ) = c := hconst T hTa
  simp only at hT1
  change T * Real.log T / (32 * Real.pi) ≤ ∑' ρ : S T, f ρ at hT1
  rw [hNT] at hT1
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]; exact hTb
  have hpi : 0 < Real.pi := Real.pi_pos
  have hT0 : 0 < T := by linarith [Real.exp_pos 1]
  have : T ≤ T * Real.log T := by nlinarith
  have h32 : |c| + 1 ≤ T * Real.log T / (32 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have := le_abs_self c
  linarith

theorem zs_liZeroSum :
    let Z := {s : ℂ // ConnesRZ.IsCriticalZero s}
    ∀ n : ℕ, 0 < n →
      let u (ρ : Z) : ℝ := (ConnesRZ.zeroMult ρ.val : ℝ) * (1 - (1 - 1/ρ.val)^n).re
      Summable u ∧ 0 < ∑' ρ : Z, u ρ := by
  intro Z n hn u
  -- termwise bounds
  have hw : ∀ ρ : Z, ‖1 - 1 / ρ.val‖ = 1 ∧ ‖1 - (1 - 1 / ρ.val)‖ ^ 2 = 1 / (1 / 4 + ρ.val.im ^ 2) := by
    intro ρ
    have hre := zs_re_half ρ.val ρ.2
    have hne : ρ.val ≠ 0 := by intro h; rw [h] at hre; simp at hre
    have hn2 : Complex.normSq ρ.val = 1 / 4 + ρ.val.im ^ 2 := by
      rw [Complex.normSq_apply, hre]; ring
    constructor
    · have : 1 - 1 / ρ.val = (ρ.val - 1) / ρ.val := by field_simp
      rw [this, norm_div]
      have h2 : ‖ρ.val - 1‖ = ‖ρ.val‖ := by
        rw [← Real.sqrt_sq (norm_nonneg (ρ.val - 1)), ← Real.sqrt_sq (norm_nonneg ρ.val),
          Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
        congr 1; simp [hre]; ring
      rw [h2, div_self (norm_ne_zero_iff.mpr hne)]
    · rw [sub_sub_cancel, Complex.sq_norm, Complex.normSq_div, hn2]; simp
  have hbd : ∀ ρ : Z, 0 ≤ u ρ ∧ u ρ ≤ (2 * (n : ℝ) ^ 2) *
      ((ConnesRZ.zeroMult ρ.1 : ℝ) / (1 + Complex.normSq ((ρ.1 - 1 / 2) / Complex.I))) := by
    intro ρ
    obtain ⟨h1, h2⟩ := hw ρ
    obtain ⟨b0, b1⟩ := zs_re_bounds _ h1 n
    rw [h2] at b1
    rw [zs_normSq_shift _ (zs_re_half ρ.val ρ.2)]
    have hm : (0 : ℝ) ≤ ConnesRZ.zeroMult ρ.val := Nat.cast_nonneg _
    refine ⟨mul_nonneg hm b0, ?_⟩
    have hg : 0 ≤ ρ.val.im ^ 2 := sq_nonneg _
    have key : (n : ℝ) ^ 2 * (1 / (1 / 4 + ρ.val.im ^ 2)) / 2 ≤ 2 * (n : ℝ) ^ 2 / (1 + ρ.val.im ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      rw [mul_one_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have : (0:ℝ) ≤ (n:ℝ)^2 := sq_nonneg _
      nlinarith
    calc (ConnesRZ.zeroMult ρ.val : ℝ) * (1 - (1 - 1 / ρ.val) ^ n).re
        ≤ (ConnesRZ.zeroMult ρ.val : ℝ) * (2 * (n : ℝ) ^ 2 / (1 + ρ.val.im ^ 2)) :=
          mul_le_mul_of_nonneg_left (b1.trans key) hm
      _ = _ := by ring
  have hsum : Summable u :=
    Summable.of_nonneg_of_le (fun ρ => (hbd ρ).1) (fun ρ => (hbd ρ).2)
      (ConnesRZ.actual_zero_reciprocal_square_summable.mul_left _)
  refine ⟨hsum, ?_⟩
  -- a large zero gives a strictly positive term
  obtain ⟨s, hz, him, hord⟩ := zs_exists_large_zero (n + 1)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : s ≠ 1 := by rintro rfl; simp at him; linarith
  have hre : s.re = 1 / 2 := by
    refine riemann_hypothesis s hz ?_ hs1
    rintro ⟨m, rfl⟩; simp at him; linarith
  have hcrit : ConnesRZ.IsCriticalZero s := ⟨hz, by rw [hre]; norm_num, by rw [hre]; norm_num⟩
  refine hsum.tsum_pos (fun ρ => (hbd ρ).1) ⟨s, hcrit⟩ ?_
  show 0 < (ConnesRZ.zeroMult s : ℝ) * (1 - (1 - 1 / s) ^ n).re
  have hm : (0 : ℝ) < ConnesRZ.zeroMult s := by
    have : ConnesRZ.zeroMult s ≠ 0 := hord
    exact_mod_cast Nat.pos_of_ne_zero this
  refine mul_pos hm ?_
  set γ := s.im with hγ
  set w := 1 - 1 / s with hwdef
  have hγ1 : 1 < γ := by linarith
  have hD : 0 < 1 / 4 + γ ^ 2 := by positivity
  have hwre : w.re = 1 - (1 / 2) / (1 / 4 + γ ^ 2) := by
    simp [hwdef, Complex.inv_re, Complex.normSq_apply, hre]; ring_nf <;> rfl
  have hwim : w.im = γ / (1 / 4 + γ ^ 2) := by
    simp [hwdef, Complex.inv_im, Complex.normSq_apply, hre]; ring_nf <;> rfl
  have hwre_pos : 0 < w.re := by
    rw [hwre, sub_pos, div_lt_one hD]; nlinarith
  have hwim_pos : 0 < w.im := by rw [hwim]; positivity
  have hwnorm : ‖w‖ = 1 := by
    have hne : s ≠ 0 := by intro h; rw [h] at hre; simp at hre
    have : w = (s - 1) / s := by rw [hwdef]; field_simp
    rw [this, norm_div]
    have h2 : ‖s - 1‖ = ‖s‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (s - 1)), ← Real.sqrt_sq (norm_nonneg s),
        Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      congr 1; simp [hre]; ring
    rw [h2, div_self (norm_ne_zero_iff.mpr hne)]
  set θ := Complex.arg w with hθ
  have hθlt : |θ| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre_pos)
  have hθnn : 0 ≤ θ := Complex.arg_nonneg_iff.mpr hwim_pos.le
  have hθne : θ ≠ 0 := by
    intro h; rw [hθ, Complex.arg_eq_zero_iff] at h; linarith [h.2]
  have hθpos : 0 < θ := lt_of_le_of_ne hθnn (Ne.symm hθne)
  have hθle : θ ≤ Real.pi / 2 := le_of_lt (lt_of_le_of_lt (le_abs_self θ) hθlt)
  have hsin : Real.sin θ = w.im := by rw [hθ, Complex.sin_arg, hwnorm, div_one]
  have hjordan := Real.mul_le_sin hθnn hθle
  rw [hsin, hwim] at hjordan
  have hpi : 0 < Real.pi := Real.pi_pos
  -- θ ≤ (π/2) γ / (1/4+γ²) < π/(2γ)
  have hθb : θ * γ < Real.pi / 2 := by
    have h1 : θ ≤ Real.pi / 2 * (γ / (1 / 4 + γ ^ 2)) := by
      have := hjordan
      rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at this
      nlinarith
    have h2 : γ / (1 / 4 + γ ^ 2) * γ < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hD]; nlinarith
    calc θ * γ ≤ Real.pi / 2 * (γ / (1 / 4 + γ ^ 2)) * γ := by gcongr
      _ = Real.pi / 2 * (γ / (1 / 4 + γ ^ 2) * γ) := by ring
      _ < Real.pi / 2 * 1 := by gcongr
      _ = Real.pi / 2 := by ring
  have hnθ : (n : ℝ) * θ < Real.pi := by
    have : (n : ℝ) * θ ≤ γ * θ := by gcongr; linarith
    nlinarith
  have hnθpos : 0 < (n : ℝ) * θ := by positivity
  have hwexp : w ^ n = Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I w
    rw [hwnorm] at this
    simp only [Complex.ofReal_one, one_mul] at this
    rw [← this, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [Complex.sub_re, Complex.one_re, hwexp, Complex.exp_ofReal_mul_I_re, sub_pos]
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hnθ.le hnθpos
  simpa using this

theorem solution :
    let Z := {s : ℂ // ConnesRZ.IsCriticalZero s}
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      let u (ρ : Z) : ℝ := (ConnesRZ.zeroMult ρ.val : ℝ) * (1 - (1 - 1/ρ.val)^n).re
      Summable u ∧ -(C * Real.exp (ε * n)) ≤ ∑' ρ : Z, u ρ := by
  intro Z ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro n hn
  obtain ⟨hs, hp⟩ := zs_liZeroSum n hn
  exact ⟨hs, le_trans (neg_nonpos.mpr (mul_nonneg zero_le_one (Real.exp_pos _).le)) hp.le⟩
