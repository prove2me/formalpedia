-- Prove2me | solution 1 for DatkoDelayWave.BoundaryDelay.theorem_i_uniform_decay
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:07.517996+00:00
-- url     : https://prove2.me/submissions/4fbcfb17-23a3-4e5a-9f68-77bd61923cb8

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

-- carved verbatim out of submission 9e78ff97-3a87-4a96-9f66-6a86542faea0, lines 1074-1089

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
open Complex
open DatkoDelayWave
open DatkoDelayWave.BoundaryDelay
open Set Filter Metric
open scoped Topology

theorem K_pos (a : ℝ) : 0 < K a := Real.exp_pos _

theorem f_h_regular (a k : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) :
    Continuous (fun p : ℝ × ℂ => f a k p.1 p.2) ∧ Continuous (fun p : ℝ × ℂ => h a k p.1 p.2) ∧
    (∀ ε, Differentiable ℂ (f a k ε)) ∧ (∀ ε, Differentiable ℂ (h a k ε)) ∧
    ∀ ε, ∀ x : ℝ, 0 < x → f a k ε (x : ℂ) ≠ 0 ∧ h a k ε (x : ℂ) ≠ 0 := by
  have hf : Continuous (fun p : ℝ × ℂ => f a k p.1 p.2) := by
    unfold f; fun_prop
  have hdf : ∀ ε, Differentiable ℂ (f a k ε) := by
    intro ε; unfold f; fun_prop
  refine ⟨hf, ?_, hdf, ?_, ?_⟩
  · unfold h; refine Continuous.add ?_ ?_
    · exact continuous_snd.mul hf
    · fun_prop
  · intro ε; unfold h; exact ((differentiable_id).mul (hdf ε)).add (by fun_prop)
  · intro ε x hx
    have hK := K_pos a
    have hex : Real.exp (-2 * a) * Real.exp (-2 * x) < 1 := by
      rw [← Real.exp_add, Real.exp_lt_one_iff]; linarith
    have e1 : 0 < 1 + K a * Real.exp (-2 * x) := by positivity
    have e2 : 0 < 1 - K a * Real.exp (-2 * x) := by unfold K; linarith
    have hfeq : f a k ε (x : ℂ) = ((1 + K a * Real.exp (-2 * x)
        + k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x)) : ℝ) : ℂ) := by
      unfold f; push_cast
      simp [Complex.ofReal_exp]
    have fpos : 0 < 1 + K a * Real.exp (-2 * x)
        + k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x)) := by
      have : 0 ≤ k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x)) := by positivity
      linarith
    have hheq : h a k ε (x : ℂ) = (((x : ℝ) * (1 + K a * Real.exp (-2 * x)
        + k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x))) + a * (1 + K a * Real.exp (-2 * x)) : ℝ) : ℂ) := by
      unfold h; rw [hfeq]; push_cast
      simp [Complex.ofReal_exp]
    refine ⟨?_, ?_⟩
    · rw [hfeq]; exact_mod_cast fpos.ne'
    · rw [hheq]
      have : 0 < x * (1 + K a * Real.exp (-2 * x)
        + k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x))) + a * (1 + K a * Real.exp (-2 * x)) := by
        have := mul_pos hx fpos
        have : 0 ≤ a * (1 + K a * Real.exp (-2 * x)) := by positivity
        linarith
      exact_mod_cast this.ne'

theorem key_identity (a k ε : ℝ) (ω : ℂ) :
    ((a : ℂ) + ω) * Complex.cosh ((a : ℂ) + ω)
      + (k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * Complex.sinh ((a : ℂ) + ω)
      = Complex.exp ((a : ℂ) + ω) / 2 * h a k ε ω := by
  have hK : (K a : ℂ) = Complex.exp (-2 * (a : ℂ)) := by
    unfold K; rw [Complex.ofReal_exp]; push_cast; ring_nf
  have hq : Complex.exp (-((a : ℂ) + ω))
      = Complex.exp ((a : ℂ) + ω) * ((K a : ℂ) * Complex.exp (-2 * ω)) := by
    rw [hK, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  unfold h f
  simp only [Complex.cosh, Complex.sinh]
  rw [hq]
  ring

theorem const_of_hasDeriv_zero (V V' : ℝ → ℂ) (hV : ∀ x, HasDerivAt V (V' x) x)
    (h0 : ∀ x ∈ Icc (0 : ℝ) 1, V' x = 0) : ∀ x ∈ Icc (0 : ℝ) 1, V x = V 0 := by
  apply constant_of_derivWithin_zero
  · intro x _; exact (hV x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hx
    rw [((hV x).hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc zero_lt_one x hx')]
    exact h0 x hx'

theorem eig_explicit (a k ε : ℝ) (ω : ℂ) (φ : ℝ → ℂ) (hφ : IsEigenpair a k ε ω φ) :
    ∀ x ∈ Icc (0 : ℝ) 1, deriv φ x = deriv φ 0 * Complex.cosh (((a : ℂ) + ω) * x) ∧
      ((a : ℂ) + ω) * φ x = deriv φ 0 * Complex.sinh (((a : ℂ) + ω) * x) := by
  set l : ℂ := (a : ℂ) + ω with hl
  have hC2 : ContDiff ℝ 2 φ := hφ.contDiff
  have hd1 : Differentiable ℝ φ := hC2.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv φ) := hC2.differentiable_deriv_two
  have hC1 : ContDiff ℝ 1 (deriv φ) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) φ from hC2)).2.2
  have hcdd : Continuous (deriv (deriv φ)) := hC1.continuous_deriv_one
  have hode : ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv φ) x = l ^ 2 * φ x := by
    have hEq : EqOn (deriv (deriv φ)) (fun x => l ^ 2 * φ x) (Ioo 0 1) := hφ.ode
    exact hEq.of_subset_closure hcdd.continuousOn
      (continuous_const.mul hd1.continuous).continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)])
  have hlin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => l * (x : ℂ)) l x := by
    intro x
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul l
  have hch : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.cosh (l * (x : ℂ)))
      (Complex.sinh (l * (x : ℂ)) * l) x := fun x => by
    have := (Complex.hasDerivAt_cosh (l * (x : ℂ))).scomp x (hlin x)
    exact this.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hsh : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.sinh (l * (x : ℂ)))
      (Complex.cosh (l * (x : ℂ)) * l) x := fun x => by
    have := (Complex.hasDerivAt_sinh (l * (x : ℂ))).scomp x (hlin x)
    exact this.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hp1 : ∀ x : ℝ, HasDerivAt φ (deriv φ x) x := fun x => (hd1 x).hasDerivAt
  have hp2 : ∀ x : ℝ, HasDerivAt (deriv φ) (deriv (deriv φ) x) x := fun x => (hdd x).hasDerivAt
  have hV := const_of_hasDeriv_zero
    (fun x => deriv φ x * Complex.cosh (l * (x : ℂ)) - l * φ x * Complex.sinh (l * (x : ℂ)))
    (fun x => (deriv (deriv φ) x - l ^ 2 * φ x) * Complex.cosh (l * (x : ℂ)))
    (by
      intro x
      have := ((hp2 x).mul (hch x)).sub (((hp1 x).const_mul l).mul (hsh x))
      exact this.congr_deriv (by ring))
    (by intro x hx; rw [hode x hx]; ring)
  have hW := const_of_hasDeriv_zero
    (fun x => deriv φ x * Complex.sinh (l * (x : ℂ)) - l * φ x * Complex.cosh (l * (x : ℂ)))
    (fun x => (deriv (deriv φ) x - l ^ 2 * φ x) * Complex.sinh (l * (x : ℂ)))
    (by
      intro x
      have := ((hp2 x).mul (hsh x)).sub (((hp1 x).const_mul l).mul (hch x))
      exact this.congr_deriv (by ring))
    (by intro x hx; rw [hode x hx]; ring)
  intro x hx
  have hV0 := hV x hx
  have hW0 := hW x hx
  simp only [Complex.ofReal_zero, mul_zero, Complex.cosh_zero, Complex.sinh_zero, mul_one,
    hφ.left, sub_zero, zero_mul] at hV0 hW0
  have hsq := Complex.cosh_sq (l * (x : ℂ))
  constructor
  · linear_combination (Complex.cosh (l * (x : ℂ))) * hV0 - (Complex.sinh (l * (x : ℂ))) * hW0
      - (deriv φ x) * hsq
  · linear_combination (Complex.sinh (l * (x : ℂ))) * hV0 - (Complex.cosh (l * (x : ℂ))) * hW0
      - (l * φ x) * hsq

theorem sinh_lx_ne_zero (l : ℂ) (hl : l ≠ 0) :
    Complex.sinh (l * ((1 / (‖l‖ + 1) : ℝ) : ℂ)) ≠ 0 := by
  intro h0
  have hn : 0 < ‖l‖ := norm_pos_iff.mpr hl
  have hx : 0 < 1 / (‖l‖ + 1) := by positivity
  have hs : Complex.sin ((l * ((1 / (‖l‖ + 1) : ℝ) : ℂ)) * Complex.I) = 0 := by
    rw [Complex.sin_mul_I, h0, zero_mul]
  obtain ⟨n, hn'⟩ := Complex.sin_eq_zero_iff.mp hs
  have hnorm : ‖(l * ((1 / (‖l‖ + 1) : ℝ) : ℂ)) * Complex.I‖ = ‖l‖ / (‖l‖ + 1) := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hx.le]
    field_simp
  rw [hn'] at hnorm
  have h1 : ‖l‖ / (‖l‖ + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h2 : ‖((n : ℂ) * (Real.pi : ℂ))‖ = |(n : ℝ)| * Real.pi := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2] at hnorm
  have hn0 : n = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
      have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
      simpa using this
    nlinarith [Real.pi_gt_three]
  have h3 : l * ((1 / (‖l‖ + 1) : ℝ) : ℂ) * Complex.I = 0 := by rw [hn', hn0]; simp
  have h4 : ((1 / (‖l‖ + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  exact (mul_ne_zero (mul_ne_zero hl h4) Complex.I_ne_zero) h3

theorem eq16_characteristic_equation (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hε : 0 < ε)
    (ω : ℂ) (hω : ω ≠ -(a : ℂ)) :
    ω ∈ delaySpectrum a k ε ↔ h a k ε ω = 0 := by
  have hl : (a : ℂ) + ω ≠ 0 := fun h0 => hω (by linear_combination h0)
  have hexp : Complex.exp ((a : ℂ) + ω) / 2 ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) two_ne_zero
  have hkey := key_identity a k ε ω
  constructor
  · rintro ⟨φ, hφ, x₁, hx₁, hφx₁⟩
    have hexpl := eig_explicit a k ε ω φ hφ
    have hc : deriv φ 0 ≠ 0 := by
      intro hc0
      have := (hexpl x₁ hx₁).2
      rw [hc0, zero_mul] at this
      exact hφx₁ ((mul_eq_zero.mp this).resolve_left hl)
    obtain ⟨d1, e1⟩ := hexpl 1 ⟨zero_le_one, le_rfl⟩
    simp only [Complex.ofReal_one, mul_one] at d1 e1
    have hb := hφ.right
    have : deriv φ 0 * (Complex.exp ((a : ℂ) + ω) / 2 * h a k ε ω) = 0 := by
      rw [← hkey]
      linear_combination ((a : ℂ) + ω) * hb - ((a : ℂ) + ω) * d1
        - ((k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω)) * e1
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hc
    · exact (mul_eq_zero.mp h1).resolve_left hexp
  · intro hh
    set l : ℂ := (a : ℂ) + ω with hl'
    have hlin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => l * (x : ℂ)) l x := by
      intro x
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul l
    have hsh : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.sinh (l * (x : ℂ)))
        (l * Complex.cosh (l * (x : ℂ))) x := fun x => by
      have := (Complex.hasDerivAt_sinh (l * (x : ℂ))).scomp x (hlin x)
      exact this.congr_deriv (by simp [smul_eq_mul])
    have hch : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.cosh (l * (x : ℂ)))
        (l * Complex.sinh (l * (x : ℂ))) x := fun x => by
      have := (Complex.hasDerivAt_cosh (l * (x : ℂ))).scomp x (hlin x)
      exact this.congr_deriv (by simp [smul_eq_mul])
    have hd1 : deriv (fun x : ℝ => Complex.sinh (l * (x : ℂ))) = fun x : ℝ => l * Complex.cosh (l * (x : ℂ)) :=
      funext fun x => (hsh x).deriv
    have hd2 : deriv (deriv (fun x : ℝ => Complex.sinh (l * (x : ℂ))))
        = fun x : ℝ => l * (l * Complex.sinh (l * (x : ℂ))) := by
      rw [hd1]; exact funext fun x => ((hch x).const_mul l).deriv
    refine ⟨fun x : ℝ => Complex.sinh (l * (x : ℂ)), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · -- ContDiff
      have h0 : ContDiff ℝ 2 (fun x : ℝ => l * (x : ℂ)) :=
        contDiff_const.mul Complex.ofRealCLM.contDiff
      exact (Complex.contDiff_sinh.restrict_scalars ℝ).comp h0
    · intro x _
      rw [hd2]; ring
    · simp
    · rw [hd1]
      have hh' : l * Complex.cosh l + (k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * Complex.sinh l = 0 := by
        rw [hkey, hh, mul_zero]
      simp only [Complex.ofReal_one, mul_one]
      linear_combination hh'
    · refine ⟨1 / (‖l‖ + 1), ⟨by positivity, ?_⟩, sinh_lx_ne_zero l hl⟩
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg l]

theorem a_pos_of_lt_threshold (a k : ℝ) (ha : 0 ≤ a) (hk : 0 < k)
    (hkK : k < (1 - K a) / (1 + K a)) : 0 < a := by
  have hK0 := K_pos a
  have hk1 : k * (1 + K a) < 1 - K a := by rwa [lt_div_iff₀ (by positivity)] at hkK
  by_contra hcon
  push Not at hcon
  have h0 : a = 0 := le_antisymm hcon ha
  have : K a = 1 := by simp [K, h0]
  have : 0 < k * (1 + K a) := by positivity
  linarith

theorem basic_ineq (a k ε β₀ : ℝ) (hk : 0 ≤ k) (hε : 0 < ε) (hβ : 0 < β₀) (ha : 0 ≤ a)
    (ω : ℂ) (hre : -β₀ ≤ ω.re) (hω : h a k ε ω = 0) :
    ‖ω + (a : ℂ)‖ * (1 - K a * Real.exp (2 * β₀))
      ≤ ‖ω‖ * (k * Real.exp (ε * β₀) * (1 + K a * Real.exp (2 * β₀))) := by
  have hK0 := K_pos a
  set Q := K a * Real.exp (2 * β₀) with hQdef
  set E := Complex.exp (-2 * ω) with hE
  have hEn : ‖E‖ ≤ Real.exp (2 * β₀) := by
    rw [hE, Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; linarith
  have hqn : ‖(K a : ℂ) * E‖ ≤ Q := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hK0.le]
    exact mul_le_mul_of_nonneg_left hEn hK0.le
  have hFn : ‖Complex.exp (-(ε : ℂ) * ω)‖ ≤ Real.exp (ε * β₀) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; nlinarith
  have heq : (ω + a) * (1 + (K a : ℂ) * E)
      = -(ω * (k : ℂ) * Complex.exp (-(ε : ℂ) * ω) * (1 - (K a : ℂ) * E)) := by
    unfold h f at hω; rw [← hE] at hω; linear_combination hω
  have n1 : 1 - Q ≤ ‖1 + (K a : ℂ) * E‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-((K a : ℂ) * E))
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  have n2 : ‖1 - (K a : ℂ) * E‖ ≤ 1 + Q := by
    calc _ ≤ ‖(1 : ℂ)‖ + ‖(K a : ℂ) * E‖ := norm_sub_le _ _
      _ ≤ 1 + Q := by rw [norm_one]; linarith
  have hkn : ‖(k : ℂ)‖ = k := by rw [Complex.norm_real, Real.norm_of_nonneg hk]
  calc ‖ω + (a : ℂ)‖ * (1 - Q) ≤ ‖ω + (a : ℂ)‖ * ‖1 + (K a : ℂ) * E‖ :=
        mul_le_mul_of_nonneg_left n1 (norm_nonneg _)
    _ = ‖(ω + a) * (1 + (K a : ℂ) * E)‖ := (norm_mul _ _).symm
    _ = ‖ω‖ * k * ‖Complex.exp (-(ε : ℂ) * ω)‖ * ‖1 - (K a : ℂ) * E‖ := by
        rw [heq, norm_neg, norm_mul, norm_mul, norm_mul, hkn]
    _ ≤ ‖ω‖ * k * Real.exp (ε * β₀) * (1 + Q) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hFn (by positivity)) n2 (norm_nonneg _)
          (by positivity)
    _ = _ := by ring

theorem no_accumulation_imaginary_axis (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 < k)
    (hkK : k < (1 - K a) / (1 + K a)) (hε : 0 < ε) :
    ∃ β > (0 : ℝ), ∀ ω : ℂ, h a k ε ω = 0 → ω.re ≤ -β := by
  have hK0 := K_pos a
  have hk1 : k * (1 + K a) < 1 - K a := by rwa [lt_div_iff₀ (by positivity)] at hkK
  have hapos := a_pos_of_lt_threshold a k ha hk hkK
  obtain ⟨_, hhc, _, hdh, hpos⟩ := f_h_regular a k ha hk.le
  set φ : ℝ → ℝ := fun β => (1 - K a * Real.exp (2 * β))
    - k * Real.exp (ε * β) * (1 + K a * Real.exp (2 * β)) with hφdef
  have hφc : Continuous φ := by simp only [hφdef]; fun_prop
  have hφ0 : 0 < φ 0 := by simp only [hφdef]; simp; linarith
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp
    (hφc.continuousAt.eventually (lt_mem_nhds hφ0))
  set β₀ : ℝ := δ / 2 with hβ₀def
  have hβ₀ : 0 < β₀ := by positivity
  have hφβ : 0 < φ β₀ := by
    apply hδ'
    rw [Real.dist_eq, sub_zero, abs_of_pos hβ₀]; linarith
  have hQ : K a * Real.exp (2 * β₀) < 1 := by
    have : 0 ≤ k * Real.exp (ε * β₀) * (1 + K a * Real.exp (2 * β₀)) := by positivity
    simp only [hφdef] at hφβ
    linarith
  set Q : ℝ := K a * Real.exp (2 * β₀) with hQdef
  set c : ℝ := k * Real.exp (ε * β₀) * (1 + Q) with hcdef
  have hφβ' : 0 < (1 - Q) - c := hφβ
  have hbasic := fun ω hre hω => basic_ineq a k ε β₀ hk.le hε hβ₀ ha ω hre hω
  have hh0 : h a k ε 0 ≠ 0 := by
    have : h a k ε 0 = (a : ℂ) * (1 + (K a : ℂ)) := by simp [h]
    rw [this]
    have : (0 : ℝ) < a * (1 + K a) := by positivity
    have h2 : ((a * (1 + K a) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    simpa using h2
  have hnoRHP : ∀ ω : ℂ, 0 ≤ ω.re → h a k ε ω ≠ 0 := by
    intro ω hre hω
    have hb := hbasic ω (by linarith) hω
    have hge : ‖ω‖ ≤ ‖ω + (a : ℂ)‖ := by
      have hsq : ‖ω‖ ^ 2 ≤ ‖ω + (a : ℂ)‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
          Complex.normSq_apply]
        simp
        nlinarith
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
    have h1Q : 0 < 1 - Q := by linarith
    have : ‖ω‖ * ((1 - Q) - c) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_right hge h1Q.le]
    have hω0 : ‖ω‖ ≤ 0 := by
      by_contra hcon; push Not at hcon
      nlinarith
    have : ω = 0 := norm_le_zero_iff.mp hω0
    exact hh0 (this ▸ hω)
  have hM : ∀ ω : ℂ, -β₀ ≤ ω.re → h a k ε ω = 0 → ‖ω‖ * ((1 - Q) - c) ≤ a * (1 - Q) := by
    intro ω hre hω
    have hb := hbasic ω hre hω
    have h1Q : 0 < 1 - Q := by linarith
    have hle : ‖ω‖ ≤ ‖ω + (a : ℂ)‖ + a := by
      have := norm_sub_le (ω + (a : ℂ)) (a : ℂ)
      rw [add_sub_cancel_right, Complex.norm_real, Real.norm_of_nonneg ha] at this
      exact this
    nlinarith [mul_le_mul_of_nonneg_right hle h1Q.le]
  set M : ℝ := a * (1 - Q) / ((1 - Q) - c) with hMdef
  set Z : Set ℂ := (closedBall (0 : ℂ) M ∩ {z | -β₀ ≤ z.re}) ∩ {z | h a k ε z = 0} with hZdef
  have hZc : IsCompact Z := by
    apply IsCompact.inter_right
    · exact (isCompact_closedBall 0 M).inter_right (isClosed_le continuous_const Complex.continuous_re)
    · exact isClosed_eq (hdh ε).continuous continuous_const
  have hmemZ : ∀ ω : ℂ, -β₀ ≤ ω.re → h a k ε ω = 0 → ω ∈ Z := by
    intro ω hre hω
    refine ⟨⟨?_, hre⟩, hω⟩
    rw [mem_closedBall, dist_zero_right, hMdef, le_div_iff₀ hφβ']
    exact hM ω hre hω
  by_cases hZ : Z.Nonempty
  · obtain ⟨ω', hω'Z, hmax⟩ := hZc.exists_isMaxOn hZ Complex.continuous_re.continuousOn
    have hneg : ω'.re < 0 := by
      by_contra hcon; push Not at hcon
      exact hnoRHP ω' hcon hω'Z.2
    refine ⟨min β₀ (-ω'.re), lt_min hβ₀ (by linarith), fun ω hω => ?_⟩
    by_cases hr : -β₀ ≤ ω.re
    · have := isMaxOn_iff.mp hmax ω (hmemZ ω hr hω)
      have h2 : min β₀ (-ω'.re) ≤ -ω'.re := min_le_right _ _
      linarith
    · push Not at hr
      have h2 : min β₀ (-ω'.re) ≤ β₀ := min_le_left _ _
      linarith
  · refine ⟨β₀, hβ₀, fun ω hω => ?_⟩
    by_contra hcon
    push Not at hcon
    exact hZ ⟨ω, hmemZ ω (by linarith) hω⟩

theorem solution (a k : ℝ) (ha : 0 ≤ a) (hk : 0 < k)
    (hkK : k < (1 - K a) / (1 + K a)) :
    ∀ ε > (0 : ℝ), ∃ β > (0 : ℝ), ∀ ω ∈ delaySpectrum a k ε, ω.re ≤ -β := by
  intro ε hε
  have hapos := a_pos_of_lt_threshold a k ha hk hkK
  obtain ⟨β, hβ, hβ'⟩ := no_accumulation_imaginary_axis a k ε ha hk hkK hε
  refine ⟨min β a, lt_min hβ hapos, fun ω hω => ?_⟩
  by_cases h0 : ω = -(a : ℂ)
  · rw [h0]; simp
  · have := hβ' ω ((eq16_characteristic_equation a k ε ha hk.le hε ω h0).mp hω)
    linarith [min_le_left β a]

end
