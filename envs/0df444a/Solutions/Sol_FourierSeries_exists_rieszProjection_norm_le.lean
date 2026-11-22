-- Prove2me | solution 1 for FourierSeries.exists_rieszProjection_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:44:20.802519+00:00
-- url     : https://prove2.me/submissions/70d63974-4379-4236-9af8-97ec7ff61597

import Mathlib

open MeasureTheory AddCircle ENNReal

set_option autoImplicit false

namespace Sol_FourierSeries_exists_rieszProjection_norm_le

open Complex Real

variable {T : ℝ} [hT : Fact (0 < T)]

lemma integral_comp_toCircle (h : ℂ → ℂ) :
    ∫ x : AddCircle T, h (toCircle x) ∂haarAddCircle = Real.circleAverage h 0 1 := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage T 0]
  have hT0 : T ≠ 0 := hT.out.ne'
  have h2 : (2 * π / T) ≠ 0 := by positivity
  have key : ∀ x : ℝ, ((toCircle (x : AddCircle T) : Circle) : ℂ) = circleMap 0 1 (2 * π / T * x) := by
    intro x
    rw [toCircle_apply_mk, Circle.coe_exp, circleMap]
    simp
  simp_rw [key]
  have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 0 + T)
    (fun u : ℝ => h (circleMap 0 1 u)) h2
  rw [this, Real.circleAverage]
  simp only [mul_zero, zero_add]
  have : 2 * π / T * T = 2 * π := by field_simp
  rw [this, smul_smul]
  congr 1
  field_simp

/-- the elementary inequality behind M. Riesz's theorem for `1 < p ≤ 2`. -/
lemma exists_trig_ineq (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ w : ℂ, 0 < w.re →
      ‖w‖ ^ p ≤ A * w.re ^ p - B * (w ^ (p : ℂ)).re := by
  set c0 := Real.cos (p * (π / 2)) with hc0def
  have hc0 : c0 < 0 := by
    apply Real.cos_neg_of_pi_div_two_lt_of_lt
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hcont : ContinuousAt (fun ψ : ℝ => Real.cos (p * ψ)) (π / 2) := by fun_prop
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hcont (-c0 / 2) (by linarith)
  set η := min δ (π / 2) with hη
  have hη0 : 0 < η := lt_min hδ (by positivity)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηπ : η ≤ π / 2 := min_le_right _ _
  have hsη : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη0 (by linarith [Real.pi_pos])
  set B := 2 / (-c0) with hB
  have hB0 : 0 < B := div_pos two_pos (neg_pos.mpr hc0)
  set A := (1 + B) / (Real.sin η) ^ p with hA
  have hA0 : 0 < A := by positivity
  refine ⟨A, B, hA0, hB0, fun w hw => ?_⟩
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  set r := ‖w‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr hw0
  set φ := Complex.arg w with hφ
  have habs : |φ| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have hre : w.re = r * Real.cos φ := (Complex.norm_mul_cos_arg w).symm
  have hcpow : (w ^ (p : ℂ)).re = r ^ p * Real.cos (p * φ) := by
    rw [Complex.cpow_def_of_ne_zero hw0, Complex.exp_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.log_re, Complex.log_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero]
    rw [Real.rpow_def_of_pos hr0, mul_comm (Real.log _) p, zero_add, mul_comm (Complex.arg w) p]
  -- reduce to |φ|
  set ψ := |φ| with hψ
  have hψ0 : 0 ≤ ψ := abs_nonneg _
  have hcosφ : Real.cos φ = Real.cos ψ := (Real.cos_abs φ).symm
  have hcospφ : Real.cos (p * φ) = Real.cos (p * ψ) := by
    rw [← Real.cos_abs (p * φ), abs_mul, abs_of_pos (by linarith : (0:ℝ) < p)]
  have hcosψ0 : 0 < Real.cos ψ := Real.cos_pos_of_mem_Ioo ⟨by linarith, habs⟩
  rw [hre, hcpow, hcosφ, hcospφ, Real.mul_rpow hr0.le hcosψ0.le]
  -- goal: r ^ p ≤ A * (r ^ p * cos ψ ^ p) - B * (r ^ p * cos (p * ψ))
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr0 p
  suffices h : 1 + B * Real.cos (p * ψ) ≤ A * Real.cos ψ ^ p by nlinarith
  by_cases hcase : π / 2 - η < ψ
  · have hd : dist ψ (π / 2) < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hδc hd
    rw [Real.dist_eq, abs_lt] at this
    have hlt : Real.cos (p * ψ) < c0 / 2 := by linarith [this.2]
    have h1 : 1 + B * Real.cos (p * ψ) ≤ 0 := by
      have : B * Real.cos (p * ψ) ≤ B * (c0 / 2) := by nlinarith
      have hc0ne : c0 ≠ 0 := hc0.ne
      have hBc : B * (c0 / 2) = -1 := by rw [hB]; field_simp [hc0ne]
      linarith
    have : 0 ≤ A * Real.cos ψ ^ p := by positivity
    linarith
  · push_neg at hcase
    have hcle : Real.sin η ≤ Real.cos ψ := by
      rw [← Real.cos_pi_div_two_sub]
      apply Real.cos_le_cos_of_nonneg_of_le_pi hψ0 (by linarith [Real.pi_pos]) hcase
    have hpow : Real.sin η ^ p ≤ Real.cos ψ ^ p :=
      Real.rpow_le_rpow hsη.le hcle (by linarith)
    have hsp : 0 < Real.sin η ^ p := Real.rpow_pos_of_pos hsη p
    have h1 : 1 + B * Real.cos (p * ψ) ≤ 1 + B := by
      have := Real.cos_le_one (p * ψ); nlinarith
    calc 1 + B * Real.cos (p * ψ) ≤ 1 + B := h1
      _ = A * Real.sin η ^ p := by rw [hA]; field_simp
      _ ≤ A * Real.cos ψ ^ p := by gcongr

/-- minimum principle for the real part of a polynomial on the closed unit disc. -/
lemma re_pos_of_sphere (Q : ℂ → ℂ) (hQ : Differentiable ℂ Q)
    (hpos : ∀ z : ℂ, ‖z‖ = 1 → 0 < (Q z).re) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → 0 < (Q z).re := by
  have hcomp : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ℂ) 1).Nonempty := ⟨1, by simp⟩
  obtain ⟨z0, hz0, hmin⟩ := hcomp.exists_isMinOn hne
    ((Complex.continuous_re.comp hQ.continuous).continuousOn)
  set m := (Q z0).re with hm
  have hm0 : 0 < m := hpos z0 (by simpa using hz0)
  intro z hz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (f := fun w => Complex.exp (-Q w))
    (U := Metric.ball (0 : ℂ) 1) Metric.isBounded_ball
    ((hQ.neg.cexp).diffContOnCl) (C := Real.exp (-m)) (by
      intro w hw
      rw [frontier_ball (0 : ℂ) one_ne_zero] at hw
      simp only [Complex.norm_exp, Complex.neg_re, Real.exp_le_exp, neg_le_neg_iff]
      exact hmin hw) (z := z) (by rw [closure_ball (0 : ℂ) one_ne_zero]; simpa using hz)
  simp only [Complex.norm_exp, Complex.neg_re, Real.exp_le_exp, neg_le_neg_iff] at hmax
  linarith

lemma continuous_toCircle_coe : Continuous (fun x : AddCircle T => ((toCircle x : Circle) : ℂ)) :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

lemma norm_toCircle_coe (x : AddCircle T) : ‖((toCircle x : Circle) : ℂ)‖ = 1 := Circle.norm_coe _

lemma integrable_cont {E : Type*} [NormedAddCommGroup E] {f : AddCircle T → E} (hf : Continuous f) :
    Integrable f (haarAddCircle (T := T)) :=
  integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

/-- M. Riesz's lemma for analytic polynomials with positive real part, `1 < p ≤ 2`. -/
lemma analytic_bound (p : ℝ) (hp : 1 < p) (hp2 : p ≤ 2) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Q : ℂ → ℂ), Differentiable ℂ Q → (Q 0).im = 0 →
      (∀ z : ℂ, ‖z‖ = 1 → 0 < (Q z).re) →
      ∫ x : AddCircle T, ‖Q (toCircle x)‖ ^ p ∂haarAddCircle ≤
        A * ∫ x : AddCircle T, (Q (toCircle x)).re ^ p ∂haarAddCircle := by
  obtain ⟨A, B, hA, hB, hineq⟩ := exists_trig_ineq p hp hp2
  refine ⟨A, hA, fun Q hQ hQ0 hpos => ?_⟩
  have hdisc := re_pos_of_sphere Q hQ hpos
  set G : ℂ → ℂ := fun z => Q z ^ (p : ℂ) with hG
  have hGd : ∀ z : ℂ, ‖z‖ ≤ 1 → DifferentiableAt ℂ G z := fun z hz =>
    (hQ z).cpow_const (Complex.mem_slitPlane_iff.mpr (Or.inl (hdisc z hz)))
  have hGcl : DiffContOnCl ℂ G (Metric.ball (0 : ℂ) |1|) := by
    rw [abs_one]
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    intro z hz
    exact (hGd z (by simpa using hz)).differentiableWithinAt
  have hmean : Real.circleAverage G 0 1 = G 0 := hGcl.circleAverage
  have hGcont : Continuous (fun x : AddCircle T => G (toCircle x)) := by
    have hcon : ContinuousOn G (Metric.closedBall 0 1) := fun z hz =>
      (hGd z (by simpa using hz)).continuousAt.continuousWithinAt
    exact hcon.comp_continuous continuous_toCircle_coe (fun x => by simp [norm_toCircle_coe])
  have hQcont : Continuous (fun x : AddCircle T => Q (toCircle x)) :=
    hQ.continuous.comp continuous_toCircle_coe
  have hint_G : Integrable (fun x : AddCircle T => G (toCircle x)) (haarAddCircle (T := T)) :=
    integrable_cont hGcont
  have hGre : ∫ x : AddCircle T, (G (toCircle x)).re ∂haarAddCircle = (G 0).re := by
    have h1 := integral_re hint_G
    simp only [RCLike.re_to_complex] at h1
    rw [h1, integral_comp_toCircle G, hmean]
  have hG0 : 0 ≤ (G 0).re := by
    have hq : Q 0 = ((Q 0).re : ℂ) := by
      apply Complex.ext <;> simp [hQ0]
    have hr : 0 ≤ (Q 0).re := (hdisc 0 (by simp)).le
    simp only [hG]
    rw [hq, ← Complex.ofReal_cpow hr, Complex.ofReal_re]
    exact Real.rpow_nonneg hr _
  have hc1 : Continuous (fun x : AddCircle T => ‖Q (toCircle x)‖ ^ p) :=
    hQcont.norm.rpow_const (fun _ => Or.inr (by linarith))
  have hc2 : Continuous (fun x : AddCircle T => (Q (toCircle x)).re ^ p) :=
    (Complex.continuous_re.comp hQcont).rpow_const (fun _ => Or.inr (by linarith))
  have hi1 := integrable_cont hc1
  have hi2 := integrable_cont hc2
  have hi3 : Integrable (fun x : AddCircle T => (G (toCircle x)).re) haarAddCircle :=
    integrable_cont (Complex.continuous_re.comp hGcont)
  calc ∫ x : AddCircle T, ‖Q (toCircle x)‖ ^ p ∂haarAddCircle
      ≤ ∫ x : AddCircle T, (A * (Q (toCircle x)).re ^ p - B * (G (toCircle x)).re) ∂haarAddCircle := by
        apply integral_mono hi1 ((hi2.const_mul A).sub (hi3.const_mul B))
        intro x
        exact hineq _ (hpos _ (norm_toCircle_coe x))
    _ = A * ∫ x : AddCircle T, (Q (toCircle x)).re ^ p ∂haarAddCircle -
          B * ∫ x : AddCircle T, (G (toCircle x)).re ∂haarAddCircle := by
        rw [integral_sub (hi2.const_mul A) (hi3.const_mul B), integral_const_mul, integral_const_mul]
    _ ≤ A * ∫ x : AddCircle T, (Q (toCircle x)).re ^ p ∂haarAddCircle := by
        rw [hGre]; nlinarith

/-! ### Trigonometric polynomials as finitely supported coefficient families -/

noncomputable def L : (ℤ →₀ ℂ) →ₗ[ℂ] C(AddCircle T, ℂ) :=
  Finsupp.linearCombination ℂ (fun n : ℤ => (fourier n : C(AddCircle T, ℂ)))

lemma L_apply (c : ℤ →₀ ℂ) (x : AddCircle T) :
    (L (T := T) c) x = ∑ n ∈ c.support, c n * fourier n x := by
  simp [L, Finsupp.linearCombination_apply, Finsupp.sum, ContinuousMap.coe_sum]

lemma L_single (n : ℤ) (a : ℂ) : L (T := T) (Finsupp.single n a) = a • fourier n := by
  simp [L]

noncomputable def P (c : ℤ →₀ ℂ) : ℤ →₀ ℂ := c.filter (fun n => 0 ≤ n)

lemma P_add (c d : ℤ →₀ ℂ) : P (c + d) = P c + P d := Finsupp.filter_add
lemma P_sub (c d : ℤ →₀ ℂ) : P (c - d) = P c - P d := Finsupp.filter_sub _ _ _
lemma P_smul (a : ℂ) (c : ℤ →₀ ℂ) : P (a • c) = a • P c := Finsupp.filter_smul

noncomputable def cstar (c : ℤ →₀ ℂ) : ℤ →₀ ℂ :=
  Finsupp.onFinset (c.support.image (fun n => -n)) (fun n => (starRingEnd ℂ) (c (-n))) (by
    intro n hn
    simp only [Finset.mem_image, Finsupp.mem_support_iff]
    refine ⟨-n, ?_, neg_neg n⟩
    intro h; apply hn; simp [h])

@[simp] lemma cstar_apply (c : ℤ →₀ ℂ) (n : ℤ) : cstar c n = (starRingEnd ℂ) (c (-n)) :=
  Finsupp.onFinset_apply

lemma cstar_add (c d : ℤ →₀ ℂ) : cstar (c + d) = cstar c + cstar d := by ext n; simp

lemma cstar_single (n : ℤ) (a : ℂ) :
    cstar (Finsupp.single n a) = Finsupp.single (-n) (starRingEnd ℂ a) := by
  ext m
  simp only [cstar_apply, Finsupp.single_apply]
  by_cases h : n = -m
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), map_zero]

lemma L_cstar (c : ℤ →₀ ℂ) (x : AddCircle T) :
    L (T := T) (cstar c) x = starRingEnd ℂ (L c x) := by
  induction c using Finsupp.induction_linear with
  | zero =>
    have : cstar (0 : ℤ →₀ ℂ) = 0 := by ext n; simp
    rw [this]; simp
  | add f g hf hg =>
    rw [cstar_add, map_add, ContinuousMap.add_apply, hf, hg, map_add, ContinuousMap.add_apply, map_add]
  | single n a =>
    rw [cstar_single, L_single, L_single]
    simp [fourier_neg]

def IsSA (c : ℤ →₀ ℂ) : Prop := cstar c = c

lemma IsSA.apply {c : ℤ →₀ ℂ} (h : IsSA c) (n : ℤ) : (starRingEnd ℂ) (c (-n)) = c n := by
  have := congrArg (fun d => d n) h
  simpa using this

lemma IsSA.L_real {c : ℤ →₀ ℂ} (h : IsSA c) (x : AddCircle T) :
    L (T := T) c x = ((L (T := T) c x).re : ℂ) := by
  have h1 : starRingEnd ℂ (L (T := T) c x) = L c x := by rw [← L_cstar, h]
  exact (Complex.conj_eq_iff_re.mp h1).symm

noncomputable def rePart (c : ℤ →₀ ℂ) : ℤ →₀ ℂ := (1 / 2 : ℂ) • (c + cstar c)
noncomputable def imPart (c : ℤ →₀ ℂ) : ℤ →₀ ℂ := (-Complex.I / 2) • (c - cstar c)

lemma rePart_SA (c : ℤ →₀ ℂ) : IsSA (rePart c) := by
  unfold IsSA rePart; ext n; simp [add_comm, map_ofNat]

lemma imPart_SA (c : ℤ →₀ ℂ) : IsSA (imPart c) := by
  unfold IsSA imPart; ext n; simp [map_ofNat]; ring

lemma re_add_im (c : ℤ →₀ ℂ) : rePart c + Complex.I • imPart c = c := by
  unfold rePart imPart; ext n
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul]
  ring_nf; rw [Complex.I_sq]; ring

lemma L_rePart (c : ℤ →₀ ℂ) (x : AddCircle T) :
    L (T := T) (rePart c) x = ((L (T := T) c x).re : ℂ) := by
  unfold rePart
  rw [map_smul, map_add, ContinuousMap.smul_apply, ContinuousMap.add_apply, L_cstar,
    Complex.add_conj]
  simp

lemma L_imPart (c : ℤ →₀ ℂ) (x : AddCircle T) :
    L (T := T) (imPart c) x = ((L (T := T) c x).im : ℂ) := by
  unfold imPart
  rw [map_smul, map_sub, ContinuousMap.smul_apply, ContinuousMap.sub_apply, L_cstar,
    Complex.sub_conj, smul_eq_mul]
  ring_nf; rw [Complex.I_sq]; push_cast; ring

lemma integrable_contMap (f : C(AddCircle T, ℂ)) : Integrable f (haarAddCircle (T := T)) :=
  integrable_cont f.continuous

lemma fourierCoeff_L (c : ℤ →₀ ℂ) (m : ℤ) : fourierCoeff (L (T := T) c) m = c m := by
  induction c using Finsupp.induction_linear with
  | zero => simp [fourierCoeff]
  | add f g hf hg =>
    rw [map_add, ContinuousMap.coe_add, fourierCoeff.add (integrable_contMap _) (integrable_contMap _),
      Pi.add_apply, hf, hg, Finsupp.add_apply]
  | single n a =>
    rw [L_single, ContinuousMap.coe_smul, fourierCoeff.const_smul, fourierCoeff_fourier]
    simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

lemma integral_L (c : ℤ →₀ ℂ) : ∫ x, L (T := T) c x ∂haarAddCircle = c 0 := by
  have := fourierCoeff_L (T := T) c 0
  rw [fourierCoeff] at this
  simpa [fourier_zero] using this

/-! ### `L^p` norms of continuous functions -/

section Norms

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

noncomputable def N (f : C(AddCircle T, ℂ)) : ℝ :=
  ‖ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ f‖

lemma N_nonneg (f : C(AddCircle T, ℂ)) : 0 ≤ N p f := norm_nonneg _

lemma N_add_le (f g : C(AddCircle T, ℂ)) : N p (f + g) ≤ N p f + N p g := by
  unfold N; rw [map_add]; exact norm_add_le _ _

lemma N_sub_le (f g : C(AddCircle T, ℂ)) : N p (f - g) ≤ N p f + N p g := by
  unfold N; rw [map_sub]; exact norm_sub_le _ _

lemma N_smul (a : ℂ) (f : C(AddCircle T, ℂ)) : N p (a • f) = ‖a‖ * N p f := by
  unfold N; rw [map_smul, norm_smul]

lemma N_mono (f g : C(AddCircle T, ℂ)) (h : ∀ x, ‖f x‖ ≤ ‖g x‖) : N p f ≤ N p g := by
  unfold N
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := p) (μ := haarAddCircle (T := T)) (𝕜 := ℂ) f,
    ContinuousMap.coeFn_toLp (E := ℂ) (p := p) (μ := haarAddCircle (T := T)) (𝕜 := ℂ) g] with x hx hy
  rw [hx, hy]; exact h x

lemma N_le_of_bound (f : C(AddCircle T, ℂ)) (r : ℝ) (hr : 0 ≤ r) (h : ∀ x, ‖f x‖ ≤ r) :
    N p f ≤ r := by
  unfold N
  have h1 := (ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ).le_opNorm f
  have h2 := ContinuousMap.toLp_norm_le (E := ℂ) (p := p) (haarAddCircle (T := T)) (𝕜 := ℂ)
  have h3 : ‖f‖ ≤ r := (ContinuousMap.norm_le f hr).mpr h
  have h4 : (measureUnivNNReal (haarAddCircle (T := T)) : ℝ) ^ p.toReal⁻¹ = 1 := by
    simp [measureUnivNNReal]
  have h2' : ‖(ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ)‖ ≤ 1 := by
    rw [← h4]; exact h2
  calc _ ≤ _ := h1
    _ ≤ 1 * ‖f‖ := by gcongr
    _ ≤ r := by linarith

lemma norm_integral_le_N (f : C(AddCircle T, ℂ)) :
    ‖∫ x, f x ∂haarAddCircle‖ ≤ N p f := by
  unfold N
  set F := ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ f
  have hF : (F : AddCircle T → ℂ) =ᵐ[haarAddCircle] f := ContinuousMap.coeFn_toLp _ f
  rw [← integral_congr_ae hF]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable F), ← eLpNorm_one_eq_lintegral_enorm,
    Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top F)
    (eLpNorm_le_eLpNorm_of_exponent_le (Fact.out : 1 ≤ p) (Lp.aestronglyMeasurable F))

lemma N_eq_integral (hp : p ≠ ∞) (f : C(AddCircle T, ℂ)) :
    N p f = (∫ x, ‖f x‖ ^ p.toReal ∂haarAddCircle) ^ (1 / p.toReal) := by
  unfold N
  have hp0 : p ≠ 0 := by
    have : (1 : ℝ≥0∞) ≤ p := Fact.out
    intro h; rw [h] at this; simp at this
  rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ f),
    (ContinuousMap.memLp (μ := haarAddCircle (T := T)) (p := p) ℂ f).eLpNorm_eq_integral_rpow_norm hp0 hp,
    ENNReal.toReal_ofReal, one_div]
  apply Real.rpow_nonneg
  exact integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)

end Norms

lemma exists_toCircle (z : ℂ) (hz : ‖z‖ = 1) : ∃ x : AddCircle T, ((toCircle x : Circle) : ℂ) = z := by
  refine ⟨((T * Complex.arg z / (2 * π) : ℝ) : AddCircle T), ?_⟩
  rw [toCircle_apply_mk, Circle.coe_exp]
  have hT0 : T ≠ 0 := hT.out.ne'
  have : 2 * π / T * (T * Complex.arg z / (2 * π)) = Complex.arg z := by field_simp
  rw [this]
  have := Complex.norm_mul_exp_arg_mul_I z
  rw [hz] at this; simpa using this

lemma fourier_eq_pow (n : ℕ) (x : AddCircle T) :
    fourier (n : ℤ) x = ((toCircle x : Circle) : ℂ) ^ n := by
  rw [fourier_apply, natCast_zsmul, toCircle_nsmul, Circle.coe_pow]

/-- the positive case: `d` self-adjoint with `L d > 0`, `1 < p ≤ 2`. -/
lemma pos_case (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp2 : p ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℤ →₀ ℂ, IsSA d → (∀ x, 0 < (L (T := T) d x).re) →
      N p (L (T := T) (P d)) ≤ K * N p (L (T := T) d) := by
  have hptop : p ≠ ∞ := ne_top_of_le_ne_top (by simp) hp2
  set r := p.toReal with hr
  have hr1 : 1 < r := by
    rw [hr]; have := ENNReal.toReal_strict_mono hptop hp; simpa using this
  have hr2 : r ≤ 2 := by
    rw [hr]; have := ENNReal.toReal_mono (by simp) hp2; simpa using this
  obtain ⟨A, hA, hbound⟩ := analytic_bound (T := T) r hr1 hr2
  refine ⟨A ^ (1 / r), Real.rpow_nonneg hA.le _, fun d hSA hpos => ?_⟩
  set f : ℤ →₀ ℂ := (2 : ℂ) • P d - Finsupp.single 0 (d 0) with hfdef
  have hfneg : ∀ n : ℤ, n < 0 → f n = 0 := by
    intro n hn
    simp [hfdef, P, Finsupp.filter_apply, Finsupp.single_apply, not_le.mpr hn, hn.ne]
  have hf0 : f 0 = d 0 := by
    simp [hfdef, P, Finsupp.filter_apply]; ring
  have hd0 : (starRingEnd ℂ) (d 0) = d 0 := by simpa using hSA.apply 0
  -- the analytic polynomial
  set Q : ℂ → ℂ := fun z => ∑ n ∈ f.support, f n * z ^ n.toNat with hQdef
  have hQ : Differentiable ℂ Q := by
    rw [hQdef]
    exact Differentiable.fun_sum (fun n _ => (differentiable_const _).mul (differentiable_pow _))
  have hQe : ∀ x : AddCircle T, Q (toCircle x) = L (T := T) f x := by
    intro x
    rw [L_apply, hQdef]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 ≤ n := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hn) (hfneg n (not_le.mp h))
    congr 1
    rw [← fourier_eq_pow, Int.toNat_of_nonneg hn0]
  have hQ0 : Q 0 = d 0 := by
    rw [hQdef]
    simp only
    rw [Finset.sum_eq_single 0]
    · simp [hf0]
    · intro n hn hn0
      have hn0' : 0 ≤ n := by
        by_contra h
        exact (Finsupp.mem_support_iff.mp hn) (hfneg n (not_le.mp h))
      have : n.toNat ≠ 0 := by omega
      simp [zero_pow this]
    · intro h
      rw [Finsupp.notMem_support_iff] at h
      simp [h]
  have hQ0im : (Q 0).im = 0 := by
    rw [hQ0]; exact Complex.conj_eq_iff_im.mp hd0
  -- real part of `L f` is `L d`
  have hsum : f + cstar f = (2 : ℂ) • d := by
    ext n
    have h1 : (starRingEnd ℂ) (d (-n)) = d n := hSA.apply n
    simp only [hfdef, P, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, cstar_apply, Finsupp.filter_apply, Finsupp.single_apply,
      smul_eq_mul, map_sub, map_mul, map_ofNat]
    rcases lt_trichotomy n 0 with h | h | h
    · simp [not_le.mpr h, h.le, h.ne, h.ne', h1]; try ring
    · subst h; simp [hd0]; try ring
    · simp [h.le, h.ne, h.ne', not_le.mpr h]
  have hre : ∀ x, (L (T := T) f x).re = (L (T := T) d x).re := by
    intro x
    have h1 := congrArg (fun c => L (T := T) c x) hsum
    simp only [map_add, map_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply, L_cstar,
      Complex.add_conj, smul_eq_mul] at h1
    have h2 := congrArg Complex.re h1
    simp at h2
    exact h2
  have hposQ : ∀ z : ℂ, ‖z‖ = 1 → 0 < (Q z).re := by
    intro z hz
    obtain ⟨x, rfl⟩ := exists_toCircle (T := T) z hz
    rw [hQe, hre]; exact hpos x
  have hb := hbound Q hQ hQ0im hposQ
  simp only [hQe, hre] at hb
  have hnormd : ∀ x, ‖L (T := T) d x‖ = (L (T := T) d x).re := by
    intro x
    rw [hSA.L_real x, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos x)]
    simp
  simp only [← hnormd] at hb
  -- `N p (L f) ≤ A ^ (1/r) * N p (L d)`
  have hNf : N p (L (T := T) f) ≤ A ^ (1 / r) * N p (L (T := T) d) := by
    rw [N_eq_integral p hptop, N_eq_integral p hptop, ← hr]
    rw [← Real.mul_rpow hA.le (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))]
    apply Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hb
    positivity
  -- `P d = (1/2) (f + single 0 (d 0))`
  have hPd : P d = (1 / 2 : ℂ) • (f + Finsupp.single 0 (d 0)) := by
    rw [hfdef, sub_add_cancel, smul_smul]; norm_num
  have hd0N : ‖d 0‖ ≤ N p (L (T := T) f) := by
    rw [← hf0, ← integral_L (T := T)]; exact norm_integral_le_N p _
  have hsingle : N p (L (T := T) (Finsupp.single 0 (d 0))) ≤ ‖d 0‖ := by
    rw [L_single, N_smul]
    have : N p (fourier (T := T) 0) ≤ 1 := N_le_of_bound p _ 1 zero_le_one (fun x => by simp [fourier_zero])
    have := mul_le_mul_of_nonneg_left this (norm_nonneg (d 0))
    linarith
  calc N p (L (T := T) (P d)) = ‖(1 / 2 : ℂ)‖ * N p (L (T := T) f + L (T := T) (Finsupp.single 0 (d 0))) := by
        rw [hPd, map_smul, N_smul, map_add]
    _ ≤ ‖(1 / 2 : ℂ)‖ * (N p (L (T := T) f) + N p (L (T := T) (Finsupp.single 0 (d 0)))) := by
        gcongr; exact N_add_le p _ _
    _ ≤ (1 / 2) * (N p (L (T := T) f) + N p (L (T := T) f)) := by
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        rw [this]; gcongr; linarith
    _ = N p (L (T := T) f) := by ring
    _ ≤ A ^ (1 / r) * N p (L (T := T) d) := hNf

lemma cstar_sub (c d : ℤ →₀ ℂ) : cstar (c - d) = cstar c - cstar d := by ext n; simp

lemma L_eq_sum (c : ℤ →₀ ℂ) : L (T := T) c = c.sum (fun n a => a • fourier n) := by
  simp [L, Finsupp.linearCombination_apply]

lemma approx_re (g : C(AddCircle T, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℤ →₀ ℂ, IsSA q ∧ ∀ x, |(L (T := T) q x).re - (g x).re| < ε := by
  have hmem : g ∈ (Submodule.span ℂ (Set.range (fourier (T := T)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨y, hy, hdist⟩ := hmem ε hε
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp (SetLike.mem_coe.mp hy)
  refine ⟨rePart c, rePart_SA c, fun x => ?_⟩
  rw [L_rePart, Complex.ofReal_re]
  have h1 : L (T := T) c = y := by rw [L_eq_sum, hc]
  have h2 : ‖L (T := T) c x - g x‖ < ε := by
    rw [h1]
    calc ‖y x - g x‖ = ‖(y - g) x‖ := rfl
      _ ≤ ‖y - g‖ := ContinuousMap.norm_coe_le_norm _ x
      _ = dist g y := by rw [dist_comm, dist_eq_norm]
      _ < ε := hdist
  calc |(L (T := T) c x).re - (g x).re| = |(L (T := T) c x - g x).re| := by rw [Complex.sub_re]
    _ ≤ ‖L (T := T) c x - g x‖ := Complex.abs_re_le_norm _
    _ < ε := h2

/-- the real case, `1 < p ≤ 2`. -/
lemma real_case (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp2 : p ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℤ →₀ ℂ, IsSA a →
      N p (L (T := T) (P a)) ≤ K * N p (L (T := T) a) := by
  obtain ⟨K0, hK0, hpos⟩ := pos_case (T := T) p hp hp2
  refine ⟨2 * K0, by positivity, fun a ha => ?_⟩
  set u : AddCircle T → ℝ := fun x => (L (T := T) a x).re with hu
  have hucont : Continuous u := Complex.continuous_re.comp (L (T := T) a).continuous
  let up : C(AddCircle T, ℂ) := ⟨fun x => ((max (u x) 0 : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (hucont.max continuous_const)⟩
  let um : C(AddCircle T, ℂ) := ⟨fun x => ((max (-u x) 0 : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (hucont.neg.max continuous_const)⟩
  have hup : N p up ≤ N p (L (T := T) a) := by
    apply N_mono; intro x
    show ‖((max (u x) 0 : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |max (u x) 0| ≤ |u x| := by
          rcases le_total (u x) 0 with h | h
          · rw [max_eq_right h]; simp
          · rw [max_eq_left h]
      _ ≤ _ := Complex.abs_re_le_norm _
  have hum : N p um ≤ N p (L (T := T) a) := by
    apply N_mono; intro x
    show ‖((max (-u x) 0 : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |max (-u x) 0| ≤ |u x| := by
          rcases le_total (-u x) 0 with h | h
          · rw [max_eq_right h]; simp
          · rw [max_eq_left h, abs_neg]
      _ ≤ _ := Complex.abs_re_le_norm _
  have key : ∀ ε : ℝ, 0 < ε → N p (L (T := T) (P a)) ≤ 2 * K0 * N p (L (T := T) a) + 6 * K0 * ε := by
    intro ε hε
    obtain ⟨q, hq, hqa⟩ := approx_re (T := T) up ε hε
    have hqa' : ∀ x, |(L (T := T) q x).re - max (u x) 0| < ε := fun x => by
      simpa [up] using hqa x
    set d1 : ℤ →₀ ℂ := q + Finsupp.single 0 ((2 * ε : ℝ) : ℂ) with hd1
    set d2 : ℤ →₀ ℂ := d1 - a with hd2
    have hd1SA : IsSA d1 := by
      unfold IsSA; rw [hd1, cstar_add, cstar_single, hq, neg_zero, Complex.conj_ofReal]
    have hd2SA : IsSA d2 := by
      unfold IsSA; rw [hd2, cstar_sub, hd1SA, ha]
    have hLd1 : ∀ x, (L (T := T) d1 x).re = (L (T := T) q x).re + 2 * ε := by
      intro x
      rw [hd1, map_add, ContinuousMap.add_apply, L_single, ContinuousMap.smul_apply, fourier_zero,
        smul_eq_mul, mul_one, Complex.add_re, Complex.ofReal_re]
    have hLd2 : ∀ x, (L (T := T) d2 x).re = (L (T := T) q x).re + 2 * ε - u x := by
      intro x; rw [hd2, map_sub, ContinuousMap.sub_apply, Complex.sub_re, hLd1]
    have hpos1 : ∀ x, 0 < (L (T := T) d1 x).re := by
      intro x; rw [hLd1]
      have := (abs_lt.mp (hqa' x)).1
      have : 0 ≤ max (u x) 0 := le_max_right _ _
      linarith
    have hpos2 : ∀ x, 0 < (L (T := T) d2 x).re := by
      intro x; rw [hLd2]
      have := (abs_lt.mp (hqa' x)).1
      have : u x ≤ max (u x) 0 := le_max_left _ _
      linarith
    have hPa : P a = P d1 - P d2 := by rw [← P_sub, hd2, _root_.sub_sub_cancel]
    have hN1 : N p (L (T := T) d1) ≤ N p up + 3 * ε := by
      have : L (T := T) d1 = up + (L (T := T) d1 - up) := by abel
      rw [this]
      refine (N_add_le p _ _).trans ?_
      gcongr
      apply N_le_of_bound p _ _ (by linarith)
      intro x
      rw [ContinuousMap.sub_apply, hd1SA.L_real x, hLd1]
      show ‖(((L (T := T) q x).re + 2 * ε : ℝ) : ℂ) - ((max (u x) 0 : ℝ) : ℂ)‖ ≤ 3 * ε
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have := abs_lt.mp (hqa' x)
      rw [abs_le]; constructor <;> linarith
    have hN2 : N p (L (T := T) d2) ≤ N p um + 3 * ε := by
      have : L (T := T) d2 = um + (L (T := T) d2 - um) := by abel
      rw [this]
      refine (N_add_le p _ _).trans ?_
      gcongr
      apply N_le_of_bound p _ _ (by linarith)
      intro x
      rw [ContinuousMap.sub_apply, hd2SA.L_real x, hLd2]
      show ‖(((L (T := T) q x).re + 2 * ε - u x : ℝ) : ℂ) - ((max (-u x) 0 : ℝ) : ℂ)‖ ≤ 3 * ε
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have := abs_lt.mp (hqa' x)
      rw [abs_le]
      rcases le_total (u x) 0 with h | h
      · rw [max_eq_right h] at this; rw [max_eq_left (by linarith)]; constructor <;> linarith
      · rw [max_eq_left h] at this; rw [max_eq_right (by linarith)]; constructor <;> linarith
    calc N p (L (T := T) (P a)) = N p (L (T := T) (P d1) - L (T := T) (P d2)) := by rw [hPa, map_sub]
      _ ≤ N p (L (T := T) (P d1)) + N p (L (T := T) (P d2)) := N_sub_le p _ _
      _ ≤ K0 * N p (L (T := T) d1) + K0 * N p (L (T := T) d2) :=
          add_le_add (hpos d1 hd1SA hpos1) (hpos d2 hd2SA hpos2)
      _ ≤ K0 * (N p up + 3 * ε) + K0 * (N p um + 3 * ε) := by gcongr
      _ ≤ K0 * (N p (L (T := T) a) + 3 * ε) + K0 * (N p (L (T := T) a) + 3 * ε) := by gcongr
      _ = 2 * K0 * N p (L (T := T) a) + 6 * K0 * ε := by ring
  apply _root_.le_of_forall_pos_le_add
  intro δ hδ
  have h6 : 0 < 6 * K0 + 1 := by linarith
  have := key (δ / (6 * K0 + 1)) (div_pos hδ h6)
  have h7 : 6 * K0 * (δ / (6 * K0 + 1)) ≤ δ := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ h6]; nlinarith
  linarith

/-- the case `1 < p ≤ 2` for arbitrary trigonometric polynomials. -/
lemma small_case (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp2 : p ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℤ →₀ ℂ, N p (L (T := T) (P c)) ≤ K * N p (L (T := T) c) := by
  obtain ⟨K1, hK1, hreal⟩ := real_case (T := T) p hp hp2
  refine ⟨2 * K1, by positivity, fun c => ?_⟩
  have hre : N p (L (T := T) (rePart c)) ≤ N p (L (T := T) c) := by
    apply N_mono; intro x
    rw [L_rePart, Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have him : N p (L (T := T) (imPart c)) ≤ N p (L (T := T) c) := by
    apply N_mono; intro x
    rw [L_imPart, Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _
  have hPc : P c = P (rePart c) + Complex.I • P (imPart c) := by
    rw [← P_smul, ← P_add, re_add_im]
  calc N p (L (T := T) (P c)) = N p (L (T := T) (P (rePart c)) + Complex.I • L (T := T) (P (imPart c))) := by
        rw [hPc, map_add, map_smul]
    _ ≤ N p (L (T := T) (P (rePart c))) + N p (Complex.I • L (T := T) (P (imPart c))) := N_add_le p _ _
    _ = N p (L (T := T) (P (rePart c))) + N p (L (T := T) (P (imPart c))) := by
        rw [N_smul, Complex.norm_I, one_mul]
    _ ≤ K1 * N p (L (T := T) (rePart c)) + K1 * N p (L (T := T) (imPart c)) :=
        add_le_add (hreal _ (rePart_SA c)) (hreal _ (imPart_SA c))
    _ ≤ K1 * N p (L (T := T) c) + K1 * N p (L (T := T) c) := by gcongr
    _ = 2 * K1 * N p (L (T := T) c) := by ring

/-! ### Duality: the case `2 < p < ∞` -/

lemma integral_mul_conj (c e : ℤ →₀ ℂ) :
    ∫ x, L (T := T) c x * starRingEnd ℂ (L (T := T) e x) ∂haarAddCircle =
      ∑ m ∈ e.support, c m * starRingEnd ℂ (e m) := by
  have h1 : ∀ x, L (T := T) c x * starRingEnd ℂ (L (T := T) e x) =
      ∑ m ∈ e.support, starRingEnd ℂ (e m) * (fourier (-m) x • L (T := T) c x) := by
    intro x
    rw [L_apply e x, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [map_mul, ← fourier_neg, smul_eq_mul]; ring
  simp_rw [h1]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl; intro m _
    rw [integral_const_mul]
    have := fourierCoeff_L (T := T) c m
    rw [fourierCoeff] at this
    rw [this]; ring
  · intro m _
    exact (integrable_cont ((fourier (-m)).continuous.smul (L (T := T) c).continuous)).const_mul _

lemma pair_P (c e : ℤ →₀ ℂ) :
    ∫ x, L (T := T) (P c) x * starRingEnd ℂ (L (T := T) e x) ∂haarAddCircle =
      ∫ x, L (T := T) c x * starRingEnd ℂ (L (T := T) (P e) x) ∂haarAddCircle := by
  rw [integral_mul_conj, integral_mul_conj]
  unfold P
  rw [Finsupp.support_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Finsupp.filter_apply]
  split_ifs <;> simp

lemma holder (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (hpq : p.toReal.HolderConjugate q.toReal) (f g : C(AddCircle T, ℂ)) :
    ‖∫ x, f x * starRingEnd ℂ (g x) ∂haarAddCircle‖ ≤ N p f * N q g := by
  rw [N_eq_integral p hp, N_eq_integral q hq]
  refine (norm_integral_le_integral_norm _).trans ?_
  have h1 : ∀ x, ‖f x * starRingEnd ℂ (g x)‖ = ‖f x‖ * ‖g x‖ := by
    intro x; rw [norm_mul, Complex.norm_conj]
  simp_rw [h1]
  apply integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ (fun x => norm_nonneg _))
    (ae_of_all _ (fun x => norm_nonneg _))
  · rw [ENNReal.ofReal_toReal hp]
    exact (ContinuousMap.memLp (μ := haarAddCircle (T := T)) (p := p) ℂ f).norm
  · rw [ENNReal.ofReal_toReal hq]
    exact (ContinuousMap.memLp (μ := haarAddCircle (T := T)) (p := q) ℂ g).norm

lemma approx (g : C(AddCircle T, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ e : ℤ →₀ ℂ, ∀ x, ‖L (T := T) e x - g x‖ < ε := by
  have hmem : g ∈ (Submodule.span ℂ (Set.range (fourier (T := T)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨y, hy, hdist⟩ := hmem ε hε
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp (SetLike.mem_coe.mp hy)
  refine ⟨c, fun x => ?_⟩
  have h1 : L (T := T) c = y := by rw [L_eq_sum, hc]
  rw [h1]
  calc ‖y x - g x‖ = ‖(y - g) x‖ := rfl
    _ ≤ ‖y - g‖ := ContinuousMap.norm_coe_le_norm _ x
    _ = dist g y := by rw [dist_comm, dist_eq_norm]
    _ < ε := hdist

lemma large_case (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ∞) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℤ →₀ ℂ, N p (L (T := T) (P c)) ≤ K * N p (L (T := T) c) := by
  set r := p.toReal with hr
  have hr2 : 2 < r := by
    rw [hr]; have := ENNReal.toReal_strict_mono hptop hp; simpa using this
  set s := r / (r - 1) with hs
  have hrs : r.HolderConjugate s := (Real.holderConjugate_iff_eq_conjExponent (by linarith)).mpr rfl
  have hs1 : 1 < s := hrs.symm.lt
  have hs2 : s ≤ 2 := by
    rw [hs, div_le_iff₀ (by linarith)]; linarith
  set q := ENNReal.ofReal s with hq
  haveI : Fact (1 ≤ q) := ⟨ENNReal.one_le_ofReal.mpr hs1.le⟩
  have hq1 : 1 < q := ENNReal.one_lt_ofReal.mpr hs1
  have hq2 : q ≤ 2 := by
    rw [hq]; exact ENNReal.ofReal_le_of_le_toReal (by simpa using hs2)
  have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
  have hqr : q.toReal = s := ENNReal.toReal_ofReal (by linarith)
  have hpq : p.toReal.HolderConjugate q.toReal := by rw [hqr]; exact hrs
  obtain ⟨K, hK, hsmall⟩ := small_case (T := T) q hq1 hq2
  refine ⟨K, hK, fun c => ?_⟩
  set h := L (T := T) (P c) with hhdef
  set M := ∫ x, ‖h x‖ ^ r ∂haarAddCircle with hM
  have hM0 : 0 ≤ M := integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have hNh : N p h = M ^ (1 / r) := N_eq_integral p hptop h
  have hGc : Continuous (fun x => ((‖h x‖ ^ (r - 2) : ℝ) : ℂ) * h x) :=
    (Complex.continuous_ofReal.comp (h.continuous.norm.rpow_const
      (fun _ => Or.inr (by linarith)))).mul h.continuous
  let G : C(AddCircle T, ℂ) := ⟨_, hGc⟩
  have hGapp : ∀ x, G x = ((‖h x‖ ^ (r - 2) : ℝ) : ℂ) * h x := fun x => rfl
  have hreal : ∀ x, ‖h x‖ ^ (r - 2) * ‖h x‖ ^ 2 = ‖h x‖ ^ r := by
    intro x
    by_cases hx : ‖h x‖ = 0
    · rw [hx, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]; ring
    · have hpos : 0 < ‖h x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      rw [← Real.rpow_natCast, ← Real.rpow_add hpos]; norm_num
  have hhG : ∀ x, h x * starRingEnd ℂ (G x) = ((‖h x‖ ^ r : ℝ) : ℂ) := by
    intro x
    rw [hGapp, map_mul, Complex.conj_ofReal]
    rw [show h x * (((‖h x‖ ^ (r - 2) : ℝ) : ℂ) * starRingEnd ℂ (h x)) =
      ((‖h x‖ ^ (r - 2) : ℝ) : ℂ) * (h x * starRingEnd ℂ (h x)) by ring]
    rw [Complex.mul_conj', ← hreal x]
    push_cast; ring
  have hGnorm : ∀ x, ‖G x‖ = ‖h x‖ ^ (r - 1) := by
    intro x
    rw [hGapp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    by_cases hx : ‖h x‖ = 0
    · rw [hx, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]; ring
    · have hpos : 0 < ‖h x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      conv_lhs => rw [show ‖h x‖ ^ (r - 2) * ‖h x‖ = ‖h x‖ ^ (r - 2) * ‖h x‖ ^ (1 : ℝ) by
        rw [Real.rpow_one]]
      rw [← Real.rpow_add hpos]; ring_nf
  have hNG : N q G = M ^ (1 / s) := by
    rw [N_eq_integral q hqtop, hqr]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    rw [hGnorm, ← Real.rpow_mul (norm_nonneg _), hrs.sub_one_mul_conj]
  have hint : ∫ x, h x * starRingEnd ℂ (G x) ∂haarAddCircle = (M : ℂ) := by
    simp_rw [hhG]; exact integral_ofReal
  have hY0 : 0 ≤ K * N p (L (T := T) c) + N p h := by
    have := N_nonneg p (L (T := T) c); have := N_nonneg p h; positivity
  have key : ∀ ε : ℝ, 0 < ε →
      M ≤ K * N p (L (T := T) c) * M ^ (1 / s) + ε * (K * N p (L (T := T) c) + N p h) := by
    intro ε hε
    obtain ⟨e, he⟩ := approx (T := T) G ε hε
    have hdiff : N q (G - L (T := T) e) ≤ ε :=
      N_le_of_bound q _ ε hε.le (fun x => by
        rw [ContinuousMap.sub_apply, norm_sub_rev]; exact (he x).le)
    have hLe : N q (L (T := T) e) ≤ M ^ (1 / s) + ε := by
      have : L (T := T) e = G - (G - L (T := T) e) := by abel
      rw [this]
      refine (N_sub_le q _ _).trans ?_
      rw [hNG]; linarith
    have hsplit : ∫ x, h x * starRingEnd ℂ (G x) ∂haarAddCircle =
        ∫ x, h x * starRingEnd ℂ (L (T := T) e x) ∂haarAddCircle +
          ∫ x, h x * starRingEnd ℂ ((G - L (T := T) e) x) ∂haarAddCircle := by
      rw [← integral_add]
      · congr 1; ext x
        rw [ContinuousMap.sub_apply, map_sub]; ring
      · exact integrable_cont (h.continuous.mul (Complex.continuous_conj.comp (L (T := T) e).continuous))
      · exact integrable_cont (h.continuous.mul (Complex.continuous_conj.comp (G - L (T := T) e).continuous))
    have h1 : ‖∫ x, h x * starRingEnd ℂ (L (T := T) e x) ∂haarAddCircle‖ ≤
        K * N p (L (T := T) c) * (M ^ (1 / s) + ε) := by
      rw [hhdef, pair_P c e]
      calc _ ≤ N p (L (T := T) c) * N q (L (T := T) (P e)) := holder p q hptop hqtop hpq _ _
        _ ≤ N p (L (T := T) c) * (K * N q (L (T := T) e)) := by
            gcongr; · exact N_nonneg p _
            exact hsmall e
        _ ≤ N p (L (T := T) c) * (K * (M ^ (1 / s) + ε)) := by
            gcongr; · exact N_nonneg p _
        _ = K * N p (L (T := T) c) * (M ^ (1 / s) + ε) := by ring
    have h2 : ‖∫ x, h x * starRingEnd ℂ ((G - L (T := T) e) x) ∂haarAddCircle‖ ≤ N p h * ε :=
      (holder p q hptop hqtop hpq _ _).trans (by gcongr; exact N_nonneg p _)
    have hMn : M = ‖(M : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
    calc M = ‖(M : ℂ)‖ := hMn
      _ = ‖∫ x, h x * starRingEnd ℂ (G x) ∂haarAddCircle‖ := by rw [hint]
      _ ≤ _ := by rw [hsplit]; exact norm_add_le _ _
      _ ≤ K * N p (L (T := T) c) * (M ^ (1 / s) + ε) + N p h * ε := add_le_add h1 h2
      _ = _ := by ring
  have hmain : M ≤ K * N p (L (T := T) c) * M ^ (1 / s) := by
    apply _root_.le_of_forall_pos_le_add
    intro δ hδ
    have hY1 : 0 < K * N p (L (T := T) c) + N p h + 1 := by linarith
    have := key (δ / (K * N p (L (T := T) c) + N p h + 1)) (div_pos hδ hY1)
    have h7 : δ / (K * N p (L (T := T) c) + N p h + 1) * (K * N p (L (T := T) c) + N p h) ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hY1]; nlinarith
    linarith
  rw [hNh]
  rcases eq_or_lt_of_le hM0 with hM00 | hMpos
  · rw [← hM00, Real.zero_rpow (by positivity)]
    exact mul_nonneg hK (N_nonneg p _)
  · have hsplitM : M = M ^ (1 / r) * M ^ (1 / s) := by
      rw [← Real.rpow_add hMpos]
      have : 1 / r + 1 / s = 1 := by
        have := hrs.inv_add_inv_eq_one; simpa [one_div] using this
      rw [this, Real.rpow_one]
    have hMs : 0 < M ^ (1 / s) := Real.rpow_pos_of_pos hMpos _
    have hmain' : M ^ (1 / r) * M ^ (1 / s) ≤ K * N p (L (T := T) c) * M ^ (1 / s) := by
      rw [← hsplitM]; exact hmain
    exact le_of_mul_le_mul_right hmain' hMs

end Sol_FourierSeries_exists_rieszProjection_norm_le

open Sol_FourierSeries_exists_rieszProjection_norm_le in
theorem solution (T : ℝ) [Fact (0 < T)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p) (hp' : p ≠ ∞) :
    ∃ C : ℝ, ∀ (s : Finset ℤ) (c : ℤ → ℂ),
      ‖∑ n ∈ s with 0 ≤ n, c n • fourierLp (T := T) p n‖ ≤
        C * ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖ := by
  obtain ⟨K, _, hbound⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℤ →₀ ℂ,
      N p (L (T := T) (P c)) ≤ K * N p (L (T := T) c) := by
    rcases le_or_gt p 2 with h2 | h2
    · exact small_case p hp h2
    · exact large_case p h2 hp'
  refine ⟨K, fun s c => ?_⟩
  set c' : ℤ →₀ ℂ := Finsupp.onFinset s (fun n => if n ∈ s then c n else 0) (by
    intro n hn; by_contra h; exact hn (if_neg h)) with hc'
  have hL1 : L (T := T) c' = ∑ n ∈ s, c n • fourier n := by
    rw [L_eq_sum, hc', Finsupp.onFinset_sum _ (fun a => by simp)]
    apply Finset.sum_congr rfl; intro n hn; rw [if_pos hn]
  have hL2 : L (T := T) (P c') = ∑ n ∈ s with 0 ≤ n, c n • fourier n := by
    rw [L_eq_sum, Finsupp.sum_of_support_subset (P c') (s := s.filter (fun n => 0 ≤ n))]
    · apply Finset.sum_congr rfl; intro n hn
      rw [Finset.mem_filter] at hn
      simp [P, Finsupp.filter_apply, hn.1, hn.2, hc']
    · intro n hn
      rw [P, Finsupp.support_filter, Finset.mem_filter] at hn
      rw [Finset.mem_filter]
      exact ⟨Finsupp.support_onFinset_subset hn.1, hn.2⟩
    · intro i _; simp
  have h1 : ∑ n ∈ s, c n • fourierLp (T := T) p n =
      ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ (L (T := T) c') := by
    rw [hL1]; simp only [map_sum, map_smul]
  have h2 : ∑ n ∈ s with 0 ≤ n, c n • fourierLp (T := T) p n =
      ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ (L (T := T) (P c')) := by
    rw [hL2]; simp only [map_sum, map_smul]
  rw [h1, h2]
  exact hbound c'
