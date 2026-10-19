-- Prove2me | solution 1 for CauchyRiemannIndex.asymptoticCZIndex_eq_winding_of_antilinear
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T16:54:55.633984+00:00
-- url     : https://prove2.me/submissions/6207d0c7-c382-4f3d-9597-b7e5751a70f2

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_CauchyRiemannIndex_exists_contDiff_periodic_approx
import Theorems.Thm_CauchyRiemannIndex_isNondegenerate_add_smul_antilinearMat
import Theorems.Thm_CauchyRiemannIndex_arg_add_one_sub_eq
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_of_joined
import Theorems.Thm_CauchyRiemannIndex_model_asymptotic_operator
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Operations



namespace CauchyRiemannIndex

open Matrix Complex
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem asymptoticCZIndex_eq_winding_of_antilinear_aux (S : ℝ → Mat 1) (hS : IsSymLoop S)
    (β : ℝ → ℂ) (hβ : Continuous β) (hper : Function.Periodic β 1) (hnz : ∀ t, β t ≠ 0)
    (hnd : ∀ σ : ℝ, 0 ≤ σ → IsNondegenerate (fun t => S t + σ • antilinearMat (β t)))
    (w : ℤ) (θ : ℝ → ℝ) (hθ : Continuous θ)
    (harg : ∀ t, β t = ‖β t‖ * Complex.exp (θ t * Complex.I))
    (hw : θ 1 - θ 0 = 2 * Real.pi * w) :
    asymptoticCZIndex S = w := by
  /- generic facts about `antilinearMat` -/
  have hAsymm : ∀ z : ℂ, (antilinearMat z).IsSymm := by
    intro z; ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [antilinearMat, Matrix.transpose_apply, Matrix.fromBlocks]
  have hAsub : ∀ a b : ℂ, antilinearMat (a - b) = antilinearMat a - antilinearMat b := by
    intro a b; ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [antilinearMat, Matrix.fromBlocks] <;> ring
  have hAent : ∀ (z : ℂ) i j, |antilinearMat z i j| ≤ ‖z‖ := by
    intro z i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [antilinearMat, Matrix.fromBlocks, Complex.abs_re_le_norm, Complex.abs_im_le_norm]
  have hAcont : Continuous antilinearMat := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp [antilinearMat, Matrix.fromBlocks] <;>
      fun_prop
  have hSc : Continuous S := hS.1
  /- bounded continuous periodic functions -/
  have hbdd : ∀ f : ℝ → ℝ, Continuous f → Function.Periodic f 1 → ∃ C, ∀ t, |f t| ≤ C := by
    intro f hf hp
    obtain ⟨C, hC⟩ := (hp.compact_of_continuous one_ne_zero hf).isBounded.exists_norm_le
    exact ⟨C, fun t => by simpa using hC (f t) ⟨t, rfl⟩⟩
  have hderiv : ∀ f : ℝ → ℝ, ContDiff ℝ ∞ f → Function.Periodic f 1 →
      (∀ t, HasDerivAt f (deriv f t) t) ∧ ∃ C, ∀ t, |deriv f t| ≤ C := by
    intro f hf hp
    have hd : Differentiable ℝ f := hf.differentiable (by simp)
    refine ⟨fun t => (hd t).hasDerivAt, hbdd _ (hf.continuous_deriv (by simp)) ?_⟩
    intro t
    have h1 : (fun x => f (x + 1)) = f := funext hp
    rw [← deriv_comp_add_const, h1]
  /- entry bound for `S` -/
  obtain ⟨KS, hKS⟩ : ∃ K, ∀ t i j, |S t i j| ≤ K := by
    have : ∀ i j, ∃ C, ∀ t, |S t i j| ≤ C := fun i j =>
      hbdd (fun t => S t i j) ((continuous_apply j).comp ((continuous_apply i).comp hS.1))
        (fun t => by simp only [hS.2.1 t])
    choose C hC using this
    refine ⟨∑ i, ∑ j, |C i j|, fun t i j => (hC i j t).trans ((le_abs_self _).trans ?_)⟩
    exact (Finset.single_le_sum (f := fun j => |C i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, |C i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  /- modulus of `β` -/
  have hrc : Continuous (fun t => ‖β t‖) := hβ.norm
  have hrp : Function.Periodic (fun t => ‖β t‖) 1 := fun t => by simp only [hper t]
  obtain ⟨m₀, hm₀, hm₀le⟩ : ∃ m₀ > 0, ∀ t, m₀ ≤ ‖β t‖ := by
    obtain ⟨y, ⟨t₀, rfl⟩, hy⟩ :=
      (hrp.compact_of_continuous one_ne_zero hrc).exists_isLeast (Set.range_nonempty _)
    exact ⟨‖β t₀‖, norm_pos_iff.2 (hnz t₀), fun t => hy ⟨t, rfl⟩⟩
  obtain ⟨R₀, hR₀⟩ := hbdd _ hrc hrp
  have hrR : ∀ t, ‖β t‖ ≤ |R₀| := fun t =>
    (le_abs_self _).trans ((hR₀ t).trans (le_abs_self _))
  /- the periodic part of the argument -/
  have hθ1 : ∀ t, θ (t + 1) - θ t = 2 * Real.pi * w :=
    arg_add_one_sub_eq β hper hnz θ hθ harg w hw
  let g : ℝ → ℝ := fun t => θ t - 2 * Real.pi * w * t
  have hgc : Continuous g := by fun_prop
  have hgp : Function.Periodic g 1 := fun t => by
    simp only [g]; linarith [hθ1 t]
  /- constants -/
  set m₃ : ℝ := min (m₀ / 2) 1 with hm₃
  have hm₃0 : 0 < m₃ := lt_min (by linarith) one_pos
  have hm₃1 : m₃ ≤ 1 := min_le_right _ _
  have hm₃2 : m₃ ≤ m₀ / 2 := min_le_left _ _
  set R₁ : ℝ := |R₀| + 1 with hR₁
  have hR₁0 : 1 ≤ R₁ := by simp [hR₁, abs_nonneg]
  /- smoothing -/
  obtain ⟨rh, hrhs, hrhp, hrha⟩ :=
    exists_contDiff_periodic_approx _ hrc hrp (m₃ / 32) (by positivity)
  obtain ⟨gh, hghs, hghp, hgha⟩ :=
    exists_contDiff_periodic_approx g hgc hgp (m₃ / (32 * R₁)) (by positivity)
  obtain ⟨hrhd, Cr, hCr⟩ := hderiv rh hrhs hrhp
  obtain ⟨hghd, Cg, hCg⟩ := hderiv gh hghs hghp
  have hrh_lo : ∀ t, m₃ ≤ rh t := fun t => by
    have := hm₀le t; have := (abs_le.1 (hrha t)).1; linarith
  have hrh_hi : ∀ t, rh t ≤ R₁ := fun t => by
    have := hrR t; have := (abs_le.1 (hrha t)).2; simp only [hR₁]; linarith
  have hCr0 : ∀ t, |deriv rh t| ≤ Cr := hCr
  /- the family of loops -/
  let γ : ℝ → ℝ → ℂ := fun l t =>
    (((1 - l) * rh t + l : ℝ) : ℂ) *
      Complex.exp ((((2 * Real.pi * w * t + (1 - l) * gh t) : ℝ) : ℂ) * Complex.I)
  set D₃ : ℝ := Cr + R₁ * (2 * Real.pi * |(w : ℝ)| + Cg) with hD₃
  have hγper : ∀ l, Function.Periodic (γ l) 1 := by
    intro l t
    simp only [γ]
    have e : ((((2 * Real.pi * w * (t + 1) + (1 - l) * gh (t + 1)) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * w * t + (1 - l) * gh t) : ℝ) : ℂ) * Complex.I +
          (w : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hghp t]; push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hrhp t]
  have hγnorm : ∀ l, 0 ≤ l → l ≤ 1 → ∀ t, m₃ ≤ ‖γ l t‖ := by
    intro l hl0 hl1 t
    have hρ : m₃ ≤ (1 - l) * rh t + l := by nlinarith [hrh_lo t]
    have : ‖γ l t‖ = |(1 - l) * rh t + l| := by
      simp only [γ, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
    rw [this, abs_of_pos (by linarith)]
    exact hρ
  have hγderiv : ∀ l, 0 ≤ l → l ≤ 1 → ∃ γ' : ℝ → ℂ, (∀ t, HasDerivAt (γ l) (γ' t) t) ∧
      ∀ t, ‖γ' t‖ ≤ D₃ := by
    intro l hl0 hl1
    have hρd : ∀ t, HasDerivAt (fun x => (1 - l) * rh x + l) ((1 - l) * deriv rh t) t :=
      fun t => ((hrhd t).const_mul (1 - l)).add_const l
    have hφd : ∀ t, HasDerivAt (fun x => 2 * Real.pi * w * x + (1 - l) * gh x)
        (2 * Real.pi * w + (1 - l) * deriv gh t) t := fun t => by
      exact (((hasDerivAt_id' t).const_mul (2 * Real.pi * w)).add
        ((hghd t).const_mul (1 - l))).congr_deriv (by ring)
    refine ⟨fun t => ((((1 - l) * deriv rh t) : ℝ) : ℂ) *
        Complex.exp ((((2 * Real.pi * w * t + (1 - l) * gh t) : ℝ) : ℂ) * Complex.I) +
      (((1 - l) * rh t + l : ℝ) : ℂ) *
        (Complex.exp ((((2 * Real.pi * w * t + (1 - l) * gh t) : ℝ) : ℂ) * Complex.I) *
          ((((2 * Real.pi * w + (1 - l) * deriv gh t) : ℝ) : ℂ) * Complex.I)), ?_, ?_⟩
    · intro t
      exact (hρd t).ofReal_comp.mul (((hφd t).ofReal_comp.mul_const Complex.I).cexp)
    · intro t
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, one_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I]
      have h1 : |(1 - l) * deriv rh t| ≤ Cr := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l)]
        nlinarith [hCr t, abs_nonneg (deriv rh t)]
      have h2 : |(1 - l) * rh t + l| ≤ R₁ := by
        rw [abs_of_pos (by nlinarith [hrh_lo t])]; nlinarith [hrh_hi t]
      have h3 : |2 * Real.pi * w + (1 - l) * deriv gh t| ≤ 2 * Real.pi * |(w : ℝ)| + Cg := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        · rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l)]
          nlinarith [hCg t, abs_nonneg (deriv gh t)]
      have h4 : 0 ≤ |2 * Real.pi * w + (1 - l) * deriv gh t| := abs_nonneg _
      rw [← abs_mul (1 - l)]
      calc _ ≤ Cr + R₁ * (2 * Real.pi * |(w : ℝ)| + Cg) :=
            add_le_add h1 (mul_le_mul h2 h3 h4 (by linarith))
        _ = D₃ := rfl
  /- the smoothed loop `β̂ = γ 0` and its distance to `β` -/
  have hββ : ∀ t, ‖β t - γ 0 t‖ ≤ m₃ / 16 := by
    intro t
    have hexp : Complex.exp ((θ t : ℂ) * Complex.I) =
        Complex.exp ((((2 * Real.pi * w * t + gh t) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (Complex.I * ((g t - gh t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; simp only [g]; push_cast; ring
    have e1 : β t - γ 0 t = ((‖β t‖ - rh t : ℝ) : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I) +
        (rh t : ℂ) * (Complex.exp ((((2 * Real.pi * w * t + gh t) : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (Complex.I * ((g t - gh t : ℝ) : ℂ)) - 1)) := by
      nth_rewrite 1 [harg t]
      simp only [γ, sub_zero, one_mul, add_zero]
      rw [hexp]; push_cast; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, one_mul]
    have h1 : |‖β t‖ - rh t| ≤ m₃ / 32 := by rw [abs_sub_comm]; exact hrha t
    have h2 : ‖Complex.exp (Complex.I * ((g t - gh t : ℝ) : ℂ)) - 1‖ ≤ m₃ / (32 * R₁) := by
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
      rw [Real.norm_eq_abs, abs_sub_comm]; exact hgha t
    have h3 : |rh t| ≤ R₁ := by
      rw [abs_of_pos (by linarith [hrh_lo t])]; exact hrh_hi t
    have h4 : |rh t| * ‖Complex.exp (Complex.I * ((g t - gh t : ℝ) : ℂ)) - 1‖ ≤ m₃ / 32 := by
      calc _ ≤ R₁ * (m₃ / (32 * R₁)) := mul_le_mul h3 h2 (norm_nonneg _) (by linarith)
        _ = m₃ / 32 := by field_simp
    linarith
  /- the size of the antilinear term -/
  set K₃ : ℝ := |KS| + Real.pi * |(w : ℝ)| with hK₃
  have hK₃0 : |KS| ≤ K₃ := by simp only [hK₃]; nlinarith [Real.pi_pos, abs_nonneg (w : ℝ)]
  obtain ⟨σ₁, hσ₁, hσ₁big⟩ : ∃ σ₁ : ℝ, 0 < σ₁ ∧
      8 * K₃ ^ 2 + 2 * σ₁ * D₃ < σ₁ ^ 2 * m₃ ^ 2 / 2 := by
    set c : ℝ := m₃ ^ 2 / 2 with hc
    have hc0 : 0 < c := by positivity
    set A : ℝ := 2 * D₃
    set E : ℝ := 8 * K₃ ^ 2
    have hE : 0 ≤ E := by positivity
    refine ⟨(|A| + E + 1) / c + 1, by positivity, ?_⟩
    set s := (|A| + E + 1) / c + 1 with hs
    have hs1 : 1 ≤ s := by
      have : 0 ≤ (|A| + E + 1) / c := by positivity
      simp only [hs]; linarith
    have hsc : s * c = |A| + E + 1 + c := by simp only [hs]; field_simp
    have : s ^ 2 * m₃ ^ 2 / 2 = s * (s * c) := by simp only [hc]; ring
    rw [this, hsc]
    nlinarith [mul_le_mul_of_nonneg_left (neg_abs_le A) (by linarith : (0:ℝ) ≤ s),
      le_abs_self A, mul_le_mul_of_nonneg_left hs1 hE]
  have hD₃0 : 0 ≤ D₃ := by
    obtain ⟨γ', -, hγ'⟩ := hγderiv 0 le_rfl zero_le_one
    exact (norm_nonneg _).trans (hγ' 0)
  /- joined loops have the same index -/
  have joined : ∀ F : ℝ → ℝ → Mat 1, Continuous (fun p : ℝ × ℝ => F p.1 p.2) →
      (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → Function.Periodic (F τ) 1 ∧ (∀ t, (F τ t).IsSymm) ∧
        IsNondegenerate (F τ)) → asymptoticCZIndex (F 0) = asymptoticCZIndex (F 1) := by
    intro F hF hτ
    let H : C(unitInterval × ℝ, Mat 1) :=
      ⟨fun p => F p.1 p.2, hF.comp (continuous_subtype_val.prodMap continuous_id)⟩
    refine asymptoticCZIndex_eq_of_joined 1 (F 0) (F 1) H (fun t => rfl) (fun t => rfl)
      (fun τ => ?_)
    obtain ⟨h1, h2, h3⟩ := hτ τ τ.2.1 τ.2.2
    exact ⟨⟨hF.comp ((continuous_const : Continuous fun _ : ℝ => (τ : ℝ)).prodMk continuous_id),
      h1, h2⟩, h3⟩
  /- stage 1: `σ` from `0` to `σ₁` -/
  have st1 : asymptoticCZIndex S =
      asymptoticCZIndex (fun t => S t + σ₁ • antilinearMat (β t)) := by
    have := joined (fun τ t => S t + (τ * σ₁) • antilinearMat (β t)) (by fun_prop)
      (fun τ h0 h1 => ⟨fun t => by simp only [hS.2.1 t, hper t],
        fun t => (hS.2.2 t).add ((hAsymm _).smul _), hnd _ (by positivity)⟩)
    simpa using this
  /- stage 2: `β` to `β̂` at `σ₁` -/
  have hγ0c : Continuous (γ 0) := by
    have := hrhs.continuous; have := hghs.continuous
    simp only [γ]; fun_prop
  have st2 : asymptoticCZIndex (fun t => S t + σ₁ • antilinearMat (β t)) =
      asymptoticCZIndex (fun t => S t + σ₁ • antilinearMat (γ 0 t)) := by
    have := joined (fun τ t => (S t + (σ₁ * (1 - τ)) • antilinearMat (β t - γ 0 t)) +
        σ₁ • antilinearMat (γ 0 t)) (by fun_prop) (fun τ h0 h1 => ⟨fun t => by
          simp only [hS.2.1 t, hper t, hγper 0 t], fun t => ((hS.2.2 t).add
            ((hAsymm _).smul _)).add ((hAsymm _).smul _), ?_⟩)
    · convert this using 2
      · funext t; simp only [sub_zero, mul_one, hAsub, smul_sub]; abel
      · funext t; simp
    · obtain ⟨γ', hγ'd, hγ'b⟩ := hγderiv 0 le_rfl zero_le_one
      refine isNondegenerate_add_smul_antilinearMat _ (fun t => (hS.2.2 t).add
        ((hAsymm _).smul _)) (|KS| + σ₁ * (m₃ / 16)) ?_ (γ 0) γ' hγ'd (hγper 0) m₃ D₃
        hm₃0.le (hγnorm 0 le_rfl zero_le_one) hγ'b σ₁ hσ₁ ?_
      · intro t i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        refine (abs_add_le _ _).trans (add_le_add ((hKS t i j).trans (le_abs_self _)) ?_)
        rw [abs_mul, abs_mul, abs_of_pos hσ₁, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - τ)]
        have hB := (hAent (β t - γ 0 t) i j).trans (hββ t)
        have h5 : (1 - τ) * |antilinearMat (β t - γ 0 t) i j| ≤ 1 * (m₃ / 16) :=
          mul_le_mul (by linarith) hB (abs_nonneg _) zero_le_one
        rw [one_mul] at h5
        calc σ₁ * (1 - τ) * |antilinearMat (β t - γ 0 t) i j|
            = σ₁ * ((1 - τ) * |antilinearMat (β t - γ 0 t) i j|) := by ring
          _ ≤ σ₁ * (m₃ / 16) := mul_le_mul_of_nonneg_left h5 hσ₁.le
      · have hK : (|KS| + σ₁ * (m₃ / 16)) ^ 2 ≤ 2 * K₃ ^ 2 + 2 * (σ₁ * (m₃ / 16)) ^ 2 := by
          have := mul_le_mul hK₃0 hK₃0 (abs_nonneg _) ((abs_nonneg _).trans hK₃0)
          nlinarith [sq_nonneg (|KS| - σ₁ * (m₃ / 16))]
        have : 0 < σ₁ ^ 2 * m₃ ^ 2 := by positivity
        nlinarith
  /- stage 3: joint deformation to the model loop -/
  have st3 : asymptoticCZIndex (fun t => S t + σ₁ • antilinearMat (γ 0 t)) =
      asymptoticCZIndex (fun t => (Real.pi * w) • (1 : Mat 1) +
        σ₁ • antilinearMat (Complex.exp (2 * Real.pi * w * t * Complex.I))) := by
    have hγc : Continuous (fun p : ℝ × ℝ => γ p.1 p.2) := by
      have := hrhs.continuous; have := hghs.continuous
      simp only [γ]; fun_prop
    have := joined (fun l t => ((1 - l) • S t + (l * (Real.pi * w)) • (1 : Mat 1)) +
        σ₁ • antilinearMat (γ l t)) (by fun_prop) (fun l h0 h1 => ⟨fun t => by
          simp only [hS.2.1 t, hγper l t], fun t => (((hS.2.2 t).smul _).add
            (Matrix.isSymm_one.smul _)).add ((hAsymm _).smul _), ?_⟩)
    · convert this using 2
      · funext t; simp
      · funext t
        have : γ 1 t = Complex.exp (2 * Real.pi * w * t * Complex.I) := by
          simp only [γ, sub_self, zero_mul, zero_add, Complex.ofReal_one, one_mul]
          congr 1; push_cast; ring
        simp [this]
    · obtain ⟨γ', hγ'd, hγ'b⟩ := hγderiv l h0 h1
      refine isNondegenerate_add_smul_antilinearMat _ (fun t => ((hS.2.2 t).smul _).add
        (Matrix.isSymm_one.smul _)) K₃ ?_ (γ l) γ' hγ'd (hγper l) m₃ D₃
        hm₃0.le (hγnorm l h0 h1) hγ'b σ₁ hσ₁ ?_
      · intro t i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        refine (abs_add_le _ _).trans ?_
        have e1 : |(1 - l) * S t i j| ≤ |KS| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l)]
          nlinarith [(hKS t i j).trans (le_abs_self KS), abs_nonneg (S t i j)]
        have hone : |(1 : Mat 1) i j| ≤ 1 := by
          rw [Matrix.one_apply]; split_ifs <;> simp
        have e2 : |l * (Real.pi * w) * (1 : Mat 1) i j| ≤ Real.pi * |(w : ℝ)| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_pos Real.pi_pos]
          have := abs_nonneg (w : ℝ)
          have := abs_nonneg ((1 : Mat 1) i j)
          have : 0 ≤ Real.pi := Real.pi_pos.le
          nlinarith [mul_le_mul h1 hone (abs_nonneg _) zero_le_one]
        simp only [hK₃]; linarith
      · nlinarith [sq_nonneg (σ₁ * m₃), sq_nonneg K₃]
  /- the model loop -/
  have hmodel := (model_asymptotic_operator w σ₁ hσ₁).2
  rw [st1, st2, st3]
  exact hmodel

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (S : ℝ → Mat 1) (hS : IsSymLoop S)
    (β : ℝ → ℂ) (hβ : Continuous β) (hper : Function.Periodic β 1) (hnz : ∀ t, β t ≠ 0)
    (hnd : ∀ σ : ℝ, 0 ≤ σ → IsNondegenerate (fun t => S t + σ • antilinearMat (β t)))
    (w : ℤ) (θ : ℝ → ℝ) (hθ : Continuous θ)
    (harg : ∀ t, β t = ‖β t‖ * Complex.exp (θ t * Complex.I))
    (hw : θ 1 - θ 0 = 2 * Real.pi * w) :
    asymptoticCZIndex S = w :=
  CauchyRiemannIndex.asymptoticCZIndex_eq_winding_of_antilinear_aux S hS β hβ hper hnz hnd w θ hθ harg hw
