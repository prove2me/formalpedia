-- Prove2me | solution 1 for EthierKurtz.oblique_halfspace_model_solvability
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T12:51:39.177065+00:00
-- url     : https://prove2.me/submissions/e15ec798-bf0a-4992-ac26-d9bbb3bdaa49

import Mathlib
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph

set_option autoImplicit false

open Real MeasureTheory
open scoped BoundedContinuousFunction Topology

namespace P502049df

abbrev E2 := EuclideanSpace ℝ (Fin 2)

noncomputable def b0 : E2 := EuclideanSpace.single 0 1
noncomputable def b1 : E2 := EuclideanSpace.single 1 1
noncomputable def ev (θ : ℝ) : E2 := Real.cos θ • b0 + Real.sin θ • b1
noncomputable def ep (θ : ℝ) : E2 := (-Real.sin θ) • b0 + Real.cos θ • b1

lemma hasDerivAt_ev (θ : ℝ) : HasDerivAt ev (ep θ) θ := by
  have h1 := (Real.hasDerivAt_cos θ).smul_const b0
  have h2 := (Real.hasDerivAt_sin θ).smul_const b1
  exact h1.add h2

lemma hasDerivAt_ep (θ : ℝ) : HasDerivAt ep (-ev θ) θ := by
  have h1 := ((Real.hasDerivAt_sin θ).neg).smul_const b0
  have h2 := (Real.hasDerivAt_cos θ).smul_const b1
  exact (h1.add h2).congr_deriv (by rw [ev, neg_add, neg_smul, neg_smul])

lemma ev_apply0 (θ : ℝ) : ev θ 0 = Real.cos θ := by simp [ev, b0, b1]
lemma ev_apply1 (θ : ℝ) : ev θ 1 = Real.sin θ := by simp [ev, b0, b1]

lemma norm_ev (θ : ℝ) : ‖ev θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, ev_apply0, ev_apply1]
  simp [Real.cos_sq_add_sin_sq]

lemma ev_two_pi : ev (2 * π) = ev 0 := by simp [ev]
lemma ep_two_pi : ep (2 * π) = ep 0 := by simp [ep]

/-- trace invariance of a symmetric bilinear form under rotation. -/
lemma trace_rot (B : E2 →L[ℝ] E2 →L[ℝ] ℝ) (hB : B b0 b1 = B b1 b0) (θ : ℝ) :
    B (ev θ) (ev θ) + B (ep θ) (ep θ) = B b0 b0 + B b1 b1 := by
  simp only [ev, ep, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hB]
  linear_combination (B b0 b0 + B b1 b1) * (Real.sin_sq_add_cos_sq θ)

section paths
variable {u : E2 → ℝ}

lemma hasDerivAt_u_path {γ : ℝ → E2} {γ' : E2} {t : ℝ} (hγ : HasDerivAt γ γ' t)
    (hu : DifferentiableAt ℝ u (γ t)) :
    HasDerivAt (fun s => u (γ s)) (fderiv ℝ u (γ t) γ') t :=
  hu.hasFDerivAt.comp_hasDerivAt t hγ

lemma hasDerivAt_du_path {γ V : ℝ → E2} {γ' V' : E2} {t : ℝ} (hγ : HasDerivAt γ γ' t)
    (hV : HasDerivAt V V' t) (hu : DifferentiableAt ℝ (fderiv ℝ u) (γ t)) :
    HasDerivAt (fun s => fderiv ℝ u (γ s) (V s))
      (fderiv ℝ (fderiv ℝ u) (γ t) γ' (V t) + fderiv ℝ u (γ t) V') t := by
  have hc : HasDerivAt (fun s => fderiv ℝ u (γ s)) (fderiv ℝ (fderiv ℝ u) (γ t) γ') t :=
    hu.hasFDerivAt.comp_hasDerivAt t hγ
  exact hc.clm_apply hV

/-- radial quantity. -/
noncomputable def psi (u : E2 → ℝ) (c : E2) (r θ : ℝ) : ℝ :=
  (r * fderiv ℝ u (c + r • ev θ) (ev θ) + 3 * u (c + r • ev θ)) * Real.cos (3 * θ) / r ^ 3

/-- angular quantity. -/
noncomputable def chi (u : E2 → ℝ) (c : E2) (r θ : ℝ) : ℝ :=
  (r * fderiv ℝ u (c + r • ev θ) (ep θ) * Real.cos (3 * θ)
    + 3 * u (c + r • ev θ) * Real.sin (3 * θ)) / r ^ 4

noncomputable def D2 (u : E2 → ℝ) (y : E2) : E2 →L[ℝ] E2 →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ u) y

lemma psi_deriv (c : E2) {r θ : ℝ} (hr : r ≠ 0)
    (h1 : DifferentiableAt ℝ u (c + r • ev θ))
    (h2 : DifferentiableAt ℝ (fderiv ℝ u) (c + r • ev θ)) :
    HasDerivAt (fun s => psi u c s θ)
      ((r ^ 2 * D2 u (c + r • ev θ) (ev θ) (ev θ) + r * fderiv ℝ u (c + r • ev θ) (ev θ)
        - 9 * u (c + r • ev θ)) * Real.cos (3 * θ) / r ^ 4) r := by
  have hγ : HasDerivAt (fun s : ℝ => c + s • ev θ) (ev θ) r := by
    simpa using ((hasDerivAt_id r).smul_const (ev θ)).const_add c
  have hA := hasDerivAt_du_path (V := fun _ => ev θ) (V' := 0) hγ (hasDerivAt_const _ _) h2
  have hU := hasDerivAt_u_path hγ h1
  have hN := (((hasDerivAt_id' r).mul hA).add (hU.const_mul 3)).mul_const (Real.cos (3 * θ))
  have hD := hN.div (hasDerivAt_pow 3 r) (pow_ne_zero 3 hr)
  unfold psi
  refine hD.congr_deriv ?_
  simp only [map_zero, add_zero, D2, Pi.mul_apply, Pi.add_apply]
  field_simp
  ring

lemma chi_deriv (c : E2) {r θ : ℝ} (hr : r ≠ 0)
    (h1 : DifferentiableAt ℝ u (c + r • ev θ))
    (h2 : DifferentiableAt ℝ (fderiv ℝ u) (c + r • ev θ)) :
    HasDerivAt (fun t => chi u c r t)
      ((r ^ 2 * D2 u (c + r • ev θ) (ep θ) (ep θ) - r * fderiv ℝ u (c + r • ev θ) (ev θ)
        + 9 * u (c + r • ev θ)) * Real.cos (3 * θ) / r ^ 4) θ := by
  have hγ : HasDerivAt (fun t : ℝ => c + r • ev t) (r • ep θ) θ :=
    ((hasDerivAt_ev θ).const_smul r).const_add c
  have hA := hasDerivAt_du_path hγ (hasDerivAt_ep θ) h2
  have hU := hasDerivAt_u_path hγ h1
  have hc3 : HasDerivAt (fun t : ℝ => Real.cos (3 * t)) (-Real.sin (3 * θ) * 3) θ := by
    simpa using ((hasDerivAt_id' θ).const_mul 3).cos
  have hs3 : HasDerivAt (fun t : ℝ => Real.sin (3 * t)) (Real.cos (3 * θ) * 3) θ := by
    simpa using ((hasDerivAt_id' θ).const_mul 3).sin
  have hN := ((hA.const_mul r).mul hc3).add ((hU.const_mul 3).mul hs3)
  have hD := hN.div_const (r ^ 4)
  unfold chi
  refine hD.congr_deriv ?_
  simp only [D2, map_smul, map_neg, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

end paths

section trig

lemma hsk (k x : ℝ) : HasDerivAt (fun x => Real.sin (k * x)) (k * Real.cos (k * x)) x := by
  have := ((hasDerivAt_id' x).const_mul k).sin
  simpa [mul_comm] using this

lemma hck (k x : ℝ) : HasDerivAt (fun x => Real.cos (k * x)) (-(k * Real.sin (k * x))) x := by
  have := ((hasDerivAt_id' x).const_mul k).cos
  simpa [mul_comm] using this

lemma sin_k2pi (k : ℕ) : Real.sin (k * (2 * π)) = 0 := by
  rw [show (k : ℝ) * (2 * π) = ((2 * k : ℕ) : ℝ) * π by push_cast; ring]
  exact Real.sin_nat_mul_pi _

lemma cos_k2pi (k : ℕ) : Real.cos (k * (2 * π)) = 1 := Real.cos_nat_mul_two_pi k

lemma pcc (a b : ℝ) : Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

lemma psc (a b : ℝ) : Real.sin a * Real.cos b = (Real.sin (a + b) + Real.sin (a - b)) / 2 := by
  rw [Real.sin_add, Real.sin_sub]; ring

lemma int2pi {F f : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (f x) x) (hf : Continuous f) :
    ∫ x in (0 : ℝ)..2 * π, f x = F (2 * π) - F 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hf.intervalIntegrable _ _)

lemma I_c3 : ∫ x in (0 : ℝ)..2 * π, Real.cos (3 * x) = 0 := by
  rw [int2pi (F := fun x => Real.sin (3 * x) / 3) (fun x => (hsk 3 x).div_const 3 |>.congr_deriv
    (by ring)) (by fun_prop)]
  have := sin_k2pi 3; push_cast at this
  simp [this]

lemma I_c1c3 : ∫ x in (0 : ℝ)..2 * π, Real.cos x * Real.cos (3 * x) = 0 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => Real.sin (2 * x) / 4 + Real.sin (4 * x) / 8)
      (Real.cos x * Real.cos (3 * x)) x := by
    intro x
    refine (((hsk 2 x).div_const 4).add ((hsk 4 x).div_const 8)).congr_deriv ?_
    have h := pcc (3 * x) x
    rw [show 3 * x - x = 2 * x by ring, show 3 * x + x = 4 * x by ring] at h
    linear_combination (-1 : ℝ) * h
  rw [int2pi hd (by fun_prop)]
  have h2 := sin_k2pi 2; have h4 := sin_k2pi 4; push_cast at h2 h4
  simp [h2, h4]

lemma I_s1c3 : ∫ x in (0 : ℝ)..2 * π, Real.sin x * Real.cos (3 * x) = 0 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => -(Real.cos (4 * x) / 8) + Real.cos (2 * x) / 4)
      (Real.sin x * Real.cos (3 * x)) x := by
    intro x
    refine ((((hck 4 x).div_const 8).neg).add ((hck 2 x).div_const 4)).congr_deriv ?_
    have h := psc x (3 * x)
    rw [show x + 3 * x = 4 * x by ring, show x - 3 * x = -(2 * x) by ring, Real.sin_neg] at h
    linear_combination (-1 : ℝ) * h
  rw [int2pi hd (by fun_prop)]
  have h2 := cos_k2pi 2; have h4 := cos_k2pi 4; push_cast at h2 h4
  simp [h2, h4]

lemma I_cc3 : ∫ x in (0 : ℝ)..2 * π, Real.cos x ^ 2 * Real.cos (3 * x) = 0 := by
  have hd : ∀ x : ℝ, HasDerivAt
      (fun x => Real.sin (1 * x) / 4 + Real.sin (3 * x) / 6 + Real.sin (5 * x) / 20)
      (Real.cos x ^ 2 * Real.cos (3 * x)) x := by
    intro x
    refine ((((hsk 1 x).div_const 4).add ((hsk 3 x).div_const 6)).add
      ((hsk 5 x).div_const 20)).congr_deriv ?_
    have h := pcc (3 * x) x
    rw [show 3 * x - x = 2 * x by ring, show 3 * x + x = 4 * x by ring] at h
    have h2 := pcc (2 * x) x
    rw [show 2 * x - x = 1 * x by ring, show 2 * x + x = 3 * x by ring] at h2
    have h4 := pcc (4 * x) x
    rw [show 4 * x - x = 3 * x by ring, show 4 * x + x = 5 * x by ring] at h4
    have h1 : Real.cos (1 * x) = Real.cos x := by rw [one_mul]
    linear_combination (-Real.cos x) * h - (1/2 : ℝ) * h2 - (1/2 : ℝ) * h4
  rw [int2pi hd (by fun_prop)]
  have h1 := sin_k2pi 1; have h3 := sin_k2pi 3; have h5 := sin_k2pi 5
  push_cast at h1 h3 h5
  simp [h1, h3, h5]

lemma I_scc3 : ∫ x in (0 : ℝ)..2 * π, Real.sin x * Real.cos x * Real.cos (3 * x) = 0 := by
  have hd : ∀ x : ℝ, HasDerivAt
      (fun x => -(Real.cos (5 * x) / 20) + Real.cos (1 * x) / 4)
      (Real.sin x * Real.cos x * Real.cos (3 * x)) x := by
    intro x
    refine ((((hck 5 x).div_const 20).neg).add ((hck 1 x).div_const 4)).congr_deriv ?_
    have h := pcc (3 * x) x
    rw [show 3 * x - x = 2 * x by ring, show 3 * x + x = 4 * x by ring] at h
    have h2 := psc x (2 * x)
    rw [show x + 2 * x = 3 * x by ring, show x - 2 * x = -(1 * x) by ring, Real.sin_neg] at h2
    have h4 := psc x (4 * x)
    rw [show x + 4 * x = 5 * x by ring, show x - 4 * x = -(3 * x) by ring, Real.sin_neg] at h4
    have h1 : Real.sin (1 * x) = Real.sin x := by rw [one_mul]
    linear_combination (-Real.sin x) * h - (1/2 : ℝ) * h2 - (1/2 : ℝ) * h4
  rw [int2pi hd (by fun_prop)]
  have h1 := cos_k2pi 1; have h5 := cos_k2pi 5
  push_cast at h1 h5
  simp [h1, h5]

lemma I_ssc3 : ∫ x in (0 : ℝ)..2 * π, Real.sin x ^ 2 * Real.cos (3 * x) = 0 := by
  have e : (fun x : ℝ => Real.sin x ^ 2 * Real.cos (3 * x))
      = fun x => Real.cos (3 * x) - Real.cos x ^ 2 * Real.cos (3 * x) := by
    funext x; rw [Real.sin_sq]; ring
  have i1 : IntervalIntegrable (fun x : ℝ => Real.cos (3 * x)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun x : ℝ => Real.cos (3 * x)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => Real.cos x ^ 2 * Real.cos (3 * x)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun x : ℝ => Real.cos x ^ 2 * Real.cos (3 * x)).intervalIntegrable _ _
  rw [e, intervalIntegral.integral_sub i1 i2, I_c3, I_cc3, sub_zero]

lemma I_c3sq : ∫ x in (0 : ℝ)..2 * π, Real.cos (3 * x) ^ 2 = π := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => x / 2 + Real.sin (6 * x) / 12)
      (Real.cos (3 * x) ^ 2) x := by
    intro x
    refine (((hasDerivAt_id' x).div_const 2).add ((hsk 6 x).div_const 12)).congr_deriv ?_
    have h := Real.cos_sq (3 * x)
    rw [show 2 * (3 * x) = 6 * x by ring] at h
    linear_combination (-1 : ℝ) * h
  rw [int2pi hd (by fun_prop)]
  have h6 := sin_k2pi 6; push_cast at h6
  simp [h6]

lemma I_H : ∫ x in (0 : ℝ)..2 * π, Real.cos x * Real.sin x ^ 2 * Real.cos (3 * x) = -(π / 4) := by
  have e : (fun x : ℝ => Real.cos x * Real.sin x ^ 2 * Real.cos (3 * x))
      = fun x => (1 / 4 : ℝ) * (Real.cos x * Real.cos (3 * x)) - (1 / 4 : ℝ) * Real.cos (3 * x) ^ 2 := by
    funext x
    have h3 := Real.cos_three_mul x
    rw [Real.sin_sq]
    linear_combination ((1 / 4 : ℝ) * Real.cos (3 * x)) * h3
  have i1 : IntervalIntegrable (fun x : ℝ => (1 / 4 : ℝ) * (Real.cos x * Real.cos (3 * x)))
      volume 0 (2 * π) := (by fun_prop : Continuous fun x : ℝ =>
      (1 / 4 : ℝ) * (Real.cos x * Real.cos (3 * x))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => (1 / 4 : ℝ) * Real.cos (3 * x) ^ 2) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun x : ℝ => (1 / 4 : ℝ) * Real.cos (3 * x) ^ 2).intervalIntegrable _ _
  rw [e, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, I_c1c3, I_c3sq]
  ring

end trig

section taylor

lemma mvt_bound {k k' : ℝ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε)
    (hk : ∀ t ∈ Set.Icc 0 ε, HasDerivAt k (k' t) t) (hb : ∀ t ∈ Set.Icc 0 ε, |k' t| ≤ C) :
    |k ε - k 0| ≤ C * ε := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := k) (f' := k') (C := C) (a := 0) (b := ε)
    (fun t ht => (hk t ht).hasDerivWithinAt) (fun t ht => by
      simpa [Real.norm_eq_abs] using hb t (Set.Ico_subset_Icc_self ht)) ε ⟨hε, le_rfl⟩
  simpa [Real.norm_eq_abs] using this

lemma taylor1 {g g1 g2 : ℝ → ℝ} {ε B : ℝ} (hε : 0 ≤ ε)
    (hg : ∀ t ∈ Set.Icc 0 ε, HasDerivAt g (g1 t) t)
    (hg1 : ∀ t ∈ Set.Icc 0 ε, HasDerivAt g1 (g2 t) t) (hB : ∀ t ∈ Set.Icc 0 ε, |g2 t| ≤ B) :
    |g ε - g 0 - ε * g1 0| ≤ B * ε ^ 2 := by
  have h1 : ∀ t ∈ Set.Icc 0 ε, |g1 t - g1 0| ≤ B * ε := by
    intro t ht
    have := mvt_bound ht.1 (fun s hs => hg1 s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hB s ⟨hs.1, hs.2.trans ht.2⟩)
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, hε⟩)
    nlinarith [ht.2, mul_le_mul_of_nonneg_left ht.2 hB0]
  have := mvt_bound (k := fun t => g t - g 0 - t * g1 0) (k' := fun t => g1 t - g1 0) (C := B * ε) hε
    (fun t ht => by
      have := ((hg t ht).sub_const (g 0)).sub ((hasDerivAt_id' t).mul_const (g1 0))
      exact this.congr_deriv (by ring)) h1
  simp only [zero_mul, sub_zero, sub_self] at this
  calc |g ε - g 0 - ε * g1 0| ≤ B * ε * ε := this
    _ = B * ε ^ 2 := by ring

lemma taylor2 {g g1 g2 : ℝ → ℝ} {ε M : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hg : ∀ t ∈ Set.Icc 0 ε, HasDerivAt g (g1 t) t)
    (hg1 : ∀ t ∈ Set.Icc 0 ε, HasDerivAt g1 (g2 t) t)
    (hL : ∀ t ∈ Set.Icc 0 ε, |g2 t - g2 0| ≤ M * t) :
    |g1 ε - g1 0 - ε * g2 0| ≤ M * ε ^ 2 ∧
      |g ε - g 0 - ε * g1 0 - ε ^ 2 / 2 * g2 0| ≤ M * ε ^ 3 := by
  have h1 : ∀ t ∈ Set.Icc 0 ε, |g1 t - g1 0 - t * g2 0| ≤ M * ε * t := by
    intro t ht
    have := mvt_bound (k := fun s => g1 s - g1 0 - s * g2 0) (k' := fun s => g2 s - g2 0)
      (C := M * ε) ht.1
      (fun s hs => by
        have := ((hg1 s ⟨hs.1, hs.2.trans ht.2⟩).sub_const (g1 0)).sub
          ((hasDerivAt_id' s).mul_const (g2 0))
        exact this.congr_deriv (by ring))
      (fun s hs => (hL s ⟨hs.1, hs.2.trans ht.2⟩).trans
        (mul_le_mul_of_nonneg_left (hs.2.trans ht.2) hM))
    simpa using this
  refine ⟨by nlinarith [h1 ε ⟨hε, le_rfl⟩], ?_⟩
  have := mvt_bound (k := fun t => g t - g 0 - t * g1 0 - t ^ 2 / 2 * g2 0)
    (k' := fun t => g1 t - g1 0 - t * g2 0) (C := M * ε * ε) hε
    (fun t ht => by
      have := (((hg t ht).sub_const (g 0)).sub ((hasDerivAt_id' t).mul_const (g1 0))).sub
        (((hasDerivAt_pow 2 t).div_const 2).mul_const (g2 0))
      refine this.congr_deriv ?_
      simp)
    (fun t ht => (h1 t ht).trans (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hM hε)))
  simp only [zero_mul, sub_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at this
  calc _ ≤ M * ε * ε * ε := this
    _ = M * ε ^ 3 := by ring

end taylor

section regularity
variable {u : E2 → ℝ} {c : E2} {R0 : ℝ}

lemma reg (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) {y : E2} (hy : y ∈ Metric.ball c R0) :
    DifferentiableAt ℝ u y ∧ DifferentiableAt ℝ (fderiv ℝ u) y ∧ D2 u y b0 b1 = D2 u y b1 b0 := by
  have hcd := hu.contDiffAt (Metric.isOpen_ball.mem_nhds hy)
  refine ⟨hcd.differentiableAt (by simp), ?_, ?_⟩
  · exact ((hu.fderiv_of_isOpen Metric.isOpen_ball (m := 1) (by norm_num)).differentiableOn
      (by simp)).differentiableAt (Metric.isOpen_ball.mem_nhds hy)
  · exact hcd.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) b0 b1

lemma continuous_ev : Continuous ev := by unfold ev; fun_prop
lemma continuous_ep : Continuous ep := by unfold ep; fun_prop

lemma path_mem {r θ : ℝ} (hr0 : 0 ≤ r) (hr : r < R0) : c + r • ev θ ∈ Metric.ball c R0 := by
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_ev, mul_one,
    Real.norm_eq_abs, abs_of_nonneg hr0]
  exact hr

lemma cont_basic (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) {ε R : ℝ} (hε : 0 ≤ ε) (hR : R < R0)
    {V W : ℝ → E2} (hV : Continuous V) (hW : Continuous W) :
    ContinuousOn (fun p : ℝ × ℝ => u (c + p.1 • ev p.2)) (Set.Icc ε R ×ˢ Set.univ) ∧
    ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ u (c + p.1 • ev p.2) (V p.2))
      (Set.Icc ε R ×ˢ Set.univ) ∧
    ContinuousOn (fun p : ℝ × ℝ => D2 u (c + p.1 • ev p.2) (V p.2) (W p.2))
      (Set.Icc ε R ×ˢ Set.univ) := by
  have hγ : Continuous (fun p : ℝ × ℝ => c + p.1 • ev p.2) := by
    have := continuous_ev; fun_prop
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => c + p.1 • ev p.2) (Set.Icc ε R ×ˢ Set.univ)
      (Metric.ball c R0) := fun p hp => path_mem (hε.trans hp.1.1) (hp.1.2.trans_lt hR)
  have cF : ContinuousOn (fun y => fderiv ℝ u y) (Metric.ball c R0) :=
    hu.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have cD : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ u) y) (Metric.ball c R0) :=
    (hu.fderiv_of_isOpen Metric.isOpen_ball (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
      Metric.isOpen_ball le_rfl
  refine ⟨hu.continuousOn.comp hγ.continuousOn hmap, ?_, ?_⟩
  · exact (cF.comp hγ.continuousOn hmap).clm_apply (hV.comp continuous_snd).continuousOn
  · exact ((cD.comp hγ.continuousOn hmap).clm_apply (hV.comp continuous_snd).continuousOn).clm_apply
      (hW.comp continuous_snd).continuousOn

end regularity

section core
variable {u : E2 → ℝ} {c : E2} {R0 lam : ℝ}

noncomputable def dpsi (u : E2 → ℝ) (c : E2) (r θ : ℝ) : ℝ :=
  (r ^ 2 * D2 u (c + r • ev θ) (ev θ) (ev θ) + r * fderiv ℝ u (c + r • ev θ) (ev θ)
    - 9 * u (c + r • ev θ)) * Real.cos (3 * θ) / r ^ 4

noncomputable def dchi (u : E2 → ℝ) (c : E2) (r θ : ℝ) : ℝ :=
  (r ^ 2 * D2 u (c + r • ev θ) (ep θ) (ep θ) - r * fderiv ℝ u (c + r • ev θ) (ev θ)
    + 9 * u (c + r • ev θ)) * Real.cos (3 * θ) / r ^ 4

noncomputable def Sf (u : E2 → ℝ) (c : E2) (lam r θ : ℝ) : ℝ :=
  (2 * lam * u (c + r • ev θ) - 2 * (r * Real.cos θ * Real.sin θ ^ 2)) * Real.cos (3 * θ) / r ^ 2

lemma pt_id (hu : ContDiffOn ℝ 2 u (Metric.ball c R0))
    (hpde : ∀ r ∈ Set.Ioo 0 R0, ∀ θ : ℝ, D2 u (c + r • ev θ) b0 b0 + D2 u (c + r • ev θ) b1 b1
      = 2 * lam * u (c + r • ev θ) - 2 * (r * Real.cos θ * Real.sin θ ^ 2))
    {r θ : ℝ} (hr : 0 < r) (hrR : r < R0) :
    dpsi u c r θ + dchi u c r θ = Sf u c lam r θ := by
  have hq := path_mem (c := c) (θ := θ) hr.le hrR
  obtain ⟨-, -, hsym⟩ := reg hu hq
  have ht := trace_rot (D2 u (c + r • ev θ)) hsym θ
  have hp := hpde r ⟨hr, hrR⟩ θ
  calc dpsi u c r θ + dchi u c r θ
      = (D2 u (c + r • ev θ) (ev θ) (ev θ) + D2 u (c + r • ev θ) (ep θ) (ep θ))
          * Real.cos (3 * θ) / r ^ 2 := by
        unfold dpsi dchi; field_simp; ring
    _ = Sf u c lam r θ := by rw [ht, hp]; rfl

lemma slice_r {F : ℝ × ℝ → ℝ} {ε R : ℝ} (h : ContinuousOn F (Set.Icc ε R ×ˢ Set.univ)) (θ : ℝ) :
    ContinuousOn (fun r => F (r, θ)) (Set.Icc ε R) :=
  h.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hr => ⟨hr, trivial⟩)

lemma slice_t {F : ℝ × ℝ → ℝ} {ε R : ℝ} (h : ContinuousOn F (Set.Icc ε R ×ˢ Set.univ)) {r : ℝ}
    (hr : r ∈ Set.Icc ε R) : Continuous (fun θ => F (r, θ)) :=
  continuousOn_univ.mp (h.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨hr, trivial⟩))

lemma cont_param {F : ℝ × ℝ → ℝ} {ε R : ℝ} (h : ContinuousOn F (Set.Icc ε R ×ˢ Set.univ))
    (a b : ℝ) : ContinuousOn (fun r => ∫ θ in a..b, F (r, θ)) (Set.Icc ε R) := by
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous (Function.uncurry fun (x : Set.Icc ε R) (t : ℝ) => F (x.1, t)) :=
    h.comp_continuous (f := fun q : Set.Icc ε R × ℝ => ((q.1 : ℝ), q.2)) (by fun_prop)
      (fun q => ⟨q.1.2, trivial⟩)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc a b

lemma joint (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) {ε R : ℝ} (hε : 0 < ε) (hR : R < R0) :
    ContinuousOn (fun p : ℝ × ℝ => psi u c p.1 p.2) (Set.Icc ε R ×ˢ Set.univ) ∧
    ContinuousOn (fun p : ℝ × ℝ => dpsi u c p.1 p.2) (Set.Icc ε R ×ˢ Set.univ) ∧
    ContinuousOn (fun p : ℝ × ℝ => dchi u c p.1 p.2) (Set.Icc ε R ×ˢ Set.univ) ∧
    ContinuousOn (fun p : ℝ × ℝ => Sf u c lam p.1 p.2) (Set.Icc ε R ×ˢ Set.univ) := by
  have hb := cont_basic hu hε.le hR continuous_ev continuous_ev
  have hb' := cont_basic hu hε.le hR continuous_ep continuous_ep
  have cfst : ContinuousOn (fun p : ℝ × ℝ => p.1) (Set.Icc ε R ×ˢ Set.univ) :=
    continuous_fst.continuousOn
  have ccos : ContinuousOn (fun p : ℝ × ℝ => Real.cos (3 * p.2)) (Set.Icc ε R ×ˢ Set.univ) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos (3 * p.2)).continuousOn
  have ctr : ContinuousOn (fun p : ℝ × ℝ => p.1 * Real.cos p.2 * Real.sin p.2 ^ 2)
      (Set.Icc ε R ×ˢ Set.univ) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => p.1 * Real.cos p.2 * Real.sin p.2 ^ 2).continuousOn
  have hne : ∀ k : ℕ, ∀ p ∈ Set.Icc ε R ×ˢ (Set.univ : Set ℝ), p.1 ^ k ≠ 0 :=
    fun k p hp => pow_ne_zero k (ne_of_gt (hε.trans_le hp.1.1))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((cfst.mul hb.2.1).add (continuousOn_const.mul hb.1)).mul ccos).div (cfst.pow 3) (hne 3)
  · exact (((((cfst.pow 2).mul hb.2.2).add (cfst.mul hb.2.1)).sub
      (continuousOn_const.mul hb.1)).mul ccos).div (cfst.pow 4) (hne 4)
  · exact (((((cfst.pow 2).mul hb'.2.2).sub (cfst.mul hb.2.1)).add
      (continuousOn_const.mul hb.1)).mul ccos).div (cfst.pow 4) (hne 4)
  · exact ((((continuousOn_const.mul hb.1)).sub (continuousOn_const.mul ctr)).mul ccos).div
      (cfst.pow 2) (hne 2)

lemma chi_period (r : ℝ) : chi u c r (2 * π) = chi u c r 0 := by
  unfold chi
  rw [ev_two_pi, ep_two_pi, show 3 * (2 * π) = (3 : ℕ) * (2 * π) by push_cast; ring,
    cos_k2pi, sin_k2pi]
  simp

lemma psi_deriv' (c : E2) {r θ : ℝ} (hr : r ≠ 0)
    (h1 : DifferentiableAt ℝ u (c + r • ev θ))
    (h2 : DifferentiableAt ℝ (fderiv ℝ u) (c + r • ev θ)) :
    HasDerivAt (fun s => psi u c s θ) (dpsi u c r θ) r := psi_deriv c hr h1 h2

lemma chi_deriv' (c : E2) {r θ : ℝ} (hr : r ≠ 0)
    (h1 : DifferentiableAt ℝ u (c + r • ev θ))
    (h2 : DifferentiableAt ℝ (fderiv ℝ u) (c + r • ev θ)) :
    HasDerivAt (fun t => chi u c r t) (dchi u c r θ) θ := chi_deriv c hr h1 h2

lemma hreg_of (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) {ε R : ℝ} (hε : 0 < ε) (hR : R < R0)
    {r : ℝ} (hr : r ∈ Set.Icc ε R) (θ : ℝ) : DifferentiableAt ℝ u (c + r • ev θ) ∧
      DifferentiableAt ℝ (fderiv ℝ u) (c + r • ev θ) :=
  let h := reg hu (path_mem (θ := θ) (hε.le.trans hr.1) (hr.2.trans_lt hR)); ⟨h.1, h.2.1⟩

lemma step1 (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (hR : R < R0) (θ : ℝ) : psi u c R θ - psi u c ε θ = ∫ r in ε..R, dpsi u c r θ := by
  have jdpsi := (joint (lam := 0) hu hε hR).2.1
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => psi u c s θ)
    (fun r hr => ?_) ((slice_r jdpsi θ).intervalIntegrable_of_Icc hεR)).symm
  rw [Set.uIcc_of_le hεR] at hr
  exact psi_deriv' c (ne_of_gt (hε.trans_le hr.1)) (hreg_of hu hε hR hr θ).1
    (hreg_of hu hε hR hr θ).2

lemma step3 (hu : ContDiffOn ℝ 2 u (Metric.ball c R0))
    (hpde : ∀ r ∈ Set.Ioo 0 R0, ∀ θ : ℝ, D2 u (c + r • ev θ) b0 b0 + D2 u (c + r • ev θ) b1 b1
      = 2 * lam * u (c + r • ev θ) - 2 * (r * Real.cos θ * Real.sin θ ^ 2))
    {ε R : ℝ} (hε : 0 < ε) (hR : R < R0) {r : ℝ} (hr : r ∈ Set.Icc ε R) :
    ∫ θ in (0 : ℝ)..2 * π, dpsi u c r θ = ∫ θ in (0 : ℝ)..2 * π, Sf u c lam r θ := by
  obtain ⟨-, -, jdchi, jS⟩ := joint (lam := lam) hu hε hR
  have hr0 : 0 < r := hε.trans_le hr.1
  have hchi : ∫ θ in (0 : ℝ)..2 * π, dchi u c r θ = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => chi u c r t)
      (fun θ _ => chi_deriv' c (ne_of_gt hr0) (hreg_of hu hε hR hr θ).1 (hreg_of hu hε hR hr θ).2)
      ((slice_t jdchi hr).intervalIntegrable _ _), chi_period, sub_self]
  have e : (fun θ => dpsi u c r θ) = fun θ => Sf u c lam r θ - dchi u c r θ := by
    funext θ; rw [← pt_id hu hpde hr0 (hr.2.trans_lt hR)]; ring
  rw [e, intervalIntegral.integral_sub ((slice_t jS hr).intervalIntegrable _ _)
    ((slice_t jdchi hr).intervalIntegrable _ _), hchi, sub_zero]

lemma swap_gen {F : ℝ × ℝ → ℝ} {ε R : ℝ} (hεR : ε ≤ R)
    (h : ContinuousOn F (Set.Icc ε R ×ˢ Set.univ)) :
    ∫ θ in (0 : ℝ)..2 * π, ∫ r in ε..R, F (r, θ) = ∫ r in ε..R, ∫ θ in (0 : ℝ)..2 * π, F (r, θ) := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => F (q.2, q.1)) (Set.Icc 0 (2 * π) ×ˢ Set.Icc ε R) :=
    h.comp continuous_swap.continuousOn (fun q hq => ⟨hq.2, trivial⟩)
  have hI : IntegrableOn (fun q : ℝ × ℝ => F (q.2, q.1))
      (Set.uIoc 0 (2 * π) ×ˢ Set.uIoc ε R) := by
    refine (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set ?_
    rw [Set.uIoc_of_le (by positivity), Set.uIoc_of_le hεR]
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  exact intervalIntegral_intervalIntegral_swap (F := fun θ r => F (r, θ)) hI

lemma swap_dpsi (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (hR : R < R0) : ∫ θ in (0 : ℝ)..2 * π, ∫ r in ε..R, dpsi u c r θ
      = ∫ r in ε..R, ∫ θ in (0 : ℝ)..2 * π, dpsi u c r θ :=
  swap_gen hεR (joint (lam := 0) hu hε hR).2.1

lemma KI (hu : ContDiffOn ℝ 2 u (Metric.ball c R0))
    (hpde : ∀ r ∈ Set.Ioo 0 R0, ∀ θ : ℝ, D2 u (c + r • ev θ) b0 b0 + D2 u (c + r • ev θ) b1 b1
      = 2 * lam * u (c + r • ev θ) - 2 * (r * Real.cos θ * Real.sin θ ^ 2))
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (hR : R < R0) :
    (∫ θ in (0 : ℝ)..2 * π, psi u c R θ) - (∫ θ in (0 : ℝ)..2 * π, psi u c ε θ)
      = ∫ r in ε..R, ∫ θ in (0 : ℝ)..2 * π, Sf u c lam r θ := by
  have jpsi := (joint (lam := 0) hu hε hR).1
  rw [← intervalIntegral.integral_sub ((slice_t jpsi ⟨hεR, le_rfl⟩).intervalIntegrable _ _)
    ((slice_t jpsi ⟨le_rfl, hεR⟩).intervalIntegrable _ _)]
  have e : (fun θ => psi u c R θ - psi u c ε θ) = fun θ => ∫ r in ε..R, dpsi u c r θ :=
    funext (step1 hu hε hεR hR)
  rw [e, swap_dpsi hu hε hεR hR]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [Set.uIcc_of_le hεR] at hr
  exact step3 hu hpde hε hR hr

end core

section bounds
variable {u : E2 → ℝ} {c : E2} {R0 lam : ℝ}

lemma exp1 (L : E2 →L[ℝ] ℝ) (θ : ℝ) : L (ev θ) = Real.cos θ * L b0 + Real.sin θ * L b1 := by
  simp [ev, map_add, map_smul]

lemma exp2 (B : E2 →L[ℝ] E2 →L[ℝ] ℝ) (θ : ℝ) : B (ev θ) (ev θ) = Real.cos θ ^ 2 * B b0 b0
    + Real.sin θ * Real.cos θ * (B b0 b1 + B b1 b0) + Real.sin θ ^ 2 * B b1 b1 := by
  simp only [ev, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  ring

lemma int_lin {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (k : ℝ)
    (h1 : ∫ x in (0 : ℝ)..2 * π, f x = 0) (h2 : ∫ x in (0 : ℝ)..2 * π, g x = 0) :
    ∫ x in (0 : ℝ)..2 * π, (k * f x + g x) = 0 := by
  rw [intervalIntegral.integral_add ((hf.const_mul k).intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), intervalIntegral.integral_const_mul, h1, h2]
  ring

lemma int_cm {f : ℝ → ℝ} (k : ℝ) (h1 : ∫ x in (0 : ℝ)..2 * π, f x = 0) :
    ∫ x in (0 : ℝ)..2 * π, k * f x = 0 := by
  rw [intervalIntegral.integral_const_mul, h1, mul_zero]

lemma lin_orth (A a0 a1 : ℝ) : ∫ θ in (0 : ℝ)..2 * π,
    (A + (Real.cos θ * a0 + Real.sin θ * a1)) * Real.cos (3 * θ) = 0 := by
  have e : (fun θ : ℝ => (A + (Real.cos θ * a0 + Real.sin θ * a1)) * Real.cos (3 * θ))
      = fun θ => A * Real.cos (3 * θ) + (a0 * (Real.cos θ * Real.cos (3 * θ))
        + a1 * (Real.sin θ * Real.cos (3 * θ))) := by funext θ; ring
  rw [e]
  exact int_lin (by fun_prop) (by fun_prop) _ I_c3
    (int_lin (by fun_prop) (by fun_prop) _ I_c1c3 (int_cm _ I_s1c3))

lemma T_orth (A a0 a1 B00 B01 B11 : ℝ) : ∫ θ in (0 : ℝ)..2 * π,
    (A + (Real.cos θ * a0 + Real.sin θ * a1) + (Real.cos θ ^ 2 * B00
      + Real.sin θ * Real.cos θ * B01 + Real.sin θ ^ 2 * B11)) * Real.cos (3 * θ) = 0 := by
  have e : (fun θ : ℝ => (A + (Real.cos θ * a0 + Real.sin θ * a1) + (Real.cos θ ^ 2 * B00
      + Real.sin θ * Real.cos θ * B01 + Real.sin θ ^ 2 * B11)) * Real.cos (3 * θ))
      = fun θ => A * Real.cos (3 * θ) + (a0 * (Real.cos θ * Real.cos (3 * θ))
        + (a1 * (Real.sin θ * Real.cos (3 * θ)) + (B00 * (Real.cos θ ^ 2 * Real.cos (3 * θ))
        + (B01 * (Real.sin θ * Real.cos θ * Real.cos (3 * θ))
        + B11 * (Real.sin θ ^ 2 * Real.cos (3 * θ)))))) := by funext θ; ring
  rw [e]
  exact int_lin (by fun_prop) (by fun_prop) _ I_c3
    (int_lin (by fun_prop) (by fun_prop) _ I_c1c3
    (int_lin (by fun_prop) (by fun_prop) _ I_s1c3
    (int_lin (by fun_prop) (by fun_prop) _ I_cc3
    (int_lin (by fun_prop) (by fun_prop) _ I_scc3 (int_cm _ I_ssc3)))))

lemma ray (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) (θ : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < R0) :
    HasDerivAt (fun s => u (c + s • ev θ)) (fderiv ℝ u (c + t • ev θ) (ev θ)) t ∧
    HasDerivAt (fun s => fderiv ℝ u (c + s • ev θ) (ev θ)) (D2 u (c + t • ev θ) (ev θ) (ev θ)) t := by
  obtain ⟨h1, h2, -⟩ := reg hu (path_mem (θ := θ) ht0 ht)
  have hγ : HasDerivAt (fun s : ℝ => c + s • ev θ) (ev θ) t := by
    simpa using ((hasDerivAt_id t).smul_const (ev θ)).const_add c
  refine ⟨hasDerivAt_u_path hγ h1, ?_⟩
  exact (hasDerivAt_du_path (V := fun _ => ev θ) (V' := 0) hγ (hasDerivAt_const _ _) h2).congr_deriv
    (by simp [D2])

lemma A_bound (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) {B : ℝ}
    (hB : ∀ y ∈ Metric.ball c R0, ∀ θ : ℝ, |D2 u y (ev θ) (ev θ)| ≤ B) {r : ℝ} (hr0 : 0 < r)
    (hr : r < R0) :
    |∫ θ in (0 : ℝ)..2 * π, u (c + r • ev θ) * Real.cos (3 * θ)| ≤ B * r ^ 2 * (2 * π) := by
  have hb := cont_basic hu (ε := r) (R := r) hr0.le hr continuous_ev continuous_ev
  have hU : Continuous fun θ => u (c + r • ev θ) := slice_t hb.1 ⟨le_rfl, le_rfl⟩
  have hL : Continuous fun θ => u c + r * fderiv ℝ u c (ev θ) :=
    continuous_const.add (continuous_const.mul ((fderiv ℝ u c).continuous.comp continuous_ev))
  have h0 : ∫ θ in (0 : ℝ)..2 * π, (u c + r * fderiv ℝ u c (ev θ)) * Real.cos (3 * θ) = 0 := by
    have := lin_orth (u c) (r * fderiv ℝ u c b0) (r * fderiv ℝ u c b1)
    rw [← this]; congr 1; funext θ; rw [exp1]; ring
  have hsplit : ∫ θ in (0 : ℝ)..2 * π, u (c + r • ev θ) * Real.cos (3 * θ)
      = ∫ θ in (0 : ℝ)..2 * π, (u (c + r • ev θ) - (u c + r * fderiv ℝ u c (ev θ)))
          * Real.cos (3 * θ) := by
    have i1 : IntervalIntegrable (fun θ => u (c + r • ev θ) * Real.cos (3 * θ)) volume 0 (2 * π) :=
      (hU.mul (by fun_prop : Continuous fun θ : ℝ => Real.cos (3 * θ))).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => (u c + r * fderiv ℝ u c (ev θ)) * Real.cos (3 * θ))
        volume 0 (2 * π) :=
      (hL.mul (by fun_prop : Continuous fun θ : ℝ => Real.cos (3 * θ))).intervalIntegrable _ _
    calc _ = (∫ θ in (0 : ℝ)..2 * π, u (c + r • ev θ) * Real.cos (3 * θ))
          - ∫ θ in (0 : ℝ)..2 * π, (u c + r * fderiv ℝ u c (ev θ)) * Real.cos (3 * θ) := by
          rw [h0, sub_zero]
      _ = _ := (intervalIntegral.integral_sub i1 i2).symm
      _ = _ := by congr 1; funext θ; ring
  rw [hsplit]
  have hpt : ∀ θ : ℝ, |(u (c + r • ev θ) - (u c + r * fderiv ℝ u c (ev θ))) * Real.cos (3 * θ)|
      ≤ B * r ^ 2 := by
    intro θ
    have ht := taylor1 (g := fun s => u (c + s • ev θ)) (g1 := fun s => fderiv ℝ u (c + s • ev θ) (ev θ))
      (g2 := fun s => D2 u (c + s • ev θ) (ev θ) (ev θ)) (ε := r) (B := B) hr0.le
      (fun t ht => (ray hu θ ht.1 (ht.2.trans_lt hr)).1)
      (fun t ht => (ray hu θ ht.1 (ht.2.trans_lt hr)).2)
      (fun t ht => hB _ (path_mem ht.1 (ht.2.trans_lt hr)) θ)
    simp only [zero_smul, add_zero] at ht
    rw [abs_mul]
    have hc3 := Real.abs_cos_le_one (3 * θ)
    have hB0 : 0 ≤ B * r ^ 2 := (abs_nonneg _).trans ht
    calc |u (c + r • ev θ) - (u c + r * fderiv ℝ u c (ev θ))| * |Real.cos (3 * θ)|
        ≤ (B * r ^ 2) * 1 := by
          apply mul_le_mul _ hc3 (abs_nonneg _) hB0
          rw [show u (c + r • ev θ) - (u c + r * fderiv ℝ u c (ev θ))
            = u (c + r • ev θ) - u c - r * fderiv ℝ u c (ev θ) by ring]
          exact ht
      _ = B * r ^ 2 := mul_one _
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (f := fun θ => (u (c + r • ev θ) - (u c + r * fderiv ℝ u c (ev θ))) * Real.cos (3 * θ))
    (C := B * r ^ 2) (fun θ _ => by rw [Real.norm_eq_abs]; exact hpt θ)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos (show (0:ℝ) < 2 * π by positivity)] at this
  exact this

lemma Psi_bound (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ Metric.ball c R0, ∀ θ : ℝ,
      |D2 u y (ev θ) (ev θ) - D2 u c (ev θ) (ev θ)| ≤ M * ‖y - c‖)
    {ε : ℝ} (hε : 0 < ε) (hεR : ε < R0) :
    |∫ θ in (0 : ℝ)..2 * π, psi u c ε θ| ≤ 8 * π * M := by
  have hb := cont_basic hu (ε := ε) (R := ε) hε.le hεR continuous_ev continuous_ev
  have hU : Continuous fun θ => u (c + ε • ev θ) := slice_t hb.1 ⟨le_rfl, le_rfl⟩
  have hG : Continuous fun θ => fderiv ℝ u (c + ε • ev θ) (ev θ) := slice_t hb.2.1 ⟨le_rfl, le_rfl⟩
  set T : ℝ → ℝ := fun θ => 3 * u c + 4 * ε * fderiv ℝ u c (ev θ)
    + 5 / 2 * ε ^ 2 * D2 u c (ev θ) (ev θ) with hT
  have hTc : Continuous T := by
    have h1 := (fderiv ℝ u c).continuous.comp continuous_ev
    have h2 : Continuous fun θ => D2 u c (ev θ) (ev θ) :=
      ((D2 u c).continuous.comp continuous_ev).clm_apply continuous_ev
    simp only [hT]; fun_prop
  have h0 : ∫ θ in (0 : ℝ)..2 * π, T θ * Real.cos (3 * θ) = 0 := by
    have := T_orth (3 * u c) (4 * ε * fderiv ℝ u c b0) (4 * ε * fderiv ℝ u c b1)
      (5 / 2 * ε ^ 2 * D2 u c b0 b0) (5 / 2 * ε ^ 2 * (D2 u c b0 b1 + D2 u c b1 b0))
      (5 / 2 * ε ^ 2 * D2 u c b1 b1)
    rw [← this]; congr 1; funext θ; simp only [hT]; rw [exp1, exp2]; ring
  have hX : Continuous fun θ => ε * fderiv ℝ u (c + ε • ev θ) (ev θ) + 3 * u (c + ε • ev θ) :=
    (continuous_const.mul hG).add (continuous_const.mul hU)
  have hpsi : ∫ θ in (0 : ℝ)..2 * π, psi u c ε θ
      = (∫ θ in (0 : ℝ)..2 * π, ((ε * fderiv ℝ u (c + ε • ev θ) (ev θ) + 3 * u (c + ε • ev θ))
          - T θ) * Real.cos (3 * θ)) / ε ^ 3 := by
    unfold psi
    rw [intervalIntegral.integral_div]
    congr 1
    have i1 : IntervalIntegrable (fun θ => (ε * fderiv ℝ u (c + ε • ev θ) (ev θ)
        + 3 * u (c + ε • ev θ)) * Real.cos (3 * θ)) volume 0 (2 * π) :=
      (hX.mul (by fun_prop : Continuous fun θ : ℝ => Real.cos (3 * θ))).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => T θ * Real.cos (3 * θ)) volume 0 (2 * π) :=
      (hTc.mul (by fun_prop : Continuous fun θ : ℝ => Real.cos (3 * θ))).intervalIntegrable _ _
    calc _ = (∫ θ in (0 : ℝ)..2 * π, (ε * fderiv ℝ u (c + ε • ev θ) (ev θ)
          + 3 * u (c + ε • ev θ)) * Real.cos (3 * θ))
          - ∫ θ in (0 : ℝ)..2 * π, T θ * Real.cos (3 * θ) := by rw [h0, sub_zero]
      _ = _ := (intervalIntegral.integral_sub i1 i2).symm
      _ = _ := by congr 1; funext θ; ring
  have hpt : ∀ θ : ℝ, |((ε * fderiv ℝ u (c + ε • ev θ) (ev θ) + 3 * u (c + ε • ev θ)) - T θ)
      * Real.cos (3 * θ)| ≤ 4 * M * ε ^ 3 := by
    intro θ
    have ht := taylor2 (g := fun s => u (c + s • ev θ))
      (g1 := fun s => fderiv ℝ u (c + s • ev θ) (ev θ))
      (g2 := fun s => D2 u (c + s • ev θ) (ev θ) (ev θ)) (ε := ε) (M := M) hε.le hM0
      (fun t ht => (ray hu θ ht.1 (ht.2.trans_lt hεR)).1)
      (fun t ht => (ray hu θ ht.1 (ht.2.trans_lt hεR)).2)
      (fun t ht => by
        have := hM _ (path_mem (θ := θ) ht.1 (ht.2.trans_lt hεR)) θ
        rw [add_sub_cancel_left, norm_smul, norm_ev, mul_one, Real.norm_eq_abs,
          abs_of_nonneg ht.1] at this
        simpa using this)
    simp only [zero_smul, add_zero] at ht
    obtain ⟨ht1, ht2⟩ := ht
    rw [abs_mul]
    have hc3 := Real.abs_cos_le_one (3 * θ)
    have hE : (ε * fderiv ℝ u (c + ε • ev θ) (ev θ) + 3 * u (c + ε • ev θ)) - T θ
        = ε * (fderiv ℝ u (c + ε • ev θ) (ev θ) - fderiv ℝ u c (ev θ) - ε * D2 u c (ev θ) (ev θ))
          + 3 * (u (c + ε • ev θ) - u c - ε * fderiv ℝ u c (ev θ)
            - ε ^ 2 / 2 * D2 u c (ev θ) (ev θ)) := by simp only [hT]; ring
    have hbd : |(ε * fderiv ℝ u (c + ε • ev θ) (ev θ) + 3 * u (c + ε • ev θ)) - T θ|
        ≤ 4 * M * ε ^ 3 := by
      rw [hE]
      calc _ ≤ |ε * (fderiv ℝ u (c + ε • ev θ) (ev θ) - fderiv ℝ u c (ev θ)
              - ε * D2 u c (ev θ) (ev θ))| + |3 * (u (c + ε • ev θ) - u c
              - ε * fderiv ℝ u c (ev θ) - ε ^ 2 / 2 * D2 u c (ev θ) (ev θ))| := abs_add_le _ _
        _ ≤ ε * (M * ε ^ 2) + 3 * (M * ε ^ 3) := by
            rw [abs_mul, abs_mul, abs_of_pos hε, abs_of_pos (by norm_num : (0:ℝ) < 3)]
            gcongr
        _ = 4 * M * ε ^ 3 := by ring
    calc _ ≤ (4 * M * ε ^ 3) * 1 :=
          mul_le_mul hbd hc3 (abs_nonneg _) (by positivity)
      _ = 4 * M * ε ^ 3 := mul_one _
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (f := fun θ => ((ε * fderiv ℝ u (c + ε • ev θ) (ev θ) + 3 * u (c + ε • ev θ)) - T θ)
      * Real.cos (3 * θ)) (C := 4 * M * ε ^ 3) (fun θ _ => by rw [Real.norm_eq_abs]; exact hpt θ)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos (show (0:ℝ) < 2 * π by positivity)] at this
  rw [hpsi, abs_div, abs_of_pos (by positivity : (0:ℝ) < ε ^ 3), div_le_iff₀ (by positivity)]
  calc _ ≤ 4 * M * ε ^ 3 * (2 * π) := this
    _ = 8 * π * M * ε ^ 3 := by ring

end bounds

section final
variable {u : E2 → ℝ} {c : E2} {R0 lam : ℝ}

lemma S_lower (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) {B : ℝ}
    (hB : ∀ y ∈ Metric.ball c R0, ∀ θ : ℝ, |D2 u y (ev θ) (ev θ)| ≤ B) {r : ℝ} (hr0 : 0 < r)
    (hr : r < R0) :
    π / 2 * r⁻¹ - 2 * |lam| * (B * (2 * π)) ≤ ∫ θ in (0 : ℝ)..2 * π, Sf u c lam r θ := by
  have hb := cont_basic hu (ε := r) (R := r) hr0.le hr continuous_ev continuous_ev
  have hU : Continuous fun θ => u (c + r • ev θ) := slice_t hb.1 ⟨le_rfl, le_rfl⟩
  have e : (fun θ => Sf u c lam r θ) = fun θ => (2 * lam / r ^ 2) * (u (c + r • ev θ)
      * Real.cos (3 * θ)) - (2 / r) * (Real.cos θ * Real.sin θ ^ 2 * Real.cos (3 * θ)) := by
    funext θ; unfold Sf; field_simp
  have i1 : IntervalIntegrable (fun θ => (2 * lam / r ^ 2) * (u (c + r • ev θ) * Real.cos (3 * θ)))
      volume 0 (2 * π) :=
    (continuous_const.mul (hU.mul (by fun_prop : Continuous fun θ : ℝ => Real.cos (3 * θ)))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => (2 / r) * (Real.cos θ * Real.sin θ ^ 2 * Real.cos (3 * θ)))
      volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ : ℝ =>
      (2 / r) * (Real.cos θ * Real.sin θ ^ 2 * Real.cos (3 * θ))).intervalIntegrable _ _
  rw [e, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, I_H]
  have hA := A_bound hu hB hr0 hr
  set A := ∫ θ in (0 : ℝ)..2 * π, u (c + r • ev θ) * Real.cos (3 * θ)
  have hk : |2 * lam / r ^ 2 * A| ≤ 2 * |lam| * (B * (2 * π)) := by
    rw [abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_pos (by positivity : (0:ℝ) < r ^ 2)]
    calc 2 * |lam| / r ^ 2 * |A| ≤ 2 * |lam| / r ^ 2 * (B * r ^ 2 * (2 * π)) := by gcongr
      _ = 2 * |lam| * (B * (2 * π)) := by field_simp
  have h2 : 2 / r * -(π / 4) = -(π / 2 * r⁻¹) := by field_simp; ring
  rw [h2]
  linarith [neg_abs_le (2 * lam / r ^ 2 * A)]

theorem core_false (hu : ContDiffOn ℝ 2 u (Metric.ball c R0)) (hR0 : 0 < R0) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ Metric.ball c R0, ∀ θ : ℝ,
      |D2 u y (ev θ) (ev θ) - D2 u c (ev θ) (ev θ)| ≤ M * ‖y - c‖)
    (hpde : ∀ r ∈ Set.Ioo 0 R0, ∀ θ : ℝ, D2 u (c + r • ev θ) b0 b0 + D2 u (c + r • ev θ) b1 b1
      = 2 * lam * u (c + r • ev θ) - 2 * (r * Real.cos θ * Real.sin θ ^ 2)) : False := by
  set R := R0 / 2 with hRdef
  have hRpos : 0 < R := by positivity
  have hR : R < R0 := by linarith
  set B := ‖D2 u c‖ + M * R0 with hBdef
  have hB : ∀ y ∈ Metric.ball c R0, ∀ θ : ℝ, |D2 u y (ev θ) (ev θ)| ≤ B := by
    intro y hy θ
    have h1 := hM y hy θ
    have h2 : |D2 u c (ev θ) (ev θ)| ≤ ‖D2 u c‖ := by
      have := (D2 u c).le_opNorm₂ (ev θ) (ev θ)
      rwa [norm_ev, mul_one, mul_one, Real.norm_eq_abs] at this
    have h3 : ‖y - c‖ < R0 := by rw [← dist_eq_norm]; exact hy
    have h4 := abs_sub_abs_le_abs_sub (D2 u y (ev θ) (ev θ)) (D2 u c (ev θ) (ev θ))
    nlinarith [mul_le_mul_of_nonneg_left h3.le hM0]
  have hB0 : 0 ≤ B := by positivity
  set K1 := 2 * |lam| * (B * (2 * π)) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set C0 := |∫ θ in (0 : ℝ)..2 * π, psi u c R θ| + 8 * π * M + K1 * R with hC0
  have hC00 : 0 ≤ C0 := by positivity
  set N := 2 / π * C0 + 1 with hN
  have hNpos : 0 < N := by positivity
  set ε := R * Real.exp (-N) with hεdef
  have hε : 0 < ε := by positivity
  have hεR : ε ≤ R := by
    have : Real.exp (-N) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc ε = R * Real.exp (-N) := rfl
      _ ≤ R * 1 := by gcongr
      _ = R := mul_one R
  have hKI := KI (lam := lam) hu hpde hε hεR hR
  have hPsi := Psi_bound hu hM0 hM hε (hεR.trans_lt hR)
  have jS := (joint (lam := lam) hu hε hR).2.2.2
  have hg : IntervalIntegrable (fun r => ∫ θ in (0 : ℝ)..2 * π, Sf u c lam r θ) volume ε R :=
    (cont_param jS 0 (2 * π)).intervalIntegrable_of_Icc hεR
  have hf : IntervalIntegrable (fun r : ℝ => π / 2 * r⁻¹ - K1) volume ε R := by
    refine ContinuousOn.intervalIntegrable_of_Icc hεR ?_
    exact (continuousOn_const.mul (continuousOn_id.inv₀ (fun x hx => ne_of_gt
      (hε.trans_le hx.1)))).sub continuousOn_const
  have hmono := intervalIntegral.integral_mono_on hεR hf hg
    (fun r hr => S_lower hu hB (hε.trans_le hr.1) (hr.2.trans_lt hR))
  have hcomp : ∫ r in ε..R, (π / 2 * r⁻¹ - K1) = π / 2 * Real.log (R / ε) - K1 * (R - ε) := by
    have i1 : IntervalIntegrable (fun r : ℝ => π / 2 * r⁻¹) volume ε R :=
      ContinuousOn.intervalIntegrable_of_Icc hεR (continuousOn_const.mul
        (continuousOn_inv₀.mono fun x hx => (ne_of_gt (hε.trans_le hx.1))))
    rw [intervalIntegral.integral_sub i1 intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_inv_of_pos hε hRpos,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hlog : Real.log (R / ε) = N := by
    rw [hεdef, div_mul_eq_div_div, div_self (ne_of_gt hRpos), one_div, ← Real.exp_neg, neg_neg,
      Real.log_exp]
  rw [hcomp, hlog] at hmono
  have h1 : π / 2 * N = C0 + π / 2 := by
    rw [hN]; field_simp
  have h2 : K1 * (R - ε) ≤ K1 * R := by nlinarith
  have h3 := neg_abs_le (∫ θ in (0 : ℝ)..2 * π, psi u c ε θ)
  have h4 := le_abs_self (∫ θ in (0 : ℝ)..2 * π, psi u c R θ)
  have hpi : 0 < π := Real.pi_pos
  nlinarith

end final

section glue

noncomputable def Gq (a b : ℝ) : ℝ := a * b ^ 2 / (a ^ 2 + b ^ 2)

lemma Gq_lip1 (a a' b : ℝ) : |Gq a b - Gq a' b| ≤ |a - a'| := by
  unfold Gq
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have h1 : 0 < a ^ 2 + b ^ 2 := by positivity
  have h2 : 0 < a' ^ 2 + b ^ 2 := by positivity
  rw [div_sub_div _ _ h1.ne' h2.ne', abs_div, abs_of_pos (mul_pos h1 h2), div_le_iff₀ (mul_pos h1 h2)]
  have e : a * b ^ 2 * (a' ^ 2 + b ^ 2) - (a ^ 2 + b ^ 2) * (a' * b ^ 2)
      = (a - a') * (b ^ 2 * (b ^ 2 - a * a')) := by ring
  rw [e, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg (a + a')),
    mul_nonneg (sq_nonneg b) (sq_nonneg (a - a')), mul_nonneg (sq_nonneg a) (sq_nonneg a'),
    sq_nonneg (a * a'), mul_nonneg (sq_nonneg b) (sq_nonneg a), mul_nonneg (sq_nonneg b) (sq_nonneg a')]

lemma Gq_lip2 (a b b' : ℝ) : |Gq a b - Gq a b'| ≤ |b - b'| := by
  unfold Gq
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h1 : 0 < a ^ 2 + b ^ 2 := by positivity
  have h2 : 0 < a ^ 2 + b' ^ 2 := by positivity
  rw [div_sub_div _ _ h1.ne' h2.ne', abs_div, abs_of_pos (mul_pos h1 h2), div_le_iff₀ (mul_pos h1 h2)]
  have e : a * b ^ 2 * (a ^ 2 + b' ^ 2) - (a ^ 2 + b ^ 2) * (a * b' ^ 2)
      = (b - b') * (a ^ 3 * (b + b')) := by ring
  rw [e, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (a - b)),
    mul_nonneg (sq_nonneg a) (sq_nonneg (a - b')), mul_nonneg (sq_nonneg a) (sq_nonneg (a + b)),
    mul_nonneg (sq_nonneg a) (sq_nonneg (a + b')), mul_nonneg (sq_nonneg b) (sq_nonneg b'),
    mul_nonneg (sq_nonneg a) (sq_nonneg b), mul_nonneg (sq_nonneg a) (sq_nonneg b')]

lemma clamp_lip (s t : ℝ) :
    |max (-1/2) (min (1/2) s) - max (-1/2) (min (1/2) t)| ≤ |s - t| := by
  have h1 := neg_abs_le (s - t); have h2 := le_abs_self (s - t)
  rw [abs_le]
  constructor <;> (simp only [max_def, min_def]; split_ifs <;> linarith)

noncomputable def hF (x : E2) : ℝ := max (-1/2) (min (1/2) (Gq (x 0 - 1) (x 1)))

lemma hF_abs (x : E2) : |hF x| ≤ 1 / 2 := by
  unfold hF; rw [abs_le]
  constructor
  · linarith [le_max_left (-1/2 : ℝ) (min (1/2 : ℝ) (Gq (x 0 - 1) (x 1)))]
  · exact max_le (by norm_num) (min_le_left (1/2 : ℝ) _)

lemma hF_lip (x y : E2) : |hF x - hF y| ≤ 2 * dist x y := by
  have h0 := PiLp.dist_apply_le x y 0
  have h1 := PiLp.dist_apply_le x y 1
  rw [Real.dist_eq] at h0 h1
  calc |hF x - hF y| ≤ |Gq (x 0 - 1) (x 1) - Gq (y 0 - 1) (y 1)| := clamp_lip _ _
    _ ≤ |Gq (x 0 - 1) (x 1) - Gq (y 0 - 1) (x 1)| + |Gq (y 0 - 1) (x 1) - Gq (y 0 - 1) (y 1)| :=
        abs_sub_le _ _ _
    _ ≤ |x 0 - 1 - (y 0 - 1)| + |x 1 - y 1| := add_le_add (Gq_lip1 _ _ _) (Gq_lip2 _ _ _)
    _ ≤ 2 * dist x y := by rw [show x 0 - 1 - (y 0 - 1) = x 0 - y 0 by ring]; linarith

lemma exists_h : ∃ h : (closure {x : E2 | (0 : ℝ) < x 0}) →ᵇ ℝ,
    (∀ x, h x = hF x.1) ∧ HolderWith 2 ⟨1, zero_le_one⟩ ⇑h := by
  have hcont : Continuous hF :=
    (LipschitzWith.of_dist_le_mul (K := 2) (fun x y => by
      rw [Real.dist_eq]; push_cast; exact hF_lip x y)).continuous
  refine ⟨BoundedContinuousFunction.mkOfBound ⟨fun x => hF x.1, hcont.comp continuous_subtype_val⟩
    1 (fun x y => ?_), fun x => rfl, ?_⟩
  · show dist (hF x.1) (hF y.1) ≤ 1
    rw [Real.dist_eq]
    have := abs_sub (hF x.1) (hF y.1)
    linarith [hF_abs x.1, hF_abs y.1]
  · intro x y
    rw [edist_dist, edist_dist, Real.dist_eq]
    change ENNReal.ofReal |hF x.1 - hF y.1| ≤ ↑(2 : NNReal) * ENNReal.ofReal (dist x y) ^ (1 : ℝ)
    rw [ENNReal.rpow_one, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    exact hF_lip x.1 y.1

lemma ball_sub : Metric.ball b0 1 ⊆ {x : E2 | (0 : ℝ) < x 0} := by
  intro y hy
  have h := PiLp.dist_apply_le y b0 0
  rw [Real.dist_eq] at h
  have hb : b0 0 = 1 := by simp [b0]
  rw [hb] at h
  have := (Metric.mem_ball.mp hy)
  show 0 < y 0
  have := abs_lt.mp (h.trans_lt this)
  linarith [this.1]

lemma CH_point {Ω : Set E2} {φ : E2 → ℝ} (hφ : EthierKurtz.ComponentHolder Ω 1 φ) {c : E2}
    (hball : Metric.ball c 1 ⊆ Ω) :
    ∃ R1 : ℝ, 0 < R1 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ Metric.ball c R1, |φ y - φ c| ≤ K * ‖y - c‖ := by
  obtain ⟨_, ρ₀, M, hρ₀, hM, hosc⟩ := hφ
  refine ⟨min (1 / 2) (ρ₀ / 2), lt_min (by norm_num) (by linarith), 2 * M, by linarith,
    fun y hy => ?_⟩
  rcases eq_or_ne y c with rfl | hne
  · simp
  have hs : 0 < ‖y - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hyc : ‖y - c‖ < min (1 / 2) (ρ₀ / 2) := by rw [← dist_eq_norm]; exact hy
  have hy1 : ‖y - c‖ < 1 / 2 := hyc.trans_le (min_le_left _ _)
  have hy2 : ‖y - c‖ < ρ₀ / 2 := hyc.trans_le (min_le_right _ _)
  set ρ := 2 * ‖y - c‖
  set W := Metric.ball c 1 ∩ Metric.ball y ρ
  have hWc : IsPreconnected W := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hyW : y ∈ W := ⟨by rw [Metric.mem_ball, dist_eq_norm]; linarith,
    Metric.mem_ball_self (by positivity)⟩
  have hcW : c ∈ W := ⟨Metric.mem_ball_self one_pos, by
    rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; linarith⟩
  have hWsub : W ⊆ Ω ∩ Metric.ball y ρ := fun p hp => ⟨hball hp.1, hp.2⟩
  have hcc := hWc.subset_connectedComponentIn hyW hWsub
  have := hosc ρ (by positivity) (by linarith) y y (hWsub hyW) y (hcc hyW) c (hcc hcW)
  rw [Real.rpow_one] at this
  calc |φ y - φ c| ≤ M * ρ := this
    _ = 2 * M * ‖y - c‖ := by ring

lemma b0_apply0 : b0 0 = 1 := by simp [b0]
lemma b0_apply1 : b0 1 = 0 := by simp [b0]

lemma q_coords (r θ : ℝ) : (b0 + r • ev θ) 0 = 1 + r * Real.cos θ ∧
    (b0 + r • ev θ) 1 = r * Real.sin θ := by
  constructor <;> simp [ev_apply0, ev_apply1, b0_apply0, b0_apply1] <;> ring

lemma hF_ray {r θ : ℝ} (hr : 0 < r) (hr2 : r < 1 / 2) :
    hF (b0 + r • ev θ) = r * Real.cos θ * Real.sin θ ^ 2 := by
  obtain ⟨h0, h1⟩ := q_coords r θ
  have hG : Gq ((b0 + r • ev θ) 0 - 1) ((b0 + r • ev θ) 1) = r * Real.cos θ * Real.sin θ ^ 2 := by
    rw [h0, h1, Gq]
    have hden : (1 + r * Real.cos θ - 1) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [hden]
    field_simp
    ring
  have hb : |r * Real.cos θ * Real.sin θ ^ 2| ≤ r := by
    rw [abs_mul, abs_mul, abs_of_pos hr, abs_of_nonneg (sq_nonneg (Real.sin θ))]
    have := Real.abs_cos_le_one θ
    have := Real.sin_sq_le_one θ
    have : |Real.cos θ| * Real.sin θ ^ 2 ≤ 1 := by
      calc |Real.cos θ| * Real.sin θ ^ 2 ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    nlinarith [abs_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]
  have hb' := abs_le.mp hb
  unfold hF
  rw [hG, min_eq_right (by linarith), max_eq_right (by linarith)]

lemma glue_false (lam : ℝ)
    (fg : ((closure {x : E2 | (0 : ℝ) < x 0}) →ᵇ ℝ) × ((closure {x : E2 | (0 : ℝ) < x 0}) →ᵇ ℝ))
    (hmem : fg ∈ EthierKurtz.obliqueDiffusionGraph {x : E2 | (0 : ℝ) < x 0} 1 (fun _ => 1)
      (fun _ => 0) (fun _ => EuclideanSpace.single (0 : Fin 2) (-1 : ℝ)))
    (h : (closure {x : E2 | (0 : ℝ) < x 0}) →ᵇ ℝ) (hh : ∀ x, h x = hF x.1)
    (heq : lam • fg.1 - fg.2 = h) : False := by
  obtain ⟨⟨hcd, hpart⟩, hg, -⟩ := hmem
  set u := EthierKurtz.closedRegionRestriction fg.1 with hu_def
  set g := EthierKurtz.closedRegionRestriction fg.2 with hg_def
  obtain ⟨R00, hR00, K00, hK00, h00⟩ := CH_point (hpart 0 0) ball_sub
  obtain ⟨R01, hR01, K01, hK01, h01⟩ := CH_point (hpart 0 1) ball_sub
  obtain ⟨R10, hR10, K10, hK10, h10⟩ := CH_point (hpart 1 0) ball_sub
  obtain ⟨R11, hR11, K11, hK11, h11⟩ := CH_point (hpart 1 1) ball_sub
  set R0 := min (1 / 2) (min (min R00 R01) (min R10 R11)) with hR0def
  have hR0 : 0 < R0 := lt_min (by norm_num) (lt_min (lt_min hR00 hR01) (lt_min hR10 hR11))
  have hR0h : R0 ≤ 1 / 2 := min_le_left _ _
  have hRle : R0 ≤ R00 ∧ R0 ≤ R01 ∧ R0 ≤ R10 ∧ R0 ≤ R11 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hR0def, min_le_iff, le_refl, true_or, or_true]
  have hsub : Metric.ball b0 R0 ⊆ {x : E2 | (0 : ℝ) < x 0} :=
    (Metric.ball_subset_ball (by linarith)).trans ball_sub
  have hu : ContDiffOn ℝ 2 u (Metric.ball b0 R0) := hcd.mono hsub
  have hc : b0 ∈ Metric.ball b0 R0 := Metric.mem_ball_self hR0
  have hpd : ∀ y ∈ Metric.ball b0 R0, ∀ i j : Fin 2,
      fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single j 1)) y
        (EuclideanSpace.single i 1) = D2 u y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) := by
    intro y hy i j
    have hD := (reg hu hy).2.1
    rw [fderiv_clm_apply hD (differentiableAt_const _)]
    simp [D2]
  have hball : ∀ {R : ℝ}, R0 ≤ R → ∀ y ∈ Metric.ball b0 R0, y ∈ Metric.ball b0 R :=
    fun hR y hy => Metric.ball_subset_ball hR hy
  have hM : ∀ y ∈ Metric.ball b0 R0, ∀ θ : ℝ,
      |D2 u y (ev θ) (ev θ) - D2 u b0 (ev θ) (ev θ)| ≤ (K00 + K01 + K10 + K11) * ‖y - b0‖ := by
    intro y hy θ
    have e00 := h00 y (hball hRle.1 y hy)
    have e01 := h01 y (hball hRle.2.1 y hy)
    have e10 := h10 y (hball hRle.2.2.1 y hy)
    have e11 := h11 y (hball hRle.2.2.2 y hy)
    simp only [hpd y hy, hpd b0 hc] at e00 e01 e10 e11
    change |D2 u y b0 b0 - D2 u b0 b0 b0| ≤ K00 * ‖y - b0‖ at e00
    change |D2 u y b0 b1 - D2 u b0 b0 b1| ≤ K01 * ‖y - b0‖ at e01
    change |D2 u y b1 b0 - D2 u b0 b1 b0| ≤ K10 * ‖y - b0‖ at e10
    change |D2 u y b1 b1 - D2 u b0 b1 b1| ≤ K11 * ‖y - b0‖ at e11
    rw [exp2, exp2]
    set cs := Real.cos θ
    set sn := Real.sin θ
    have hcs : |cs| ≤ 1 := Real.abs_cos_le_one θ
    have hsn : |sn| ≤ 1 := Real.abs_sin_le_one θ
    have hc2 : |cs ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hcs
    have hs2 : |sn ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hsn
    have hsc : |sn * cs| ≤ 1 := by
      rw [abs_mul]; exact mul_le_one₀ hsn (abs_nonneg _) hcs
    have key : cs ^ 2 * D2 u y b0 b0 + sn * cs * (D2 u y b0 b1 + D2 u y b1 b0) +
        sn ^ 2 * D2 u y b1 b1 - (cs ^ 2 * D2 u b0 b0 b0 +
        sn * cs * (D2 u b0 b0 b1 + D2 u b0 b1 b0) + sn ^ 2 * D2 u b0 b1 b1) =
        cs ^ 2 * (D2 u y b0 b0 - D2 u b0 b0 b0) + sn * cs * (D2 u y b0 b1 - D2 u b0 b0 b1) +
        sn * cs * (D2 u y b1 b0 - D2 u b0 b1 b0) + sn ^ 2 * (D2 u y b1 b1 - D2 u b0 b1 b1) := by
      ring
    rw [key]
    have t1 : |cs ^ 2 * (D2 u y b0 b0 - D2 u b0 b0 b0)| ≤ K00 * ‖y - b0‖ := by
      rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hc2).trans e00
    have t2 : |sn * cs * (D2 u y b0 b1 - D2 u b0 b0 b1)| ≤ K01 * ‖y - b0‖ := by
      rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hsc).trans e01
    have t3 : |sn * cs * (D2 u y b1 b0 - D2 u b0 b1 b0)| ≤ K10 * ‖y - b0‖ := by
      rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hsc).trans e10
    have t4 : |sn ^ 2 * (D2 u y b1 b1 - D2 u b0 b1 b1)| ≤ K11 * ‖y - b0‖ := by
      rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hs2).trans e11
    have a1 := abs_le.mp t1
    have a2 := abs_le.mp t2
    have a3 := abs_le.mp t3
    have a4 := abs_le.mp t4
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  have hpde : ∀ r ∈ Set.Ioo 0 R0, ∀ θ : ℝ, D2 u (b0 + r • ev θ) b0 b0 +
      D2 u (b0 + r • ev θ) b1 b1
      = 2 * lam * u (b0 + r • ev θ) - 2 * (r * Real.cos θ * Real.sin θ ^ 2) := by
    intro r hr θ
    set q := b0 + r • ev θ with hq
    have hqb : q ∈ Metric.ball b0 R0 := by
      rw [Metric.mem_ball, hq, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_ev, mul_one,
        Real.norm_eq_abs, abs_of_pos hr.1]
      exact hr.2
    have hqΩ := hsub hqb
    have hqc : q ∈ closure {x : E2 | (0 : ℝ) < x 0} := subset_closure hqΩ
    have e1 := congrArg (fun F => F ⟨q, hqc⟩) heq
    simp only [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hh] at e1
    have uq : u q = fg.1 ⟨q, hqc⟩ := by
      simp only [hu_def, EthierKurtz.closedRegionRestriction, dif_pos hqc]
    have gq : g q = fg.2 ⟨q, hqc⟩ := by
      simp only [hg_def, EthierKurtz.closedRegionRestriction, dif_pos hqc]
    have e2 := hg q hqΩ
    simp only [Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1
      by decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), one_mul, zero_mul,
      add_zero, zero_add, map_zero, hpd q hqb] at e2
    change g q = 1 / 2 * (D2 u q b0 b0 + D2 u q b1 b1) at e2
    rw [hF_ray hr.1 (hr.2.trans_le hR0h)] at e1
    rw [uq]
    linarith
  exact core_false hu hR0 (by positivity) hM hpde

end glue

end P502049df

open Filter in
open scoped Topology BoundedContinuousFunction in
open EthierKurtz in
theorem solution : ¬ (∀ (n : ℕ) (hd : 2 ≤ n + 1) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1),
    ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ (h : (closure {x : EuclideanSpace ℝ (Fin (n + 1)) |
        (0 : ℝ) < x (0 : Fin (n + 1))}) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph
          {x : EuclideanSpace ℝ (Fin (n + 1)) |
            (0 : ℝ) < x (0 : Fin (n + 1))} μ (fun _ => 1) (fun _ => 0)
          (fun _ => EuclideanSpace.single (0 : Fin (n + 1)) (-1 : ℝ)),
          lam₀ • fg.1 - fg.2 = h) := by
  intro H
  obtain ⟨lam, -, hH⟩ := H 1 (by norm_num) 1 ⟨one_pos, le_rfl⟩
  obtain ⟨hb, hbx, hHol⟩ := P502049df.exists_h
  obtain ⟨fg, hmem, heq⟩ := hH hb 2 hHol
  exact P502049df.glue_false lam fg hmem hb hbx heq
