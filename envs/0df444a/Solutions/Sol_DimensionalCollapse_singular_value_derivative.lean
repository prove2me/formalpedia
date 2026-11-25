-- Prove2me | solution 1 for DimensionalCollapse.singular_value_derivative
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:58:37.897519+00:00
-- url     : https://prove2.me/submissions/fc1a8f7f-9a3e-4185-b7ec-313407be511d

import Mathlib
import Definitions.Def_DimensionalCollapse_Basic

set_option autoImplicit false

open Matrix Filter Topology
namespace DimensionalCollapse

lemma sv_orth {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (h : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    Aᵀ * A = 1 := by
  have := (Matrix.mem_orthogonalGroup_iff' (n := Fin d) (R := ℝ)).1 h
  exact this

lemma sv_facts {d : ℕ} (W U V : Matrix (Fin d) (Fin d) ℝ) (sg : Fin d → ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) (hW : W = U * Matrix.diagonal sg * Vᵀ) (k : Fin d) :
    sg k = ∑ a, ∑ b, U a k * W a b * V b k ∧
    (∀ a, ∑ b, W a b * V b k = U a k * sg k) ∧
    (∀ b, ∑ a, U a k * W a b = sg k * V b k) ∧
    ∑ a, U a k ^ 2 = 1 ∧ ∑ b, V b k ^ 2 = 1 := by
  have h1 : Uᵀ * W * V = Matrix.diagonal sg := by
    rw [hW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.mul_assoc, hV,
      Matrix.mul_one]
  have h2 : W * V = U * Matrix.diagonal sg := by
    rw [hW, Matrix.mul_assoc, hV, Matrix.mul_one]
  have h3 : Uᵀ * W = Matrix.diagonal sg * Vᵀ := by
    rw [hW, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := congrFun (congrFun h1 k) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply_eq] at this
    rw [← this, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_mul]
  · intro a
    have := congrFun (congrFun h2 a) k
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact this
  · intro b
    have := congrFun (congrFun h3 k) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
    exact this
  · have := congrFun (congrFun hU k) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
    rw [← this]; apply Finset.sum_congr rfl; intro a _; ring
  · have := congrFun (congrFun hV k) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at this
    rw [← this]; apply Finset.sum_congr rfl; intro a _; ring

theorem singular_value_derivative {d : ℕ} (W U V : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (sig : ℝ → Fin d → ℝ) (t : ℝ) (hsvd : IsDiffSVDAt W U V sig t) :
    ∀ k, deriv (fun s => sig s k) t =
      ∑ a, ∑ b, U t a k * deriv (fun s => W s a b) t * V t b k := by
  obtain ⟨hev, hUd, hVd, hsd⟩ := hsvd
  intro k
  have hfacts : ∀ᶠ s in 𝓝 t, _ := hev.mono (fun s hs =>
    sv_facts (W s) (U s) (V s) (sig s) (sv_orth _ hs.1) (sv_orth _ hs.2.1) hs.2.2.2 k)
  have ht := hfacts.self_of_nhds
  -- W differentiable
  have hWd : ∀ a b, DifferentiableAt ℝ (fun s => W s a b) t := by
    intro a b
    have heq : (fun s => ∑ c, U s a c * sig s c * V s b c) =ᶠ[𝓝 t] fun s => W s a b := by
      filter_upwards [hev] with s hs
      rw [hs.2.2.2]
      simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
    exact DifferentiableAt.fun_sum (fun c _ => ((hUd a c).mul (hsd c)).mul (hVd b c))
  -- sig k = F eventually
  have hF : (fun s => sig s k) =ᶠ[𝓝 t] fun s => ∑ a, ∑ b, U s a k * W s a b * V s b k :=
    hfacts.mono (fun s hs => hs.1)
  rw [hF.deriv_eq]
  have hFd : HasDerivAt (fun s => ∑ a, ∑ b, U s a k * W s a b * V s b k)
      (∑ a, ∑ b, ((deriv (fun s => U s a k) t * W t a b + U t a k * deriv (fun s => W s a b) t)
        * V t b k + U t a k * W t a b * deriv (fun s => V s b k) t)) t := by
    apply HasDerivAt.fun_sum; intro a _
    apply HasDerivAt.fun_sum; intro b _
    exact (((hUd a k).hasDerivAt.mul (hWd a b).hasDerivAt).mul (hVd b k).hasDerivAt)
  rw [hFd.deriv]
  -- orthogonality derivatives
  have hU0 : ∑ a, U t a k * deriv (fun s => U s a k) t = 0 := by
    have hc : (fun s => ∑ a, U s a k ^ 2) =ᶠ[𝓝 t] fun _ => (1:ℝ) :=
      hfacts.mono (fun s hs => hs.2.2.2.1)
    have hd : HasDerivAt (fun s => ∑ a, U s a k ^ 2)
        (∑ a, (2:ℕ) * U t a k ^ (2 - 1) * deriv (fun s => U s a k) t) t :=
      HasDerivAt.fun_sum (fun a _ => (hUd a k).hasDerivAt.pow 2)
    have h0 := hd.deriv
    rw [hc.deriv_eq, deriv_const] at h0
    have : ∑ a, (2:ℕ) * U t a k ^ (2 - 1) * deriv (fun s => U s a k) t =
        2 * ∑ a, U t a k * deriv (fun s => U s a k) t := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; push_cast; ring
    linarith
  have hV0 : ∑ b, V t b k * deriv (fun s => V s b k) t = 0 := by
    have hc : (fun s => ∑ b, V s b k ^ 2) =ᶠ[𝓝 t] fun _ => (1:ℝ) :=
      hfacts.mono (fun s hs => hs.2.2.2.2)
    have hd : HasDerivAt (fun s => ∑ b, V s b k ^ 2)
        (∑ b, (2:ℕ) * V t b k ^ (2 - 1) * deriv (fun s => V s b k) t) t :=
      HasDerivAt.fun_sum (fun b _ => (hVd b k).hasDerivAt.pow 2)
    have h0 := hd.deriv
    rw [hc.deriv_eq, deriv_const] at h0
    have : ∑ b, (2:ℕ) * V t b k ^ (2 - 1) * deriv (fun s => V s b k) t =
        2 * ∑ b, V t b k * deriv (fun s => V s b k) t := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; push_cast; ring
    linarith
  obtain ⟨_, hWV, hUW, _, _⟩ := ht
  have e1 : ∑ a, ∑ b, deriv (fun s => U s a k) t * W t a b * V t b k = 0 := by
    have : ∀ a, ∑ b, deriv (fun s => U s a k) t * W t a b * V t b k =
        sig t k * (U t a k * deriv (fun s => U s a k) t) := by
      intro a
      have := hWV a
      calc ∑ b, deriv (fun s => U s a k) t * W t a b * V t b k
          = deriv (fun s => U s a k) t * ∑ b, W t a b * V t b k := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
        _ = _ := by rw [this]; ring
    rw [Finset.sum_congr rfl (fun a _ => this a), ← Finset.mul_sum, hU0, mul_zero]
  have e2 : ∑ a, ∑ b, U t a k * W t a b * deriv (fun s => V s b k) t = 0 := by
    rw [Finset.sum_comm]
    have : ∀ b, ∑ a, U t a k * W t a b * deriv (fun s => V s b k) t =
        sig t k * (V t b k * deriv (fun s => V s b k) t) := by
      intro b
      have := hUW b
      calc ∑ a, U t a k * W t a b * deriv (fun s => V s b k) t
          = (∑ a, U t a k * W t a b) * deriv (fun s => V s b k) t := by
            rw [Finset.sum_mul]
        _ = _ := by rw [this]; ring
    rw [Finset.sum_congr rfl (fun b _ => this b), ← Finset.mul_sum, hV0, mul_zero]
  have e3 : ∀ a b, ((deriv (fun s => U s a k) t * W t a b + U t a k * deriv (fun s => W s a b) t)
        * V t b k + U t a k * W t a b * deriv (fun s => V s b k) t) =
      deriv (fun s => U s a k) t * W t a b * V t b k +
        U t a k * deriv (fun s => W s a b) t * V t b k +
        U t a k * W t a b * deriv (fun s => V s b k) t := by intros; ring
  simp only [e3, Finset.sum_add_distrib, e1, e2, zero_add, add_zero]

end DimensionalCollapse

open DimensionalCollapse in
theorem solution {d : ℕ} (W U V : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (sig : ℝ → Fin d → ℝ) (t : ℝ) (hsvd : IsDiffSVDAt W U V sig t) :
    ∀ k, deriv (fun s => sig s k) t =
      ∑ a, ∑ b, U t a k * deriv (fun s => W s a b) t * V t b k :=
  DimensionalCollapse.singular_value_derivative W U V sig t hsvd
