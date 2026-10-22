-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_body_of_regular_starshaped_hessian
-- status  : ACCEPTED   (disprove)
-- author  : @Mazecto
-- created : 2026-10-02T07:46:42.40186+00:00
-- url     : https://prove2.me/submissions/18cb9ed1-e73d-45b6-aad7-7e0dc2acaa2b

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Topology.MetricSpace.Bounded

open BirkhoffGlobalSection

namespace ConvexBodyDisproof

/-- The squared Euclidean norm minus one. -/
noncomputable def H (y : Phase) : ℝ := ∑ i, y i ^ 2 - 1

/-- The first basis vector `e₀`. -/
def e0 : Phase := fun i => if i = 0 then 1 else 0

noncomputable def DH (x : Phase) : Phase →L[ℝ] ℝ :=
  ∑ i, (2 * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i

theorem DH_apply (x v : Phase) : DH x v = ∑ i, 2 * x i * v i := by
  simp [DH, mul_comm, mul_left_comm]

theorem hasFDerivAt_H (x : Phase) : HasFDerivAt H (DH x) x := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      HasFDerivAt (fun y : Phase => y i ^ 2)
        ((2 * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) x := by
    intro i _
    have hp := (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) i x).pow 2
    refine hp.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp
  have hs := HasFDerivAt.fun_sum h
  have : (fun y : Phase => ∑ i, y i ^ 2) = fun y => ∑ i ∈ Finset.univ, y i ^ 2 := rfl
  unfold H DH
  exact (by simpa using hs.sub_const 1)

theorem fderiv_H (x : Phase) : fderiv ℝ H x = DH x := (hasFDerivAt_H x).fderiv

theorem contDiff_H : ContDiff ℝ 2 H := by
  unfold H; fun_prop

theorem second_deriv (v : Phase) :
    fderiv ℝ (fun x => fderiv ℝ H x v) e0 v = ∑ i, 2 * v i * v i := by
  have hfun : (fun x => fderiv ℝ H x v) = fun x : Phase => ∑ i, (2 * v i) * x i := by
    funext x; rw [fderiv_H, DH_apply]; congr 1; funext i; ring
  rw [hfun]
  have hlin : HasFDerivAt (fun x : Phase => ∑ i, (2 * v i) * x i)
      (∑ i, (2 * v i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) e0 := by
    exact HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) i e0).const_mul (2 * v i))
  rw [hlin.fderiv]
  simp [mul_assoc]

end ConvexBodyDisproof

open ConvexBodyDisproof in
theorem solution : ¬ (∀ (H : Phase → ℝ) (S : Set Phase),
    IsCompact S → IsConnected S →
    (∀ y ∈ S, fderiv ℝ H y ≠ 0) →
    (∀ y ∈ S, 0 < fderiv ℝ H y y) →
    (∀ y ∈ S, H y = 0) →
    HasPositiveTangentialHessianOn H S →
    ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
      (0 : Phase) ∈ interior B ∧ S = frontier B) := by
  intro hall
  have he0 : ∀ y ∈ ({e0} : Set Phase), y = e0 := fun y hy => hy
  have hD0 : ∀ v : Phase, fderiv ℝ ConvexBodyDisproof.H e0 v = 2 * v 0 := by
    intro v; rw [fderiv_H, DH_apply]; simp [e0]
  obtain ⟨B, hBc, -, h0, hfr⟩ := hall ConvexBodyDisproof.H {e0}
    isCompact_singleton isConnected_singleton
    (by
      intro y hy; rw [he0 y hy]; intro h
      have := congrArg (fun L => L e0) h
      simp only [hD0, zero_apply] at this
      simp [e0] at this)
    (by intro y hy; rw [he0 y hy, hD0]; simp [e0])
    (by intro y hy; rw [he0 y hy]; simp [ConvexBodyDisproof.H, e0])
    ⟨fun s _ => contDiff_H.contDiffAt, by
      intro s hs v hv _
      rw [he0 s hs, second_deriv]
      have : ∃ i, v i ≠ 0 := by
        by_contra h; push Not at h; exact hv (funext h)
      obtain ⟨i, hi⟩ := this
      have hpos : 0 < 2 * v i * v i := by
        have := mul_self_pos.2 hi; linarith
      calc 0 < 2 * v i * v i := hpos
        _ ≤ ∑ j, 2 * v j * v j :=
          Finset.single_le_sum (f := fun j => 2 * v j * v j)
            (fun j _ => by nlinarith [sq_nonneg (v j)]) (Finset.mem_univ i)⟩
  -- `B` is bounded, so a point far along `-e₀` lies outside it.
  obtain ⟨R, hR⟩ := hBc.isBounded.subset_closedBall 0
  set p : Phase := fun i => if i = 0 then -(|R| + 1) else 0 with hp
  have hpB : p ∉ B := by
    intro hpB
    have h1 := hR hpB
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : |p 0| ≤ ‖p‖ := by
      have := norm_le_pi_norm p 0
      simpa [Real.norm_eq_abs] using this
    have : |p 0| = |R| + 1 := by
      simp only [hp, if_pos rfl, abs_neg]; exact abs_of_pos (by positivity)
    linarith [le_abs_self R]
  -- The segment `[0, p]` cannot split into the open sets `interior B` and `Bᶜ`.
  have hcross : ∃ q ∈ segment ℝ (0 : Phase) p, q ∈ frontier B := by
    by_contra hno
    push Not at hno
    have hcov : segment ℝ (0 : Phase) p ⊆ interior B ∪ Bᶜ := by
      intro q hq
      by_cases hqB : q ∈ B
      · left
        by_contra hqi
        exact hno q hq (by rw [hBc.isClosed.frontier_eq]; exact ⟨hqB, hqi⟩)
      · right; exact hqB
    obtain ⟨q, -, hqi, hqc⟩ := (convex_segment (0 : Phase) p).isPreconnected _ _
      isOpen_interior hBc.isClosed.isOpen_compl hcov
      ⟨0, left_mem_segment ℝ 0 p, h0⟩ ⟨p, right_mem_segment ℝ 0 p, hpB⟩
    exact hqc (interior_subset hqi)
  obtain ⟨q, hqseg, hqfr⟩ := hcross
  rw [← hfr] at hqfr
  have hq : q = e0 := hqfr
  obtain ⟨a, b, ha, hb, -, hqab⟩ := hqseg
  have hq0 : q 0 = b * (-(|R| + 1)) := by
    rw [← hqab]; simp [hp]
  rw [hq] at hq0
  have : (e0 : Phase) 0 = 1 := by simp [e0]
  nlinarith [abs_nonneg R]
