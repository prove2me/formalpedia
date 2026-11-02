-- Prove2me | solution 1 for EthierKurtz.oblique_boundary_chart_local_inverse
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T23:22:48.156604+00:00
-- url     : https://prove2.me/submissions/af3eb4ae-1b35-4c4b-bc09-7312a49d9fb9

import Mathlib
import Definitions.Def_EthierKurtz_CTwiceHolder

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology

namespace ObliqueLib
/-- Euclidean space of dimension `d`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Normalized Gaussian of "variance parameter" `s`: `G s z = (π s)^(-d/2) exp(-|z|^2/s)`. -/
noncomputable def G (d : ℕ) (s : ℝ) (z : Eu d) : ℝ :=
  (π * s) ^ (-((d : ℝ) / 2)) * rexp (-‖z‖ ^ 2 / s)

section Comp2

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Uniform `C^{2,μ}`-type bounds of `(f, Df, D2f)` on a set `T` with one constant `K`. -/
structure C2B (T : Set E) (μ K : ℝ) (f : E → F) (Df : E → E →L[ℝ] F)
    (D2f : E → E →L[ℝ] E →L[ℝ] F) : Prop where
  hK : 0 ≤ K
  lip : ∀ x ∈ T, ∀ y ∈ T, ‖f x - f y‖ ≤ K * ‖x - y‖
  b1 : ∀ x ∈ T, ‖Df x‖ ≤ K
  lip1 : ∀ x ∈ T, ∀ y ∈ T, ‖Df x - Df y‖ ≤ K * ‖x - y‖
  b2 : ∀ x ∈ T, ‖D2f x‖ ≤ K
  hol2 : ∀ x ∈ T, ∀ y ∈ T, ‖D2f x - D2f y‖ ≤ K * ‖x - y‖ ^ μ

end Comp2

section Glue

variable {n : ℕ}

end Glue

section IFT

variable {d : ℕ}

/-- the identity as a nonlinear right inverse of `id`, with `nnnorm = 1`. -/
def idNRI : (ContinuousLinearMap.id ℝ (Eu d)).NonlinearRightInverse where
  toFun := id
  nnnorm := 1
  bound' := fun y => by simp
  right_inv' := fun y => by simp

lemma chart_local_inverse {Θ : Eu d → Eu d} {x0 : Eu d}
    (hΘ : HasStrictFDerivAt Θ (ContinuousLinearMap.id ℝ (Eu d)) x0) :
    ∃ r : ℝ, 0 < r ∧
      (∀ x ∈ Metric.ball x0 r, ∀ x' ∈ Metric.ball x0 r, ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖) ∧
      (∀ x ∈ Metric.ball x0 r, ∀ x' ∈ Metric.ball x0 r, ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖) ∧
      ∀ z ∈ Metric.closedBall (Θ x0) (r / 4), ∃ x ∈ Metric.closedBall x0 (r / 2), Θ x = z := by
  obtain ⟨s, hs, hap⟩ := hΘ.approximates_deriv_on_nhds (c := (1 / 2 : NNReal)) (Or.inr (by norm_num))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hs
  have key : ∀ x ∈ Metric.ball x0 r, ∀ x' ∈ Metric.ball x0 r,
      ‖Θ x - Θ x' - (x - x')‖ ≤ (1 / 2) * ‖x - x'‖ := by
    intro x hx x' hx'
    have := hap x (hball hx) x' (hball hx')
    simpa using this
  refine ⟨r, hr, fun x hx x' hx' => ?_, fun x hx x' hx' => ?_, ?_⟩
  · have h1 := key x hx x' hx'
    have h2 := norm_sub_norm_le (x - x') (Θ x - Θ x')
    rw [norm_sub_rev (x - x') (Θ x - Θ x')] at h2
    linarith
  · have h1 := key x hx x' hx'
    have h2 := norm_sub_norm_le (Θ x - Θ x') (x - x')
    have h3 : 0 ≤ ‖x - x'‖ := norm_nonneg _
    linarith
  · intro z hz
    have hsub : Metric.closedBall x0 (r / 2) ⊆ s :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    have hsurj := hap.surjOn_closedBall_of_nonlinearRightInverse idNRI (by positivity) hsub
    have hrad : (((idNRI : (ContinuousLinearMap.id ℝ (Eu d)).NonlinearRightInverse).nnnorm : ℝ)⁻¹ -
        ((1 / 2 : NNReal) : ℝ)) * (r / 2) = r / 4 := by
      simp [idNRI]; ring
    rw [hrad] at hsurj
    obtain ⟨x, hx, hxz⟩ := hsurj hz
    exact ⟨x, hx, hxz⟩

end IFT

section OpTrans

variable {d : ℕ}

end OpTrans

section CutHelp

variable {d : ℕ}

/-- an inverse function from the `chart_local_inverse` output. -/
theorem chart_inverse_fn {Θ : Eu d → Eu d} {x0 : Eu d} {r : ℝ} (hr : 0 < r)
    (hlo : ∀ x ∈ Metric.ball x0 r, ∀ x' ∈ Metric.ball x0 r, ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖)
    (hsurj : ∀ z ∈ Metric.closedBall (Θ x0) (r / 4), ∃ x ∈ Metric.closedBall x0 (r / 2), Θ x = z) :
    ∃ Λ : Eu d → Eu d,
      (∀ z ∈ Metric.closedBall (Θ x0) (r / 4), Λ z ∈ Metric.closedBall x0 (r / 2) ∧ Θ (Λ z) = z) ∧
      (∀ z ∈ Metric.closedBall (Θ x0) (r / 4), ∀ z' ∈ Metric.closedBall (Θ x0) (r / 4),
        ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) ∧
      (∀ x ∈ Metric.ball x0 r, Θ x ∈ Metric.closedBall (Θ x0) (r / 4) → Λ (Θ x) = x) := by
  classical
  let Λ : Eu d → Eu d := fun z =>
    if h : z ∈ Metric.closedBall (Θ x0) (r / 4) then (hsurj z h).choose else x0
  have hΛ : ∀ z ∈ Metric.closedBall (Θ x0) (r / 4), Λ z ∈ Metric.closedBall x0 (r / 2) ∧ Θ (Λ z) = z := by
    intro z hz
    simp only [Λ, dif_pos hz]
    exact (hsurj z hz).choose_spec
  have hin : ∀ y ∈ Metric.closedBall x0 (r / 2), y ∈ Metric.ball x0 r :=
    fun y hy => Metric.closedBall_subset_ball (by linarith) hy
  refine ⟨Λ, hΛ, fun z hz z' hz' => ?_, fun x hx hΘx => ?_⟩
  · have := hlo _ (hin _ (hΛ z hz).1) _ (hin _ (hΛ z' hz').1)
    rwa [(hΛ z hz).2, (hΛ z' hz').2] at this
  · have := hlo _ (hin _ (hΛ _ hΘx).1) _ hx
    rw [(hΛ _ hΘx).2, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

end CutHelp

structure ObChart {d : ℕ} (Ω : Set (Eu d)) (μ : ℝ) (c : Eu d → Eu d) (x0 : Eu d) (r0 K : ℝ) (e b : Eu d)
    (Θ : Eu d → Eu d) (DΘ : Eu d → Eu d →L[ℝ] Eu d) (D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d) : Prop where
  hr0 : 0 < r0
  he : ‖e‖ = 1
  hb : inner ℝ b e = 0
  strict : ∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x
  hd2 : ∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x
  h0 : Θ x0 = 0
  hD0 : DΘ x0 = ContinuousLinearMap.id ℝ (Eu d)
  side : ∀ x ∈ Metric.ball x0 r0, (x ∈ Ω ↔ 0 < inner ℝ (Θ x) e) ∧ (x ∈ frontier Ω ↔ inner ℝ (Θ x) e = 0)
  obl : ∀ x ∈ Metric.ball x0 r0 ∩ frontier Ω, ∃ κ : ℝ, 0 < κ ∧ DΘ x (c x) = κ • (b - e)
  c2b : C2B (Metric.ball x0 r0 ∩ closure Ω) μ K Θ DΘ D2Θ

section ObChartS

end ObChartS

section VarDef

end VarDef

section Pull

variable {d : ℕ}

theorem chart_inv_small {Ω : Set (Eu d)} {μ : ℝ} {c : Eu d → Eu d} {x0 : Eu d} {r0 K : ℝ} {e b : Eu d}
    {Θ : Eu d → Eu d} {DΘ : Eu d → Eu d →L[ℝ] Eu d} {D2Θ : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] Eu d}
    (hch : ObChart Ω μ c x0 r0 K e b Θ DΘ D2Θ) :
    ∃ r1 : ℝ, 0 < r1 ∧ r1 ≤ r0 ∧ ∃ Λ : Eu d → Eu d,
      (∀ x ∈ Metric.ball x0 r1, ∀ x' ∈ Metric.ball x0 r1,
        ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖ ∧ ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖) ∧
      (∀ z ∈ Metric.closedBall (0 : Eu d) (r1 / 4), Λ z ∈ Metric.closedBall x0 (r1 / 2) ∧ Θ (Λ z) = z) ∧
      (∀ z ∈ Metric.closedBall (0 : Eu d) (r1 / 4), ∀ z' ∈ Metric.closedBall (0 : Eu d) (r1 / 4),
        ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) ∧
      (∀ x ∈ Metric.ball x0 r1, Θ x ∈ Metric.closedBall (0 : Eu d) (r1 / 4) → Λ (Θ x) = x) := by
  have hs : HasStrictFDerivAt Θ (ContinuousLinearMap.id ℝ (Eu d)) x0 := by
    have := hch.strict x0 (Metric.mem_ball_self hch.hr0); rwa [hch.hD0] at this
  obtain ⟨r, hr, hlo, hup, hsurj⟩ := chart_local_inverse hs
  have hr1 : 0 < min r r0 := lt_min hr hch.hr0
  have hmr : min r r0 ≤ r := min_le_left _ _
  have hsub : Metric.ball x0 (min r r0) ⊆ Metric.ball x0 r := Metric.ball_subset_ball hmr
  have hsurj1 : ∀ z ∈ Metric.closedBall (Θ x0) (min r r0 / 4),
      ∃ x ∈ Metric.closedBall x0 (min r r0 / 2), Θ x = z := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (Θ x0) (r / 4) :=
      Metric.closedBall_subset_closedBall (by linarith) hz
    obtain ⟨x, hx, rfl⟩ := hsurj z hz'
    refine ⟨x, ?_, rfl⟩
    have hxb : x ∈ Metric.ball x0 r := Metric.closedBall_subset_ball (by linarith) hx
    have := hlo x hxb x0 (Metric.mem_ball_self hr)
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    linarith
  obtain ⟨Λ, h1, h2, h3⟩ :=
    chart_inverse_fn hr1 (fun x hx x' hx' => hlo x (hsub hx) x' (hsub hx')) hsurj1
  rw [hch.h0] at h1 h2 h3
  exact ⟨min r r0, hr1, min_le_right _ _, Λ,
    fun x hx x' hx' => ⟨hlo x (hsub hx) x' (hsub hx'), hup x (hsub hx) x' (hsub hx')⟩, h1, h2, h3⟩

end Pull

section NormA

variable {d : ℕ}

end NormA

section VarA

variable {d : ℕ}

end VarA

section PullA

variable {d : ℕ}

end PullA

section CoefA

variable {d : ℕ}

end CoefA

section LocalSolveA

variable {d : ℕ}

end LocalSolveA

end ObliqueLib

theorem solution (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (c : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x0 : EuclideanSpace ℝ (Fin d)) (r0 K : ℝ) (e b : EuclideanSpace ℝ (Fin d)) (Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (DΘ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (D2Θ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hchart : 0 < r0 ∧ ‖e‖ = 1 ∧ inner ℝ b e = 0 ∧
        (∀ x ∈ Metric.ball x0 r0, HasStrictFDerivAt Θ (DΘ x) x) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ Ω, HasFDerivAt DΘ (D2Θ x) x) ∧
        Θ x0 = 0 ∧ DΘ x0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) ∧
        (∀ x ∈ Metric.ball x0 r0,
          (x ∈ Ω ↔ 0 < inner ℝ (Θ x) e) ∧ (x ∈ frontier Ω ↔ inner ℝ (Θ x) e = 0)) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ frontier Ω, ∃ κ : ℝ, 0 < κ ∧ DΘ x (c x) = κ • (b - e)) ∧
        0 ≤ K ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖Θ x - Θ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖DΘ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖DΘ x - DΘ y‖ ≤ K * ‖x - y‖) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ‖D2Θ x‖ ≤ K) ∧
        (∀ x ∈ Metric.ball x0 r0 ∩ closure Ω, ∀ y ∈ Metric.ball x0 r0 ∩ closure Ω,
          ‖D2Θ x - D2Θ y‖ ≤ K * ‖x - y‖ ^ μ)) :
    ∃ r1 : ℝ, 0 < r1 ∧ r1 ≤ r0 ∧ ∃ Λ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x ∈ Metric.ball x0 r1, ∀ x' ∈ Metric.ball x0 r1,
        ‖x - x'‖ ≤ 2 * ‖Θ x - Θ x'‖ ∧ ‖Θ x - Θ x'‖ ≤ 2 * ‖x - x'‖) ∧
      (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4), Λ z ∈ Metric.closedBall x0 (r1 / 2) ∧ Θ (Λ z) = z) ∧
      (∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4), ∀ z' ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4),
        ‖Λ z - Λ z'‖ ≤ 2 * ‖z - z'‖) ∧
      (∀ x ∈ Metric.ball x0 r1, Θ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (r1 / 4) → Λ (Θ x) = x) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, k1, k2, k3, k4, k5, k6⟩ := hchart
  exact ObliqueLib.chart_inv_small (μ := μ) (c := c) ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ⟨k1, k2, k3, k4, k5, k6⟩⟩
