-- Prove2me | solution 1 for FunctionalInequalities.Analysis.le_det_hessianMatrix_of_upper_touch_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:16.725991+00:00
-- url     : https://prove2.me/submissions/6369f4e7-2222-462c-9f18-079bba873dd6

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity
import Theorems.Thm_FunctionalInequalities_Analysis_convexOn_quadraticAt_readable
import Theorems.Thm_FunctionalInequalities_Analysis_posSemidef_hessianMatrix_of_upper_touch_readable
import Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_subset_of_le_readable
import Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_quadraticAt_aux_readable
import Theorems.Thm_FunctionalInequalities_Analysis_hessianMatrix_quadratic_readable
import Theorems.Thm_FunctionalInequalities_Analysis_local_taylor_two_readable

section
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT12C1QuadraticSubgradientImage
open MeasureTheory Set Matrix
section
/-- **Subgradient images of a positive definite quadratic are exact affine images, with volume
`det A · vol G`** (weak Letwin route). -/
theorem FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) {G : Set (EuclideanSpace ℝ (Fin n))}
    (hG : MeasurableSet G) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage (quadraticAt A x₀ b c) G) =
      ENNReal.ofReal A.det * (volume : Measure (EuclideanSpace ℝ (Fin n))) G := by
  have _hG : MeasurableSet G := hG
  exact volume_subgradientImage_quadraticAt_aux_readable hA x₀ b c
end
end LT12C1QuadraticSubgradientImage
end
end

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12C2TaylorHessianBound
section
/-- **Second-order Taylor bound with the coordinate Hessian** (weak Letwin route, viscosity tests):
for `ψ` twice differentiable at `x₀` (`ContDiffAt ℝ 2`), every `ε > 0` admits `r > 0` with
`|ψ x − ψ x₀ − Dψ(x₀)(x − x₀) − ½ ⟪x − x₀, ∇²ψ(x₀)(x − x₀)⟫| ≤ ε ‖x − x₀‖²` on `ball x₀ r`. -/
theorem FunctionalInequalities.Analysis.exists_taylor_two_hessianMatrix_bound {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)} (hψ : ContDiffAt ℝ 2 ψ x₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ ball x₀ r,
      |ψ x - (ψ x₀ + fderiv ℝ ψ x₀ (x - x₀) +
        (1 / 2) * ⟪x - x₀, Matrix.toEuclideanLin (hessianMatrix ψ x₀) (x - x₀)⟫)| ≤
        ε * ‖x - x₀‖ ^ 2 := by
  rcases local_taylor_two_readable hψ hε with ⟨r, hr, hrbound⟩
  refine ⟨r, hr, ?_⟩
  intro x hx
  rw [hessianMatrix_quadratic_readable]
  exact hrbound x hx
end
end LT12C2TaylorHessianBound
section LT12C4ViscosityTouchingAssembly
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
private lemma FunctionalInequalities.Analysis.touching_positive_parameter {P : ℝ → Prop}
    (hP : ∀ᶠ t in 𝓝 (0 : ℝ), P t) :
    ∃ t > 0, P t := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨r / 2, half_pos hr, hsub ?_⟩
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
  linarith
private lemma FunctionalInequalities.Analysis.touching_closedBall {n : ℕ}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {P : EuclideanSpace ℝ (Fin n) → Prop}
    (hP : ∀ᶠ x in 𝓝 x₀, P x) :
    ∃ r > 0, ∀ x ∈ closedBall x₀ r, P x := by
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro x hx
  exact hsub (closedBall_subset_ball (by linarith : R / 2 < R) hx)
private lemma FunctionalInequalities.Analysis.touching_quadratic_shift {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ b x : EuclideanSpace ℝ (Fin n)) (c d t : ℝ) :
    quadraticAt (A + t • 1) x₀ b c x =
      quadraticAt A x₀ b d x + (c - d) + t / 2 * ‖x - x₀‖ ^ 2 := by
  unfold quadraticAt
  have ha :
      Matrix.toEuclideanLin (A + t • 1) (x - x₀) =
        Matrix.toEuclideanLin A (x - x₀) + t • (x - x₀) := by
    change Matrix.toLpLin 2 2 (A + t • 1) (x - x₀) = _
    rw [map_add, map_smul, Matrix.toLpLin_one]
    rfl
  rw [ha, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring
private lemma FunctionalInequalities.Analysis.touching_comparison_set {n : ℕ}
    {v w : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv : ConvexOn ℝ univ v) (hw : ConvexOn ℝ univ w)
    {x₀ : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hcenter : w x₀ < v x₀)
    (hsphere : ∀ x, ‖x - x₀‖ = r → v x ≤ w x) :
    ∃ G : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen G ∧ G ⊆ ball x₀ r ∧ Bornology.IsBounded G ∧ G.Nonempty ∧
        subgradientImage v G ⊆ subgradientImage w G := by
  have hvc : Continuous v :=
    continuousOn_univ.mp (hv.continuousOn isOpen_univ)
  have hwc : Continuous w :=
    continuousOn_univ.mp (hw.continuousOn isOpen_univ)
  let G : Set (EuclideanSpace ℝ (Fin n)) :=
    ball x₀ r ∩ {x | w x < v x}
  have hGo : IsOpen G := isOpen_ball.inter (isOpen_lt hwc hvc)
  have hGball : G ⊆ ball x₀ r := fun _ hx => hx.1
  have hGb : Bornology.IsBounded G := isBounded_ball.subset hGball
  have hGeq : ∀ x ∈ frontier G, w x = v x := by
    intro x hx
    have hxclG : x ∈ closure G := frontier_subset_closure hx
    have hxclB : x ∈ closedBall x₀ r :=
      closure_minimal
        (fun y hy => ball_subset_closedBall (hGball (show y ∈ G from hy)))
        isClosed_closedBall hxclG
    have hle : w x ≤ v x := by
      apply closure_minimal
        (s := G) (t := {y | w y ≤ v y}) ?_
        (isClosed_le hwc hvc) hxclG
      intro y hy
      change w y ≤ v y
      exact le_of_lt (show w y < v y from hy.2)
    have hxnotG : x ∉ G := by
      rw [hGo.frontier_eq] at hx
      exact hx.2
    by_cases hxb : x ∈ ball x₀ r
    · exact le_antisymm hle
        (le_of_not_gt fun hlt => hxnotG ⟨hxb, hlt⟩)
    · have hnle : ‖x - x₀‖ ≤ r := by
        simpa only [mem_closedBall, dist_eq_norm] using hxclB
      have hnge : r ≤ ‖x - x₀‖ := by
        apply le_of_not_gt
        intro hlt
        apply hxb
        simpa only [mem_ball, dist_eq_norm] using hlt
      exact le_antisymm hle (hsphere x (le_antisymm hnle hnge))
  refine ⟨G, hGo, hGball, hGb, ⟨x₀, mem_ball_self hr, hcenter⟩, ?_⟩
  exact subgradientImage_subset_of_le_readable hw hv hGo hGb
    (fun x hx => le_of_lt (show w x < v x from hx.2)) hGeq
private lemma FunctionalInequalities.Analysis.touching_cancel_volume {n : ℕ}
    {G : Set (EuclideanSpace ℝ (Fin n))}
    (hpos : 0 < volume G) (hfin : volume G < ∞)
    {a b : ℝ} (hb : 0 ≤ b)
    (h : ENNReal.ofReal a * volume G ≤ ENNReal.ofReal b * volume G) :
    a ≤ b := by
  apply (ENNReal.ofReal_le_ofReal_iff hb).mp
  exact
    (ENNReal.mul_le_mul_iff_right (ne_of_gt hpos) (ne_of_lt hfin)).mp
      (by simpa only [mul_comm] using h)
set_option maxHeartbeats 800000 in
/-- **Upper touching test for an Alexandrov solution** (weak Letwin route, viscosity inequality): if the subgradient images of the convex `u` on open subsets of `Ω` carry the density `f`
(`vol (∂u(G)) = ∫_G f`), `f` is continuous at `x₀ ∈ Ω`, and a `C²` function `ψ` touches `u` from above
at `x₀` (`u ≤ ψ` near `x₀`, `u x₀ = ψ x₀`), then `f x₀ ≤ det ∇²ψ(x₀)` (standard coordinates of
`EuclideanSpace ℝ (Fin n)`, `hessianMatrix ψ x₀ i j = D²ψ(x₀)(eᵢ, eⱼ)`). -/
theorem solution {n : ℕ} {u f ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (FunctionalInequalities.Analysis.subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (f x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (hf : ContinuousAt f x₀)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    f x₀ ≤ (FunctionalInequalities.Probability.Stein.hessianMatrix ψ x₀).det := by
  classical
  apply le_of_not_gt
  intro hbad
  let A := FunctionalInequalities.Probability.Stein.hessianMatrix ψ x₀
  have hA : A.PosSemidef :=
    FunctionalInequalities.Analysis.posSemidef_hessianMatrix_of_upper_touch_readable hconv hψ hcontact htouch
  change A.det < f x₀ at hbad
  obtain ⟨a, hAa, haf⟩ := exists_between hbad
  have hdcont : Continuous (fun t : ℝ => (A + (4 * t) • 1).det) :=
    (continuous_const.add
      ((continuous_const.mul continuous_id).smul continuous_const)).matrix_det
  have hdnear : ∀ᶠ t : ℝ in 𝓝 0, (A + (4 * t) • 1).det < a :=
    hdcont.continuousAt.eventually_lt continuous_const.continuousAt
      (by simpa using hAa)
  obtain ⟨ε, hε, hdet⟩ := FunctionalInequalities.Analysis.touching_positive_parameter hdnear
  let M : Matrix (Fin n) (Fin n) ℝ := A + (4 * ε) • 1
  have hM : M.PosDef := by
    dsimp only [M]
    simpa only [add_comm] using
      (Matrix.PosDef.one.smul (show 0 < 4 * ε by positivity)).add_posSemidef hA
  have hMdet : M.det < a := hdet
  let b : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ ψ x₀)
  let q := FunctionalInequalities.Analysis.quadraticAt A x₀ b (ψ x₀)
  obtain ⟨ρ, hρ, htaylor⟩ := FunctionalInequalities.Analysis.exists_taylor_two_hessianMatrix_bound hψ hε
  have htaylor' (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball x₀ ρ) :
      |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    simpa only [q, A, b, FunctionalInequalities.Analysis.quadraticAt, InnerProductSpace.toDual_symm_apply]
      using htaylor x hx
  have hfnear : ∀ᶠ x in 𝓝 x₀, a < f x :=
    continuous_const.continuousAt.eventually_lt hf haf
  have hnear : ∀ᶠ x in 𝓝 x₀,
      x ∈ Ω ∧ u x ≤ ψ x ∧ a ≤ f x ∧
        |ψ x - q x| ≤ ε * ‖x - x₀‖ ^ 2 := by
    filter_upwards [hΩ.mem_nhds hx₀, htouch, hfnear, ball_mem_nhds x₀ hρ]
      with x hxΩ hxu hxf hxt
    exact ⟨hxΩ, hxu, le_of_lt hxf, htaylor' x hxt⟩
  obtain ⟨r, hr, hlocal⟩ := FunctionalInequalities.Analysis.touching_closedBall hnear
  let w := FunctionalInequalities.Analysis.quadraticAt M x₀ b (ψ x₀ - ε * r ^ 2)
  have hwconv : ConvexOn ℝ univ w :=
    FunctionalInequalities.Analysis.convexOn_quadraticAt_readable hM.posSemidef x₀ b (ψ x₀ - ε * r ^ 2)
  have hwformula (x : EuclideanSpace ℝ (Fin n)) :
      w x = q x - ε * r ^ 2 + 2 * ε * ‖x - x₀‖ ^ 2 := by
    dsimp only [w, M, q]
    rw [FunctionalInequalities.Analysis.touching_quadratic_shift A x₀ b x
      (ψ x₀ - ε * r ^ 2) (ψ x₀) (4 * ε)]
    ring
  have hwcenter : w x₀ = ψ x₀ - ε * r ^ 2 := by
    simp [w, FunctionalInequalities.Analysis.quadraticAt]
  have hcenter : w x₀ < u x₀ := by
    rw [hwcenter, hcontact]
    have hpos : 0 < ε * r ^ 2 := mul_pos hε (sq_pos_of_pos hr)
    linarith
  have hsphere : ∀ x, ‖x - x₀‖ = r → u x ≤ w x := by
    intro x hxr
    have hx : x ∈ closedBall x₀ r := by
      simpa only [mem_closedBall, dist_eq_norm, hxr] using (le_refl r)
    have hloc := hlocal x hx
    have he := (abs_le.mp hloc.2.2.2).2
    rw [hxr] at he
    rw [hwformula, hxr]
    nlinarith [hloc.2.1]
  obtain ⟨G, hGo, hGball, hGb, hGne, hcomp⟩ :=
    FunctionalInequalities.Analysis.touching_comparison_set hconv hwconv hr hcenter hsphere
  have hGΩ : G ⊆ Ω := by
    intro x hx
    exact (hlocal x (ball_subset_closedBall (hGball hx))).1
  have hGpos : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))) G :=
    IsOpen.measure_pos volume hGo hGne
  have hGfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) G < ∞ :=
    hGb.measure_lt_top
  have hmul :
      ENNReal.ofReal a * volume G ≤ ENNReal.ofReal M.det * volume G := by
    calc
      ENNReal.ofReal a * volume G =
          ∫⁻ x in G, ENNReal.ofReal a ∂volume :=
        (setLIntegral_const G (ENNReal.ofReal a)).symm
      _ ≤ ∫⁻ x in G, ENNReal.ofReal (f x) ∂volume := by
        apply setLIntegral_mono' hGo.measurableSet
        intro x hx
        exact ENNReal.ofReal_mono
          (hlocal x (ball_subset_closedBall (hGball hx))).2.2.1
      _ = volume (FunctionalInequalities.Analysis.subgradientImage u G) := (hMA G hGo hGΩ).symm
      _ ≤ volume (FunctionalInequalities.Analysis.subgradientImage w G) := measure_mono hcomp
      _ = ENNReal.ofReal M.det * volume G :=
        FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt hM x₀ b
          (ψ x₀ - ε * r ^ 2) hGo.measurableSet
  have hcoef : a ≤ M.det :=
    FunctionalInequalities.Analysis.touching_cancel_volume hGpos hGfin hM.det_pos.le hmul
  exact (not_le_of_gt hMdet) hcoef
