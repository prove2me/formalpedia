-- Prove2me | solution 1 for EthierKurtz.resolvent_positive_interior_step
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T02:53:00.109631+00:00
-- url     : https://prove2.me/submissions/162e268b-6fe8-4116-8ba1-6713708d43c6

import Mathlib
import Theorems.Thm_EthierKurtz_posSemidef_frobenius_nonneg

open scoped Topology

theorem solution {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    {gval lam : ℝ}
    (hopen : IsOpen Ω) (hx : x₀ ∈ Ω)
    (hC : ContDiffOn ℝ 2 u Ω)
    (hmin : IsLocalMin u x₀)
    (hH : ∀ v, 0 ≤ (fderiv ℝ (fun y => fderiv ℝ u y v) x₀) v)
    (ha : (a x₀).PosSemidef)
    (hId : gval = (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
      a x₀ i j * fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x₀
        (EuclideanSpace.single i 1)) + fderiv ℝ u x₀ (b x₀))
    (hlam : 0 < lam) (hu0 : u x₀ < 0)
    (hineq : 0 ≤ lam * u x₀ - gval) :
    False := by
  set H : Fin d → Fin d → ℝ := fun i j =>
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x₀
      (EuclideanSpace.single i 1) with hHdef
  set Hs : Matrix (Fin d) (Fin d) ℝ := fun i j => (H i j + H j i) / 2 with hHsdef
  have hgrad : fderiv ℝ u x₀ = 0 := IsLocalMin.fderiv_eq_zero hmin
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hx)
  set B := Metric.ball x₀ r₀ with hBdef
  have hBnbhd : B ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ hr₀
  have hsB : ContDiffOn ℝ 2 u B := hC.mono hsub
  have hU : UniqueDiffOn ℝ B :=
    uniqueDiffOn_convex (convex_ball x₀ r₀) (by
      have hInt : interior B = B := Metric.isOpen_ball.interior_eq
      rw [hInt]
      exact ⟨x₀, by rw [Metric.mem_ball, dist_self]; exact hr₀⟩)
  have hsB11 : ContDiffOn ℝ (1 + 1) u B := hsB
  have hHdiffv : ∀ v, DifferentiableAt ℝ (fun y => fderiv ℝ u y v) x₀ := by
    intro v
    have hHW : ContDiffOn ℝ 1 (fun x => fderivWithin ℝ u B x v) B :=
      ((contDiffOn_succ_iff_fderiv_apply hU).mp hsB11).2.2 v
    have hW : DifferentiableOn ℝ (fun x => fderivWithin ℝ u B x v) B :=
      ContDiffOn.differentiableOn hHW one_ne_zero
    have hWx₀ : DifferentiableAt ℝ (fun x => fderivWithin ℝ u B x v) x₀ :=
      hW.differentiableAt hBnbhd
    have heq : (fun y => fderiv ℝ u y v) =ᶠ[𝓝 x₀]
        (fun x => fderivWithin ℝ u B x v) :=
      Filter.eventuallyEq_of_mem hBnbhd (fun x hxB => by
        have hxnbhd : B ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hxB
        rw [fderivWithin_of_mem_nhds hxnbhd])
    exact hWx₀.congr_of_eventuallyEq heq
  have hexp : ∀ v : EuclideanSpace ℝ (Fin d),
      v = ∑ i : Fin d, (v.ofLp i) • EuclideanSpace.single i 1 := by
    intro v
    have h := (EuclideanSpace.basisFun _ _).sum_repr v
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at h
    exact h.symm
  have hQ : ∀ (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (w : EuclideanSpace ℝ (Fin d)),
      L w = ∑ i : Fin d, (w.ofLp i) • L (EuclideanSpace.single i 1) := by
    intro L w
    conv_lhs => rw [hexp w]
    rw [map_sum]
    congr 1
    ext i
    rw [map_smul]
  have h1 : ∀ v : EuclideanSpace ℝ (Fin d),
      (fun y => fderiv ℝ u y v)
        = ∑ j : Fin d, ((v.ofLp j) • fun y => fderiv ℝ u y
          (EuclideanSpace.single j 1)) := by
    intro v
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply]
    conv_lhs => rw [hexp v]
    rw [map_sum]
    congr 1
    ext j
    rw [map_smul]
  have hD : ∀ v : EuclideanSpace ℝ (Fin d),
      fderiv ℝ (fun y => fderiv ℝ u y v) x₀
        = ∑ j : Fin d, (v.ofLp j) • fderiv ℝ
          (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x₀ := by
    intro v
    rw [h1 v, fderiv_sum
      (fun j _ => (hHdiffv (EuclideanSpace.single j 1)).const_smul (v.ofLp j))]
    congr 1
    ext j
    rw [fderiv_const_smul (hHdiffv (EuclideanSpace.single j 1))]
  have hexpand : ∀ v : EuclideanSpace ℝ (Fin d),
      fderiv ℝ (fun y => fderiv ℝ u y v) x₀ v
        = ∑ i, ∑ j, (v.ofLp i) * (v.ofLp j) * H i j := by
    intro v
    rw [hQ _ v]
    congr 1
    ext i
    have hDi : fderiv ℝ (fun y => fderiv ℝ u y v) x₀
        (EuclideanSpace.single i 1)
        = ∑ j, (v.ofLp j) • H i j := by
      rw [hD v]
      simp only [sum_apply, smul_apply]
      congr 1
    rw [hDi, Finset.smul_sum]
    congr 1
    ext j
    simp only [smul_eq_mul]
    ring
  have ofLp_sum : ∀ (s : Finset (Fin d))
      (f : Fin d → EuclideanSpace ℝ (Fin d)) (j : Fin d),
      (∑ i ∈ s, f i).ofLp j = ∑ i ∈ s, (f i).ofLp j := by
    intro s f j
    induction s using Finset.induction with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      rw [WithLp.ofLp_add]
      exact congrArg _ ih
  have hcomp164 : ∀ (x : Fin d → ℝ) (j : Fin d),
      (∑ i, x i • EuclideanSpace.single i (1:ℝ)).ofLp j = x j := by
    intro x j
    rw [ofLp_sum]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.single_apply,
      smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hAsymm : ∀ i j : Fin d, a x₀ i j = a x₀ j i := by
    intro i j
    have h := congrFun (congrFun ha.isHermitian i) j
    simp only [Matrix.conjTranspose_apply, star_trivial] at h
    exact h.symm
  have hswap : (∑ i, ∑ j, a x₀ i j * H j i)
      = ∑ i, ∑ j, a x₀ i j * H i j := by
    have h1 : (∑ i, ∑ j, a x₀ i j * H j i)
        = ∑ j, ∑ i, a x₀ i j * H j i := Finset.sum_comm
    have h2 : (∑ j, ∑ i, a x₀ i j * H j i)
        = ∑ i, ∑ j, a x₀ j i * H i j := rfl
    have h3 : (∑ i, ∑ j, a x₀ j i * H i j)
        = ∑ i, ∑ j, a x₀ i j * H i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hAsymm j i]
    exact h1.trans (h2.trans h3)
  have hSeq : (∑ i, ∑ j, a x₀ i j * Hs i j) * 2
      = (∑ i, ∑ j, a x₀ i j * H i j)
        + (∑ i, ∑ j, a x₀ i j * H j i) := by
    calc (∑ i, ∑ j, a x₀ i j * Hs i j) * 2
        = ∑ i, ∑ j, (a x₀ i j * H i j + a x₀ i j * H j i) := by
          simp only [Finset.sum_mul, hHsdef]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hSS' : (∑ i, ∑ j, a x₀ i j * Hs i j)
      = ∑ i, ∑ j, a x₀ i j * H i j := by linarith [hSeq, hswap]
  have hHsHerm : Hs.IsHermitian := by
    ext i j
    rw [Matrix.conjTranspose_apply]
    simp only [hHsdef, star_trivial]
    ring
  have hHsQuad : ∀ x : Fin d → ℝ,
      0 ≤ dotProduct (star x) (Matrix.mulVec Hs x) := by
    intro x
    have hQv := hH (∑ i, x i • EuclideanSpace.single i (1:ℝ))
    rw [hexpand _] at hQv
    simp only [hcomp164] at hQv
    have hexpQ : dotProduct (star x) (Matrix.mulVec Hs x)
        = ∑ i, ∑ j, x i * x j * Hs i j := by
      simp only [dotProduct, Matrix.mulVec, star_trivial]
      congr 1
      ext i
      rw [Finset.mul_sum]
      congr 1
      ext j
      ring
    rw [hexpQ]
    have hconn : (∑ i, ∑ j, x i * x j * Hs i j)
        = ((∑ i, ∑ j, x i * x j * H i j)
          + (∑ i, ∑ j, x i * x j * H j i)) / 2 := by
      have h2 : (∑ i, ∑ j, x i * x j * Hs i j) * 2
          = (∑ i, ∑ j, x i * x j * H i j)
            + (∑ i, ∑ j, x i * x j * H j i) := by
        calc (∑ i, ∑ j, x i * x j * Hs i j) * 2
            = ∑ i, ∑ j, (x i * x j * H i j + x i * x j * H j i) := by
              simp only [Finset.sum_mul, hHsdef]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
          _ = _ := by simp only [Finset.sum_add_distrib]
      linarith
    have hswapQ : (∑ i, ∑ j, x i * x j * H j i)
        = ∑ i, ∑ j, x i * x j * H i j := by
      have h1 : (∑ i, ∑ j, x i * x j * H j i)
          = ∑ j, ∑ i, x i * x j * H j i := Finset.sum_comm
      have h2 : (∑ j, ∑ i, x i * x j * H j i)
          = ∑ i, ∑ j, x j * x i * H i j := rfl
      have h3 : (∑ i, ∑ j, x j * x i * H i j)
          = ∑ i, ∑ j, x i * x j * H i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      exact h1.trans (h2.trans h3)
    have hQQ : (∑ i, ∑ j, x i * x j * Hs i j)
        = ∑ i, ∑ j, x i * x j * H i j := by linarith [hconn, hswapQ]
    rw [hQQ]
    exact hQv
  have hHs : Hs.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHsHerm hHsQuad
  have hTr := EthierKurtz.posSemidef_frobenius_nonneg _ _ ha hHs
  have hSnn : 0 ≤ (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
      a x₀ i j * H i j) := by
    rw [← hSS']
    exact mul_nonneg (by positivity) hTr
  have hDu0 : fderiv ℝ u x₀ (b x₀) = 0 := by
    rw [hgrad]
    simp
  have hId' : gval = (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
      a x₀ i j * H i j) := by
    rw [hId, hDu0, add_zero]
  have hu0neg : lam * u x₀ < 0 := mul_neg_of_pos_of_neg hlam hu0
  linarith
