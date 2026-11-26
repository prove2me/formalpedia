-- Prove2me | solution 1 for FiniteEnergyPlane.hopf_lemma_disk
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-26T17:35:32.012532+00:00
-- url     : https://prove2.me/submissions/d7f17892-37af-49d3-9c6d-11916a1817cf

import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Complex.Basic
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_eq_of_isMaxOn_of_laplacian_nonneg

open Laplacian Metric Filter Topology

namespace FiniteEnergyPlane

noncomputable section

/-- The Gaussian barrier around `c`. -/
def ampW (α R : ℝ) (c : ℂ) (z : ℂ) : ℝ := Real.exp (-α * ‖z - c‖ ^ 2) - Real.exp (-α * R ^ 2)

/-- Its derivative. -/
def ampDW (α : ℝ) (c : ℂ) (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (-2 * α * Real.exp (-α * ‖z - c‖ ^ 2)) • innerSL ℝ (z - c)

theorem amp_hasFDerivAt_W (α R : ℝ) (c z : ℂ) :
    HasFDerivAt (ampW α R c) (ampDW α c z) z := by
  have h1 : HasFDerivAt (fun y : ℂ => ‖y - c‖ ^ 2) (2 • (innerSL ℝ (z - c)).comp
      (ContinuousLinearMap.id ℝ ℂ)) z :=
    ((hasFDerivAt_id z).sub_const c).norm_sq
  have h2 := (h1.const_mul (-α)).exp
  have h3 := h2.sub_const (Real.exp (-α * R ^ 2))
  refine h3.congr_fderiv ?_
  ext v
  simp only [ampDW, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, innerSL_apply_apply, nsmul_eq_mul]
  push_cast
  ring

theorem amp_hasFDerivAt_DW_apply (α : ℝ) (c z v : ℂ) :
    HasFDerivAt (fun y => ampDW α c y v)
      ((-2 * α * Real.exp (-α * ‖z - c‖ ^ 2)) • innerSL ℝ v +
        (inner ℝ (z - c) v * (-2 * α * Real.exp (-α * ‖z - c‖ ^ 2) * (-α))) •
          (2 • innerSL ℝ (z - c))) z := by
  have h1 : HasFDerivAt (fun y : ℂ => ‖y - c‖ ^ 2) (2 • (innerSL ℝ (z - c)).comp
      (ContinuousLinearMap.id ℝ ℂ)) z :=
    ((hasFDerivAt_id z).sub_const c).norm_sq
  have hs := ((h1.const_mul (-α)).exp).const_mul (-2 * α)
  have hi : HasFDerivAt (fun y : ℂ => inner ℝ (y - c) v) (innerSL ℝ v) z := by
    have : (fun y : ℂ => inner ℝ (y - c) v) = fun y => (innerSL ℝ v) (y - c) := by
      funext y; simp [real_inner_comm]
    rw [this]
    exact (innerSL ℝ v).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const c)
  have hp := hs.mul hi
  have hfun : (fun y => ampDW α c y v) =
      fun y => -2 * α * Real.exp (-α * ‖y - c‖ ^ 2) * inner ℝ (y - c) v := by
    funext y; simp only [ampDW, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [hfun]
  refine hp.congr_fderiv ?_
  ext w
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    innerSL_apply_apply, nsmul_eq_mul]
  push_cast
  ring

theorem amp_contDiff_W (α R : ℝ) (c : ℂ) : ContDiff ℝ 2 (ampW α R c) := by
  unfold ampW
  have hq : ContDiff ℝ 2 (fun z : ℂ => ‖z - c‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  exact ((hq.const_smul (-α)).exp).sub contDiff_const

theorem amp_laplacian_W (α R : ℝ) (c z : ℂ) :
    Δ (ampW α R c) z =
      4 * α * Real.exp (-α * ‖z - c‖ ^ 2) * (α * ‖z - c‖ ^ 2 - 1) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hfd : fderiv ℝ (ampW α R c) = ampDW α c := by
    funext y; exact (amp_hasFDerivAt_W α R c y).fderiv
  rw [hfd]
  have hDW : ∀ v : ℂ, fderiv ℝ (ampDW α c) z v v = fderiv ℝ (fun y => ampDW α c y v) z v := by
    intro v
    have hd : DifferentiableAt ℝ (ampDW α c) z := by
      unfold ampDW
      have hq : DifferentiableAt ℝ (fun y : ℂ => ‖y - c‖ ^ 2) z :=
        (((hasFDerivAt_id z).sub_const c).norm_sq).differentiableAt
      have hs : DifferentiableAt ℝ (fun y : ℂ => -2 * α * Real.exp (-α * ‖y - c‖ ^ 2)) z :=
        ((hq.const_mul (-α)).exp).const_mul _
      exact hs.smul (((innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).differentiableAt).comp z
          (differentiableAt_id.sub_const c))
    rw [fderiv_clm_apply hd (differentiableAt_const v)]
    simp
  rw [hDW, hDW, (amp_hasFDerivAt_DW_apply α c z 1).fderiv,
    (amp_hasFDerivAt_DW_apply α c z Complex.I).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    smul_eq_mul, nsmul_eq_mul]
  have hn : ‖z - c‖ ^ 2 = (z - c).re ^ 2 + (z - c).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [Complex.inner, map_one, mul_one, Complex.conj_I, Complex.one_re, Complex.I_re,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_im, one_mul]
  rw [hn]
  push_cast
  ring_nf
  simp
  ring

end

end FiniteEnergyPlane

namespace FiniteEnergyPlane

theorem amp_W_eq_zero {α R : ℝ} {c z : ℂ} (hR : 0 ≤ R) (hz : dist z c = R) :
    ampW α R c z = 0 := by
  unfold ampW; rw [← dist_eq_norm, hz]; ring

theorem amp_W_le_one (α R : ℝ) (hα : 0 ≤ α) (c z : ℂ) : ampW α R c z ≤ 1 := by
  unfold ampW
  have h1 : Real.exp (-α * ‖z - c‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖z - c‖]
  have h2 : 0 < Real.exp (-α * R ^ 2) := Real.exp_pos _
  linarith

theorem amp_laplacian_W_pos {R : ℝ} (hR : 0 < R) (c z : ℂ) (hz : R / 2 < dist z c) :
    0 < Δ (ampW (8 / R ^ 2) R c) z := by
  rw [amp_laplacian_W]
  have hα : 0 < 8 / R ^ 2 := by positivity
  have hd : (R / 2) ^ 2 < ‖z - c‖ ^ 2 := by
    rw [← dist_eq_norm]; exact pow_lt_pow_left₀ hz (by linarith) two_ne_zero
  have h2 : 1 < 8 / R ^ 2 * ‖z - c‖ ^ 2 := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith
  have := Real.exp_pos (-(8 / R ^ 2) * ‖z - c‖ ^ 2)
  have h3 : 0 < 8 / R ^ 2 * ‖z - c‖ ^ 2 - 1 := by linarith
  positivity

/-- Hopf's boundary point lemma on a disk in `ℂ`. -/
theorem hopf_lemma_disk_aux {c ζ : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℝ} {f' : ℂ →L[ℝ] ℝ}
    (hcont : ContinuousOn f (closedBall c R)) (hf : ContDiffOn ℝ 2 f (ball c R))
    (hΔ : ∀ z ∈ ball c R, 0 ≤ Δ f z) (hlt : ∀ z ∈ ball c R, f z < f ζ)
    (hζ : ζ ∈ sphere c R) (hd : HasFDerivWithinAt f f' (closedBall c R) ζ) :
    0 < f' (ζ - c) := by
  have hζR : dist ζ c = R := hζ
  -- the inner sphere
  set K : Set ℂ := sphere c (R / 2) with hK
  have hKsub : K ⊆ ball c R := by
    intro z hz
    rw [mem_sphere] at hz
    rw [mem_ball, hz]; linarith
  have hKc : IsCompact K := isCompact_sphere c (R / 2)
  have hKne : K.Nonempty := NormedSpace.sphere_nonempty.2 (by linarith)
  obtain ⟨p₀, hp₀K, hp₀max⟩ := hKc.exists_isMaxOn hKne
    ((hcont.mono ball_subset_closedBall).mono hKsub)
  set δ : ℝ := f ζ - f p₀ with hδ
  have hδpos : 0 < δ := by have := hlt p₀ (hKsub hp₀K); linarith
  -- `f ≤ f ζ` on the closed ball
  have hle : ∀ z ∈ closedBall c R, f z ≤ f ζ := by
    intro z hz
    have hcl : z ∈ closure (ball c R) := by rw [closure_ball c hR.ne']; exact hz
    exact ContinuousWithinAt.closure_le hcl ((hcont z hz).mono ball_subset_closedBall)
      continuousWithinAt_const (fun y hy => (hlt y hy).le)
  set α : ℝ := 8 / R ^ 2 with hαdef
  have hα : 0 < α := by positivity
  set ε : ℝ := δ / 2 with hε
  have hεpos : 0 < ε := by positivity
  set w : ℂ → ℝ := ampW α R c with hw
  set g : ℂ → ℝ := fun z => ε * w z - f ζ with hg
  set v : ℂ → ℝ := fun z => f z + g z with hv
  set Kc : Set ℂ := closedBall c R \ ball c (R / 2) with hKcdef
  have hKcc : IsCompact Kc := (isCompact_closedBall c R).diff isOpen_ball
  have hζKc : ζ ∈ Kc := by
    refine ⟨mem_closedBall.2 hζR.le, ?_⟩
    rw [mem_ball, hζR]; linarith
  have hgC : ContDiff ℝ 2 g := ((amp_contDiff_W α R c).const_smul ε).sub contDiff_const
  have hvcont : ContinuousOn v Kc :=
    (hcont.mono Set.diff_subset).add hgC.continuous.continuousOn
  have hΔg : ∀ z, Δ g z = ε * Δ w z := by
    intro z
    have : g = (ε • w) - fun _ => f ζ := by funext y; simp [hg, smul_eq_mul]
    have h1 : ContDiffAt ℝ 2 (ε • w) z := (amp_contDiff_W α R c).contDiffAt.const_smul ε
    rw [this, h1.laplacian_sub (contDiffAt_const (c := f ζ)),
      InnerProductSpace.laplacian_smul ε (amp_contDiff_W α R c).contDiffAt]
    simp [smul_eq_mul, hw]
  -- `v ≤ 0` on the closed annulus
  have hvle : ∀ z ∈ Kc, v z ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨z₁, hz₁, hz₁pos⟩ := hcon
    obtain ⟨p, hpK, hpmax⟩ := hKcc.exists_isMaxOn ⟨ζ, hζKc⟩ hvcont
    have hvp : 0 < v p := lt_of_lt_of_le hz₁pos (hpmax hz₁)
    have hp1 : dist p c ≤ R := mem_closedBall.1 hpK.1
    have hp2 : R / 2 ≤ dist p c := by
      have := hpK.2; rw [mem_ball] at this; linarith
    rcases hp1.lt_or_eq with hp1 | hp1
    · rcases hp2.lt_or_eq with hp2 | hp2
      · -- interior point of the annulus
        set A : Set ℂ := ball c R ∩ (closedBall c (R / 2))ᶜ with hA
        have hAo : IsOpen A := isOpen_ball.inter isClosed_closedBall.isOpen_compl
        have hpA : p ∈ A := ⟨mem_ball.2 hp1, fun h => by
          rw [mem_closedBall] at h; linarith⟩
        obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.1 hAo p hpA
        have hAKc : A ⊆ Kc := by
          intro z hz
          refine ⟨ball_subset_closedBall hz.1, fun h => hz.2 (ball_subset_closedBall h)⟩
        have hAball : A ⊆ ball c R := fun z hz => hz.1
        have hvC : ContDiffOn ℝ 2 v (ball p r) :=
          (hf.mono (hrA.trans hAball)).add hgC.contDiffOn
        have hΔv : ∀ z ∈ A, Δ v z = Δ f z + ε * Δ w z := by
          intro z hz
          have hfz : ContDiffAt ℝ 2 f z := hf.contDiffAt (isOpen_ball.mem_nhds hz.1)
          have : v = f + g := rfl
          rw [this, hfz.laplacian_add hgC.contDiffAt, hΔg]
        have hΔwA : ∀ z ∈ A, 0 < Δ w z := by
          intro z hz
          have : R / 2 < dist z c := by
            have := hz.2; rw [Set.mem_compl_iff, mem_closedBall] at this; linarith
          exact amp_laplacian_W_pos hR c z this
        have hconst := eq_of_isMaxOn_of_laplacian_nonneg isOpen_ball
          (convex_ball p r).isPreconnected hvC
          (fun z hz => by
            rw [hΔv z (hrA hz)]
            have := hΔ z (hAball (hrA hz)); have := hΔwA z (hrA hz)
            positivity)
          (mem_ball_self hr) (fun z hz => hpmax (hAKc (hrA hz)))
        have hev : v =ᶠ[𝓝 p] fun _ => v p :=
          Filter.eventually_of_mem (ball_mem_nhds p hr) hconst
        have h0 : Δ v p = 0 := by
          rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]; simp
        have hpos : 0 < Δ v p := by
          rw [hΔv p hpA]
          have := hΔ p (hAball hpA); have := hΔwA p hpA
          positivity
        linarith
      · -- inner sphere
        have hpK' : p ∈ K := by rw [hK, mem_sphere]; exact hp2.symm
        have h1 : f p ≤ f p₀ := hp₀max hpK'
        have h2 : w p ≤ 1 := amp_W_le_one α R hα.le c p
        have : v p ≤ f p₀ - f ζ + ε := by
          simp only [hv, hg]; nlinarith
        linarith
    · -- outer sphere
      have h1 : w p = 0 := amp_W_eq_zero hR.le hp1
      have h2 : f p ≤ f ζ := hle p hpK.1
      have : v p ≤ 0 := by simp only [hv, hg, h1]; linarith
      linarith
  -- `ζ` is a maximum point of `v` on the annulus
  have hvζ : v ζ = 0 := by
    simp only [hv, hg, hw, amp_W_eq_zero hR.le hζR]; ring
  have hM : IsMaxOn v Kc ζ := fun z hz => by
    show v z ≤ v ζ
    rw [hvζ]; exact hvle z hz
  have hmaxζ : IsLocalMaxOn v Kc ζ := hM.localize
  have hdv : HasFDerivWithinAt v (f' + ε • ampDW α c ζ) Kc ζ := by
    have h1 : HasFDerivWithinAt f f' Kc ζ := hd.mono Set.diff_subset
    have h2 : HasFDerivWithinAt g (ε • ampDW α c ζ) Kc ζ :=
      (((amp_hasFDerivAt_W α R c ζ).const_smul ε).sub_const (f ζ)).hasFDerivWithinAt
    exact h1.add h2
  set y : ℂ := (c - ζ) / 2 with hy
  have hseg : segment ℝ ζ (ζ + y) ⊆ Kc := by
    rw [segment_eq_image']
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have hdist : dist (ζ + t • (ζ + y - ζ)) c = (1 - t / 2) * R := by
      have : ζ + t • (ζ + y - ζ) - c = ((1 - t / 2 : ℝ) : ℂ) * (ζ - c) := by
        simp only [hy, add_sub_cancel_left, Complex.real_smul]; push_cast; ring
      rw [dist_eq_norm, this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), ← dist_eq_norm, hζR]
    refine ⟨mem_closedBall.2 ?_, ?_⟩
    · rw [hdist]; nlinarith
    · rw [mem_ball, hdist]; nlinarith
  have hcone := hmaxζ.hasFDerivWithinAt_nonpos hdv (mem_posTangentConeAt_of_segment_subset hseg)
  have hDW : ampDW α c ζ y = α * Real.exp (-α * ‖ζ - c‖ ^ 2) * ‖ζ - c‖ ^ 2 := by
    simp only [ampDW, ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, hy]
    have : (c - ζ) / 2 = (-(1 / 2 : ℝ)) • (ζ - c) := by
      rw [Complex.real_smul]; push_cast; ring
    rw [this, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hDWpos : 0 < ampDW α c ζ y := by
    rw [hDW]
    have : 0 < ‖ζ - c‖ := by rw [← dist_eq_norm, hζR]; exact hR
    positivity
  have hf'y : f' y < 0 := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] at hcone
    nlinarith
  have hzc : ζ - c = (-2 : ℝ) • y := by
    rw [hy, Complex.real_smul]; push_cast; ring
  rw [hzc, map_smul, smul_eq_mul]; linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open Laplacian Metric

theorem solution {c ζ : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℝ} {f' : ℂ →L[ℝ] ℝ}
    (hcont : ContinuousOn f (closedBall c R)) (hf : ContDiffOn ℝ 2 f (ball c R))
    (hΔ : ∀ z ∈ ball c R, 0 ≤ Δ f z) (hlt : ∀ z ∈ ball c R, f z < f ζ)
    (hζ : ζ ∈ sphere c R) (hd : HasFDerivWithinAt f f' (closedBall c R) ζ) :
    0 < f' (ζ - c) :=
  hopf_lemma_disk_aux hR hcont hf hΔ hlt hζ hd
