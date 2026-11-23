-- Prove2me | solution 1 for DelaunayStretch.corollary_4_10_sliding_disk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:49:18.804193+00:00
-- url     : https://prove2.me/submissions/ed8318a5-c2db-4218-9ac3-c6c00b2a628f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DelaunayStretch_lemma_4_2_range_of_coordinates
import Theorems.Thm_DelaunayStretch_lemma_4_4_pencil
import Theorems.Thm_DelaunayStretch_lemma_4_8_derivatives_along_curves

open DelaunayStretch

theorem solution (U : ℝ) (H : R4 → ℝ)
    (hH : ∃ P : PiecewiseC1 H, CondH0 H ∧ CondH4 U P) (aG bG : ℂ) (ha : 0 < aG.im)
    (hb : bG.im < 0) (δ : ℝ) (hδ : |δ| ≤ dist aG bG) (X₁ X₂ : ℝ) (hX : X₁ < X₂) :
    potential H U (pencilState aG bG δ X₂) ≤ potential H U (pencilState aG bG δ X₁) := by
  obtain ⟨P, h0, h4⟩ := hH
  obtain ⟨hSig, -, -, -⟩ := lemma_4_2_range_of_coordinates
  obtain ⟨-, -, hP⟩ := lemma_4_4_pencil aG bG ha hb
  obtain ⟨hgs, hγ, hφ, hθ, hψ, -, -, hpot, -⟩ := hP δ hδ
  set z : ℝ → R4 := fun X => (pencilState aG bG δ X).angularCoords with hz_def
  have hzC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z := by
    have : z = fun X => ((pencilState aG bG δ X).gammaCoord, (pencilState aG bG δ X).phiCoord,
        (pencilState aG bG δ X).thetaCoord, (pencilState aG bG δ X).psiCoord) := rfl
    rw [this]
    exact hγ.prodMk (hφ.prodMk (hθ.prodMk hψ))
  have hzC1 : ContDiffOn ℝ 1 z (Set.Icc X₁ X₂) :=
    (hzC.of_le (by exact_mod_cast le_top)).contDiffOn
  have hmaps : Set.MapsTo z (Set.Icc X₁ X₂) OmegaTimesR := fun X _ => (hSig _ (hgs X)).1
  obtain ⟨hAC, hae⟩ := lemma_4_8_derivatives_along_curves H h0 P X₁ X₂ hX.le z hzC1 hmaps
  set f : ℝ → ℝ := fun X => potential H U (pencilState aG bG δ X) with hf_def
  -- absolute continuity of f
  set d := dist aG bG
  have hd : 0 < d := by
    apply dist_pos.mpr; intro h; rw [h] at ha; linarith
  set rr : ℝ → ℝ := fun X => Real.sqrt (X ^ 2 + d ^ 2 / 4) with hrr
  have hrC : ContDiff ℝ 1 rr := by
    apply ContDiff.sqrt (by fun_prop)
    intro X; positivity
  have hθC : ContDiff ℝ 1 (fun X => (pencilState aG bG δ X).thetaCoord) :=
    hθ.of_le (by exact_mod_cast le_top)
  have hfeq : f = fun X => (rr X * (Real.pi / 2 - (pencilState aG bG δ X).thetaCoord) +
      U * ((axisCrossing aG bG).re - ((aG + bG) / 2).re - X * (segNormal aG bG).re)) -
      rr X * H (z X) := by
    funext X
    simp only [hf_def, potential, pencilState, pencilDisk, GateState.crossing, hz_def, rr, d]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    ring
  have hfAC : AbsolutelyContinuousOnInterval f X₁ X₂ := by
    rw [hfeq]
    apply AbsolutelyContinuousOnInterval.sub
    · apply ContDiffOn.absolutelyContinuousOnInterval
      apply ContDiff.contDiffOn
      apply ContDiff.add
      · exact hrC.mul (contDiff_const.sub hθC)
      · fun_prop
    · exact AbsolutelyContinuousOnInterval.fun_mul
        (ContDiffOn.absolutelyContinuousOnInterval hrC.contDiffOn) hAC
  -- a.e. derivative is nonpositive
  have hderiv : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc X₁ X₂)), deriv f t ≤ 0 := by
    have hmem : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc X₁ X₂)), t ∈ Set.Icc X₁ X₂ :=
      MeasureTheory.ae_restrict_mem measurableSet_Icc
    filter_upwards [hae, hmem] with t ht htm
    obtain ⟨g, hg, hHd⟩ := ht
    have := hpot U H t g hHd
    rw [this.deriv]
    exact h4 _ (hSig _ (hgs t)) g hg
  have hint := hfAC.integral_deriv_eq_sub
  have hneg : 0 ≤ ∫ x in X₁..X₂, -deriv f x := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hX.le
    filter_upwards [hderiv] with t ht
    simp only [Pi.zero_apply]; linarith
  rw [intervalIntegral.integral_neg, hint] at hneg
  show f X₂ ≤ f X₁
  linarith
