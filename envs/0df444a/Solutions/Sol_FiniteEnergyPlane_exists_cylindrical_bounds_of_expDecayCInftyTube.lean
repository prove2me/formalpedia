-- Prove2me | solution 1 for FiniteEnergyPlane.exists_cylindrical_bounds_of_expDecayCInftyTube
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T18:40:05.554023+00:00
-- url     : https://prove2.me/submissions/9e731538-c630-40bd-897b-2d9cf2dfbaf3

import Definitions.Def_FiniteEnergyPlane_Tube
import Mathlib



/-!
# X transfer: cylindrical `C²` bounds of a map on `ℂ × ℂ` and their consequences

`CylBound F ρ' C`: on `ℂ × closedBall 0 ρ'`, the first two derivatives of `F` are bounded by `C`
in the cylindrical scale (base directions weighted by `1 / (1 + ‖ζ‖)`).
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Cylindrical `C²` bound. -/
def CylBound (F : ℂ × ℂ → E) (ρ' C : ℝ) : Prop :=
  ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' →
    (∀ h : ℂ × ℂ, ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) ∧
    ∀ h k : ℂ × ℂ, ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
      C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖)

lemma CylBound.nonneg {F : ℂ × ℂ → E} {ρ' C : ℝ} (hρ' : 0 ≤ ρ') (hC : CylBound F ρ' C) :
    0 ≤ C := by
  have h := (hC 0 0 (by simpa using hρ')).1 (0, 1)
  simp only [norm_zero, zero_div, zero_add, norm_one, mul_one] at h
  exact le_trans (norm_nonneg _) h

/-- Mean value estimate along a segment, centred at `ζ₀`. -/
lemma seg_core {Ψ : ℂ × ℂ → E} {ρ' B : ℝ} {ζ₀ ζ₁ w₀ w₁ : ℂ}
    (hw₀ : w₀ ∈ closedBall (0 : ℂ) ρ') (hw₁ : w₁ ∈ closedBall (0 : ℂ) ρ')
    (hζ : ‖ζ₁ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2)
    (hd : ∀ ζ w, w ∈ closedBall (0 : ℂ) ρ' → DifferentiableAt ℝ Ψ (ζ, w))
    (hb : ∀ ζ w (h : ℂ × ℂ), w ∈ closedBall (0 : ℂ) ρ' → ‖ζ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2 →
      ‖fderiv ℝ Ψ (ζ, w) h‖ ≤ B * (2 * ‖h.1‖ / (1 + ‖ζ₀‖) + ‖h.2‖)) :
    ‖Ψ (ζ₁, w₁) - Ψ (ζ₀, w₀)‖ ≤ B * (2 * ‖ζ₁ - ζ₀‖ / (1 + ‖ζ₀‖) + ‖w₁ - w₀‖) := by
  set Δ : ℂ × ℂ := (ζ₁ - ζ₀, w₁ - w₀) with hΔ
  set γ : ℝ → ℂ × ℂ := fun θ => (ζ₀, w₀) + θ • Δ with hγ
  have hγd : ∀ θ : ℝ, HasDerivAt γ Δ θ := fun θ => by
    have h0 : HasDerivAt (fun x : ℝ => x • Δ) ((1 : ℝ) • Δ) θ := (hasDerivAt_id θ).smul_const Δ
    rw [one_smul] at h0
    exact h0.const_add (ζ₀, w₀)
  have hmem : ∀ θ ∈ Set.Icc (0 : ℝ) 1, (γ θ).2 ∈ closedBall (0 : ℂ) ρ' ∧
      ‖(γ θ).1 - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2 := by
    intro θ hθ
    constructor
    · have := (convex_closedBall (0 : ℂ) ρ').add_smul_sub_mem hw₀ hw₁ hθ
      simpa [hγ, hΔ] using this
    · have e : (γ θ).1 - ζ₀ = θ • (ζ₁ - ζ₀) := by simp [hγ, hΔ]
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
      calc θ * ‖ζ₁ - ζ₀‖ ≤ 1 * ‖ζ₁ - ζ₀‖ := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg _)
        _ ≤ (1 + ‖ζ₀‖) / 2 := by rw [one_mul]; exact hζ
  have key := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun θ => Ψ (γ θ))
    (f' := fun θ => fderiv ℝ Ψ (γ θ) Δ)
    (C := B * (2 * ‖ζ₁ - ζ₀‖ / (1 + ‖ζ₀‖) + ‖w₁ - w₀‖))
    (fun θ hθ => by
      have hdθ : DifferentiableAt ℝ Ψ (γ θ) := hd (γ θ).1 (γ θ).2 (hmem θ hθ).1
      exact (hdθ.hasFDerivAt.comp_hasDerivAt θ (hγd θ)).hasDerivWithinAt)
    (fun θ hθ => by
      have hθ' : θ ∈ Set.Icc (0 : ℝ) 1 := ⟨hθ.1, hθ.2.le⟩
      exact hb (γ θ).1 (γ θ).2 Δ (hmem θ hθ').1 (hmem θ hθ').2)
  have e1 : γ 1 = (ζ₁, w₁) := by simp [hγ, hΔ]
  have e0 : γ 0 = (ζ₀, w₀) := by simp [hγ]
  simpa [e1, e0] using key

lemma differentiableAt_of_mem {F : ℂ × ℂ → E} {ρ ρ' : ℝ} (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) {ζ w : ℂ}
    (hw : w ∈ closedBall (0 : ℂ) ρ') :
    ContDiffAt ℝ ∞ F (ζ, w) := by
  have hopen : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) := isOpen_univ.prod isOpen_ball
  have hin : (ζ, w) ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) :=
    ⟨Set.mem_univ _, lt_of_le_of_lt (mem_closedBall.1 hw) hρ⟩
  exact hF.contDiffAt (hopen.mem_nhds hin)

lemma weight_le {ζ ζ₀ : ℂ} (h : ‖ζ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2) (a : ℝ) (ha : 0 ≤ a) :
    a / (1 + ‖ζ‖) ≤ 2 * a / (1 + ‖ζ₀‖) := by
  have h1 : ‖ζ₀‖ ≤ ‖ζ‖ + ‖ζ - ζ₀‖ := by
    have := norm_sub_norm_le ζ₀ ζ
    rw [norm_sub_rev] at this
    linarith
  have h2 : (1 + ‖ζ₀‖) / 2 ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ, norm_nonneg ζ₀]
  have hp : 0 < 1 + ‖ζ₀‖ := by linarith [norm_nonneg ζ₀]
  have hq : 0 < 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  rw [div_le_div_iff₀ hq hp]
  nlinarith

lemma CylBound.seg {F : ℂ × ℂ → E} {ρ ρ' C : ℝ} (hρ' : 0 ≤ ρ') (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (hC : CylBound F ρ' C)
    {ζ₀ ζ₁ w₀ w₁ : ℂ} (hw₀ : w₀ ∈ closedBall (0 : ℂ) ρ') (hw₁ : w₁ ∈ closedBall (0 : ℂ) ρ')
    (hζ : ‖ζ₁ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2) :
    ‖F (ζ₁, w₁) - F (ζ₀, w₀)‖ ≤ C * (2 * ‖ζ₁ - ζ₀‖ / (1 + ‖ζ₀‖) + ‖w₁ - w₀‖) := by
  have hC0 := hC.nonneg hρ'
  refine seg_core hw₀ hw₁ hζ
    (fun ζ w hw => (differentiableAt_of_mem hρ hF hw).differentiableAt (by simp)) ?_
  intro ζ w h hw hζ'
  refine le_trans ((hC ζ w hw).1 h) (mul_le_mul_of_nonneg_left ?_ hC0)
  have := weight_le hζ' ‖h.1‖ (norm_nonneg _)
  linarith

lemma CylBound.seg_fderiv {F : ℂ × ℂ → E} {ρ ρ' C : ℝ} (hρ' : 0 ≤ ρ') (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (hC : CylBound F ρ' C)
    {ζ₀ ζ₁ w₀ w₁ : ℂ} (hw₀ : w₀ ∈ closedBall (0 : ℂ) ρ') (hw₁ : w₁ ∈ closedBall (0 : ℂ) ρ')
    (hζ : ‖ζ₁ - ζ₀‖ ≤ (1 + ‖ζ₀‖) / 2) (k : ℂ × ℂ) :
    ‖fderiv ℝ F (ζ₁, w₁) k - fderiv ℝ F (ζ₀, w₀) k‖ ≤
      C * (2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖) * (2 * ‖ζ₁ - ζ₀‖ / (1 + ‖ζ₀‖) + ‖w₁ - w₀‖) := by
  have hC0 := hC.nonneg hρ'
  have hp : 0 < 1 + ‖ζ₀‖ := by linarith [norm_nonneg ζ₀]
  have hdd : ∀ ζ w, w ∈ closedBall (0 : ℂ) ρ' → DifferentiableAt ℝ (fderiv ℝ F) (ζ, w) := by
    intro ζ w hw
    have h1 : ContDiffAt ℝ ∞ (fderiv ℝ F) (ζ, w) :=
      (differentiableAt_of_mem hρ hF hw).fderiv_right (m := ∞) (by simp)
    exact h1.differentiableAt (by simp)
  refine seg_core (Ψ := fun p => fderiv ℝ F p k) hw₀ hw₁ hζ
    (fun ζ w hw => (hdd ζ w hw).clm_apply (differentiableAt_const k)) ?_
  intro ζ w h hw hζ'
  have e : fderiv ℝ (fun p => fderiv ℝ F p k) (ζ, w) h = fderiv ℝ (fderiv ℝ F) (ζ, w) h k := by
    rw [fderiv_clm_apply (hdd ζ w hw) (differentiableAt_const k)]
    simp
  rw [e]
  refine le_trans ((hC ζ w hw).2 h k) ?_
  have a1 := weight_le hζ' ‖h.1‖ (norm_nonneg _)
  have a2 := weight_le hζ' ‖k.1‖ (norm_nonneg _)
  have n1 : 0 ≤ ‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖ := by positivity
  have n2 : 0 ≤ 2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖ := by positivity
  calc C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖)
      ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC0 n1); linarith
    _ ≤ C * (2 * ‖h.1‖ / (1 + ‖ζ₀‖) + ‖h.2‖) * (2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖) := by
        apply mul_le_mul_of_nonneg_right _ n2
        apply mul_le_mul_of_nonneg_left _ hC0; linarith
    _ = C * (2 * ‖k.1‖ / (1 + ‖ζ₀‖) + ‖k.2‖) * (2 * ‖h.1‖ / (1 + ‖ζ₀‖) + ‖h.2‖) := by ring

/-- Closeness of `F ∘ (ψ, v)` to `F(·, 0)` in cylindrical `C¹` scale, pointwise at `z`. -/
lemma CylBound.close {F : ℂ × ℂ → E} {ρ ρ' C : ℝ} (hρ' : 0 ≤ ρ') (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (hC : CylBound F ρ' C)
    {ψ v : ℂ → ℂ} {z : ℂ} (hψ : DifferentiableAt ℝ ψ z) (hv : DifferentiableAt ℝ v z)
    {ε : ℝ} (hε1 : ε ≤ 1 / 2) (hερ : ε ≤ ρ')
    (h1 : ‖ψ z - z‖ ≤ ε * (1 + ‖z‖)) (h2 : ‖v z‖ ≤ ε)
    (h3 : ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε)
    (h4 : (1 + ‖z‖) * ‖fderiv ℝ v z‖ ≤ ε) :
    ‖F (ψ z, v z) - F (z, 0)‖ ≤ 3 * C * ε ∧
      (1 + ‖z‖) * ‖fderiv ℝ (fun x => F (ψ x, v x)) z - fderiv ℝ (fun x => F (x, 0)) z‖ ≤
        9 * C * ε := by
  have hC0 := hC.nonneg hρ'
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) h2
  have hp : 0 < 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hw0 : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ' := by simpa using hρ'
  have hw1 : v z ∈ closedBall (0 : ℂ) ρ' := by
    rw [mem_closedBall, dist_zero_right]; linarith
  have hζ : ‖ψ z - z‖ ≤ (1 + ‖z‖) / 2 := by nlinarith
  have hq : 2 * ‖ψ z - z‖ / (1 + ‖z‖) ≤ 2 * ε := by
    rw [div_le_iff₀ hp]; nlinarith
  have hseg : 2 * ‖ψ z - z‖ / (1 + ‖z‖) + ‖v z - 0‖ ≤ 3 * ε := by
    rw [sub_zero]; linarith
  constructor
  · refine le_trans (hC.seg hρ' hρ hF hw0 hw1 hζ) ?_
    calc C * (2 * ‖ψ z - z‖ / (1 + ‖z‖) + ‖v z - 0‖) ≤ C * (3 * ε) :=
          mul_le_mul_of_nonneg_left hseg hC0
      _ = 3 * C * ε := by ring
  · have hFd : DifferentiableAt ℝ F (ψ z, v z) :=
      (differentiableAt_of_mem hρ hF hw1).differentiableAt (by simp)
    have hFd0 : DifferentiableAt ℝ F (z, 0) :=
      (differentiableAt_of_mem hρ hF hw0).differentiableAt (by simp)
    have hA : HasFDerivAt (fun x => F (ψ x, v x))
        ((fderiv ℝ F (ψ z, v z)).comp ((fderiv ℝ ψ z).prod (fderiv ℝ v z))) z :=
      hFd.hasFDerivAt.comp z (hψ.hasFDerivAt.prodMk hv.hasFDerivAt)
    have hB : HasFDerivAt (fun x : ℂ => F (x, 0))
        ((fderiv ℝ F (z, 0)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ))) z :=
      hFd0.hasFDerivAt.comp z ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (0 : ℂ) z))
    rw [hA.fderiv, hB.fderiv]
    have hop : ‖(fderiv ℝ F (ψ z, v z)).comp ((fderiv ℝ ψ z).prod (fderiv ℝ v z)) -
        (fderiv ℝ F (z, 0)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ))‖ ≤
        9 * C * ε / (1 + ‖z‖) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
      intro h
      have hsplit : ((fderiv ℝ F (ψ z, v z)).comp ((fderiv ℝ ψ z).prod (fderiv ℝ v z)) -
          (fderiv ℝ F (z, 0)).comp ((ContinuousLinearMap.id ℝ ℂ).prod (0 : ℂ →L[ℝ] ℂ))) h =
          fderiv ℝ F (ψ z, v z) (fderiv ℝ ψ z h - h, fderiv ℝ v z h) +
            (fderiv ℝ F (ψ z, v z) (h, 0) - fderiv ℝ F (z, 0) (h, 0)) := by
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.zero_apply]
        have : (fderiv ℝ ψ z h, fderiv ℝ v z h) =
            (fderiv ℝ ψ z h - h, fderiv ℝ v z h) + (h, (0 : ℂ)) := by simp
        rw [this, map_add]
        abel
      rw [hsplit]
      have t1 : ‖fderiv ℝ F (ψ z, v z) (fderiv ℝ ψ z h - h, fderiv ℝ v z h)‖ ≤
          C * (3 * ε * ‖h‖ / (1 + ‖z‖)) := by
        refine le_trans ((hC (ψ z) (v z) hw1).1 _) (mul_le_mul_of_nonneg_left ?_ hC0)
        have a1 : ‖fderiv ℝ ψ z h - h‖ ≤ ε * ‖h‖ := by
          have := (fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ).le_opNorm h
          simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply] at this
          exact le_trans this (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
        have a2 : ‖fderiv ℝ v z h‖ ≤ ε * ‖h‖ / (1 + ‖z‖) := by
          rw [le_div_iff₀ hp]
          have := (fderiv ℝ v z).le_opNorm h
          calc ‖fderiv ℝ v z h‖ * (1 + ‖z‖) ≤ ‖fderiv ℝ v z‖ * ‖h‖ * (1 + ‖z‖) :=
                mul_le_mul_of_nonneg_right this hp.le
            _ = (1 + ‖z‖) * ‖fderiv ℝ v z‖ * ‖h‖ := by ring
            _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
        have a3 := weight_le (ζ := ψ z) (ζ₀ := z) hζ ‖fderiv ℝ ψ z h - h‖ (norm_nonneg _)
        have a4 : 2 * ‖fderiv ℝ ψ z h - h‖ / (1 + ‖z‖) ≤ 2 * (ε * ‖h‖) / (1 + ‖z‖) := by
          apply div_le_div_of_nonneg_right _ hp.le; linarith
        have e : 3 * ε * ‖h‖ / (1 + ‖z‖) = 2 * (ε * ‖h‖) / (1 + ‖z‖) + ε * ‖h‖ / (1 + ‖z‖) := by
          ring
        simp only
        rw [e]
        linarith
      have t2 := hC.seg_fderiv hρ' hρ hF hw0 hw1 hζ (h, (0 : ℂ))
      simp only [norm_zero, add_zero] at t2
      have t2' : ‖fderiv ℝ F (ψ z, v z) (h, 0) - fderiv ℝ F (z, 0) (h, 0)‖ ≤
          C * (2 * ‖h‖ / (1 + ‖z‖)) * (3 * ε) :=
        le_trans t2 (mul_le_mul_of_nonneg_left hseg (by positivity))
      calc ‖fderiv ℝ F (ψ z, v z) (fderiv ℝ ψ z h - h, fderiv ℝ v z h) +
            (fderiv ℝ F (ψ z, v z) (h, 0) - fderiv ℝ F (z, 0) (h, 0))‖
          ≤ C * (3 * ε * ‖h‖ / (1 + ‖z‖)) + C * (2 * ‖h‖ / (1 + ‖z‖)) * (3 * ε) :=
            le_trans (norm_add_le _ _) (add_le_add t1 t2')
        _ = 9 * C * ε / (1 + ‖z‖) * ‖h‖ := by ring
    calc (1 + ‖z‖) * ‖_‖ ≤ (1 + ‖z‖) * (9 * C * ε / (1 + ‖z‖)) :=
          mul_le_mul_of_nonneg_left hop hp.le
      _ = 9 * C * ε := by field_simp

end XT

end FiniteEnergyPlane

/-!
# X transfer, child A, part 1: from bounds in the cylinder chart to plane bounds

`Pc (s, t, w) = (cylInf s t, w)`. If `F ∘ Pc` has bounded first and second derivatives on
`s ≥ s₁`, `w ∈ closedBall 0 ρ'`, then `F` has cylindrical bounds on `‖ζ‖ ≥ e^{2π s₁}`.
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real
open ContinuousLinearMap (fst snd)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linear form `(s, t, w) ↦ 2π (s + i t)`. -/
noncomputable def lc : ℝ × ℝ × ℂ →L[ℝ] ℂ :=
  ((2 * π : ℝ) : ℂ) • (Complex.ofRealCLM.comp (fst ℝ ℝ (ℝ × ℂ)) +
    Complex.I • Complex.ofRealCLM.comp ((fst ℝ ℝ ℂ).comp (snd ℝ ℝ (ℝ × ℂ))))

lemma lc_apply (h : ℝ × ℝ × ℂ) :
    lc h = ((2 * π : ℝ) : ℂ) * ((h.1 : ℂ) + Complex.I * (h.2.1 : ℂ)) := by
  simp [lc]
  ring

lemma cylInf_eq (q : ℝ × ℝ × ℂ) : cylInf q.1 q.2.1 = Complex.exp (lc q) := by
  rw [lc_apply]
  unfold cylInf ccwLoop
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The cylinder chart. -/
noncomputable def Pc (q : ℝ × ℝ × ℂ) : ℂ × ℂ := (cylInf q.1 q.2.1, q.2.2)

/-- The derivative of the cylinder chart. -/
noncomputable def Lc (q : ℝ × ℝ × ℂ) : ℝ × ℝ × ℂ →L[ℝ] ℂ × ℂ :=
  ((cylInf q.1 q.2.1) • lc).prod ((snd ℝ ℝ ℂ).comp (snd ℝ ℝ (ℝ × ℂ)))

lemma Lc_apply (q h : ℝ × ℝ × ℂ) : Lc q h = (cylInf q.1 q.2.1 * lc h, h.2.2) := by
  simp [Lc]

lemma hasFDerivAt_cyl (q : ℝ × ℝ × ℂ) :
    HasFDerivAt (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) ((cylInf q.1 q.2.1) • lc) q := by
  have h := (lc.hasFDerivAt (x := q)).cexp
  have e : (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) = fun q => Complex.exp (lc q) :=
    funext cylInf_eq
  rw [e, cylInf_eq]
  exact h

lemma hasFDerivAt_Pc (q : ℝ × ℝ × ℂ) : HasFDerivAt Pc (Lc q) q :=
  (hasFDerivAt_cyl q).prodMk ((snd ℝ ℝ ℂ).comp (snd ℝ ℝ (ℝ × ℂ))).hasFDerivAt

lemma contDiff_Pc : ContDiff ℝ ∞ Pc := by
  have e : (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) = fun q => Complex.exp (lc q) :=
    funext cylInf_eq
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => cylInf q.1 q.2.1) := by
    rw [e]; exact Complex.contDiff_exp.comp lc.contDiff
  exact h1.prodMk ((snd ℝ ℝ ℂ).comp (snd ℝ ℝ (ℝ × ℂ))).contDiff

lemma isOpen_tube (ρ : ℝ) : IsOpen {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} :=
  isOpen_ball.preimage (continuous_snd.comp continuous_snd)

lemma isOpen_plane (ρ : ℝ) : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) :=
  isOpen_univ.prod isOpen_ball

section chart

variable {F : ℂ × ℂ → E} {ρ : ℝ}

lemma contDiffAt_plane (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) {p : ℂ × ℂ}
    (hp : p.2 ∈ ball (0 : ℂ) ρ) : ContDiffAt ℝ ∞ F p :=
  hF.contDiffAt ((isOpen_plane ρ).mem_nhds ⟨Set.mem_univ _, hp⟩)

lemma hasFDerivAt_comp_Pc (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ))
    {q : ℝ × ℝ × ℂ} (hq : q.2.2 ∈ ball (0 : ℂ) ρ) :
    HasFDerivAt (fun q => F (Pc q)) ((fderiv ℝ F (Pc q)).comp (Lc q)) q :=
  ((contDiffAt_plane hF (p := Pc q) hq).differentiableAt (by simp)).hasFDerivAt.comp q
    (hasFDerivAt_Pc q)

lemma contDiffOn_comp_Pc (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiffOn ℝ ∞ (fun q => F (Pc q)) {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} :=
  hF.comp contDiff_Pc.contDiffOn (fun q hq => ⟨Set.mem_univ _, hq⟩)

lemma fderiv2_comp_Pc (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ))
    {q : ℝ × ℝ × ℂ} (hq : q.2.2 ∈ ball (0 : ℂ) ρ) (h k : ℝ × ℝ × ℂ) :
    fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q h k =
      fderiv ℝ (fderiv ℝ F) (Pc q) (Lc q h) (Lc q k) +
        fderiv ℝ F (Pc q) (lc k * (cylInf q.1 q.2.1 * lc h), 0) := by
  have hnh : {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} ∈ 𝓝 q := (isOpen_tube ρ).mem_nhds hq
  have hdd : DifferentiableAt ℝ (fderiv ℝ (fun q => F (Pc q))) q :=
    (((contDiffOn_comp_Pc hF).contDiffAt hnh).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)
  have e1 : fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q h k =
      fderiv ℝ (fun q' => fderiv ℝ (fun q => F (Pc q)) q' k) q h := by
    rw [fderiv_clm_apply hdd (differentiableAt_const k)]
    simp
  have hev : (fun q' => fderiv ℝ (fun q => F (Pc q)) q' k) =ᶠ[𝓝 q]
      fun q' => fderiv ℝ F (Pc q') (Lc q' k) := by
    filter_upwards [hnh] with q' hq'
    rw [(hasFDerivAt_comp_Pc hF hq').fderiv]
    rfl
  have hFd : DifferentiableAt ℝ (fderiv ℝ F) (Pc q) :=
    ((contDiffAt_plane hF (p := Pc q) hq).fderiv_right (m := ∞) (by simp)).differentiableAt
      (by simp)
  have hc : HasFDerivAt (fun q' => fderiv ℝ F (Pc q'))
      ((fderiv ℝ (fderiv ℝ F) (Pc q)).comp (Lc q)) q :=
    hFd.hasFDerivAt.comp q (hasFDerivAt_Pc q)
  have hu : HasFDerivAt (fun q' => Lc q' k)
      (((lc k) • ((cylInf q.1 q.2.1) • lc)).prod (0 : ℝ × ℝ × ℂ →L[ℝ] ℂ)) q := by
    have : (fun q' => Lc q' k) = fun q' : ℝ × ℝ × ℂ => (cylInf q'.1 q'.2.1 * lc k, k.2.2) :=
      funext fun q' => Lc_apply q' k
    rw [this]
    exact ((hasFDerivAt_cyl q).mul_const (lc k)).prodMk (hasFDerivAt_const _ _)
  have key := (hc.clm_apply hu).congr_of_eventuallyEq hev
  rw [e1, key.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_eq_mul]
  rw [add_comm]

end chart

lemma exists_cylInf_eq (z : ℂ) (hz : z ≠ 0) :
    ∃ t : ℝ, cylInf (Real.log ‖z‖ / (2 * π)) t = z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hexp : Real.exp (2 * π * (Real.log ‖z‖ / (2 * π))) = ‖z‖ := by
    rw [mul_div_cancel₀ _ h2pi.ne', Real.exp_log hzpos]
  refine ⟨Complex.arg z / (2 * π), ?_⟩
  unfold cylInf ccwLoop
  rw [hexp]
  have e : ((2 * π * (Complex.arg z / (2 * π)) : ℝ) : ℂ) = (Complex.arg z : ℂ) := by
    congr 1
    field_simp
  rw [e]
  exact Complex.norm_mul_exp_arg_mul_I z

/-- A preimage of `(Δ, o)` under the chart derivative at a point over `ζ`. -/
noncomputable def hsol (ζ Δ o : ℂ) : ℝ × ℝ × ℂ :=
  ((Δ / (((2 * π : ℝ) : ℂ) * ζ)).re, (Δ / (((2 * π : ℝ) : ℂ) * ζ)).im, o)

lemma two_pi_ne : (((2 * π : ℝ) : ℂ)) ≠ 0 := by
  have : (0 : ℝ) < 2 * π := by positivity
  exact_mod_cast this.ne'

lemma lc_hsol {ζ : ℂ} (hζ : ζ ≠ 0) (Δ o : ℂ) : lc (hsol ζ Δ o) = Δ / ζ := by
  rw [lc_apply]
  simp only [hsol]
  rw [mul_comm Complex.I, Complex.re_add_im]
  have := two_pi_ne
  field_simp

lemma norm_hsol_le {ζ : ℂ} (hζ : ζ ≠ 0) (Δ o : ℂ) : ‖hsol ζ Δ o‖ ≤ ‖Δ‖ / ‖ζ‖ + ‖o‖ := by
  have hζn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  have h2 : (1 : ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have hx : ‖Δ / (((2 * π : ℝ) : ℂ) * ζ)‖ ≤ ‖Δ‖ / ‖ζ‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply div_le_div_of_nonneg_left (norm_nonneg _) hζn
    nlinarith
  have hre := Complex.abs_re_le_norm (Δ / (((2 * π : ℝ) : ℂ) * ζ))
  have him := Complex.abs_im_le_norm (Δ / (((2 * π : ℝ) : ℂ) * ζ))
  have hd : 0 ≤ ‖Δ‖ / ‖ζ‖ := by positivity
  simp only [hsol, Prod.norm_def, Real.norm_eq_abs]
  refine max_le (by linarith [norm_nonneg o]) (max_le (by linarith [norm_nonneg o]) (by linarith))

/-- From the cylinder chart to the plane. -/
theorem chart_bound {F : ℂ × ℂ → E} {ρ ρ' : ℝ} (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) {s₁ C₁ C₂ : ℝ}
    (h1 : ∀ q : ℝ × ℝ × ℂ, s₁ ≤ q.1 → q.2.2 ∈ closedBall (0 : ℂ) ρ' →
      ‖fderiv ℝ (fun q => F (Pc q)) q‖ ≤ C₁)
    (h2 : ∀ q : ℝ × ℝ × ℂ, s₁ ≤ q.1 → q.2.2 ∈ closedBall (0 : ℂ) ρ' →
      ‖fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q‖ ≤ C₂) :
    ∀ ζ w : ℂ, Real.exp (2 * π * s₁) ≤ ‖ζ‖ → w ∈ closedBall (0 : ℂ) ρ' →
      (∀ h : ℂ × ℂ, ‖fderiv ℝ F (ζ, w) h‖ ≤ C₁ * (‖h.1‖ / ‖ζ‖ + ‖h.2‖)) ∧
      ∀ h k : ℂ × ℂ, ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        (C₁ + C₂) * (‖h.1‖ / ‖ζ‖ + ‖h.2‖) * (‖k.1‖ / ‖ζ‖ + ‖k.2‖) := by
  intro ζ w hζR hw
  have hζn : 0 < ‖ζ‖ := lt_of_lt_of_le (Real.exp_pos _) hζR
  have hζ0 : ζ ≠ 0 := norm_pos_iff.1 hζn
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨t, ht⟩ := exists_cylInf_eq ζ hζ0
  set q : ℝ × ℝ × ℂ := (Real.log ‖ζ‖ / (2 * π), t, w) with hq
  have hs : s₁ ≤ q.1 := by
    show s₁ ≤ Real.log ‖ζ‖ / (2 * π)
    rw [le_div_iff₀ h2pi, mul_comm]
    exact (Real.le_log_iff_exp_le hζn).2 hζR
  have hcyl : cylInf q.1 q.2.1 = ζ := ht
  have hPq : Pc q = (ζ, w) := by
    show (cylInf (Real.log ‖ζ‖ / (2 * π)) t, w) = (ζ, w)
    rw [ht]
  have hqb : q.2.2 ∈ ball (0 : ℂ) ρ :=
    mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ)
  have hC1 : 0 ≤ C₁ := (norm_nonneg _).trans (h1 q hs hw)
  have hC2 : 0 ≤ C₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q)) (h2 q hs hw)
  have L1 : ∀ Δ o : ℂ, Lc q (hsol ζ Δ o) = (Δ, o) := by
    intro Δ o
    rw [Lc_apply, lc_hsol hζ0, hcyl]
    simp only [hsol]
    rw [mul_div_cancel₀ _ hζ0]
  have D1 : ∀ Δ o : ℂ, ‖fderiv ℝ F (ζ, w) (Δ, o)‖ ≤ C₁ * (‖Δ‖ / ‖ζ‖ + ‖o‖) := by
    intro Δ o
    have e : fderiv ℝ F (ζ, w) (Δ, o) = fderiv ℝ (fun q => F (Pc q)) q (hsol ζ Δ o) := by
      rw [(hasFDerivAt_comp_Pc hF hqb).fderiv, ContinuousLinearMap.comp_apply, L1, hPq]
    rw [e]
    exact ((fderiv ℝ (fun q => F (Pc q)) q).le_opNorm _).trans
      (mul_le_mul (h1 q hs hw) (norm_hsol_le hζ0 Δ o) (norm_nonneg _) hC1)
  refine ⟨fun h => D1 h.1 h.2, ?_⟩
  rintro ⟨Δ₁, o₁⟩ ⟨Δ₂, o₂⟩
  have I2 := fderiv2_comp_Pc hF hqb (hsol ζ Δ₁ o₁) (hsol ζ Δ₂ o₂)
  rw [L1, L1, hPq, lc_hsol hζ0, lc_hsol hζ0, hcyl] at I2
  have e : fderiv ℝ (fderiv ℝ F) (ζ, w) (Δ₁, o₁) (Δ₂, o₂) =
      fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q (hsol ζ Δ₁ o₁) (hsol ζ Δ₂ o₂) -
        fderiv ℝ F (ζ, w) (Δ₂ / ζ * (ζ * (Δ₁ / ζ)), 0) := eq_sub_of_add_eq I2.symm
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have n1 := norm_hsol_le hζ0 Δ₁ o₁
  have n2 := norm_hsol_le hζ0 Δ₂ o₂
  have a1 : 0 ≤ ‖Δ₁‖ / ‖ζ‖ := by positivity
  have a2 : 0 ≤ ‖Δ₂‖ / ‖ζ‖ := by positivity
  have b1 : ‖fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q (hsol ζ Δ₁ o₁) (hsol ζ Δ₂ o₂)‖ ≤
      C₂ * (‖Δ₁‖ / ‖ζ‖ + ‖o₁‖) * (‖Δ₂‖ / ‖ζ‖ + ‖o₂‖) := by
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    exact mul_le_mul (mul_le_mul (h2 q hs hw) n1 (norm_nonneg _) hC2) n2 (norm_nonneg _)
      (by positivity)
  have b2 : ‖fderiv ℝ F (ζ, w) (Δ₂ / ζ * (ζ * (Δ₁ / ζ)), 0)‖ ≤
      C₁ * ((‖Δ₁‖ / ‖ζ‖) * (‖Δ₂‖ / ‖ζ‖)) := by
    refine (D1 _ 0).trans (le_of_eq ?_)
    rw [norm_zero, add_zero, norm_mul, norm_mul, norm_div, norm_div]
    field_simp
  have b3 : (‖Δ₁‖ / ‖ζ‖) * (‖Δ₂‖ / ‖ζ‖) ≤ (‖Δ₁‖ / ‖ζ‖ + ‖o₁‖) * (‖Δ₂‖ / ‖ζ‖ + ‖o₂‖) :=
    mul_le_mul (by linarith [norm_nonneg o₁]) (by linarith [norm_nonneg o₂]) a2 (by positivity)
  calc _ ≤ C₂ * (‖Δ₁‖ / ‖ζ‖ + ‖o₁‖) * (‖Δ₂‖ / ‖ζ‖ + ‖o₂‖) +
        C₁ * ((‖Δ₁‖ / ‖ζ‖ + ‖o₁‖) * (‖Δ₂‖ / ‖ζ‖ + ‖o₂‖)) :=
        add_le_add b1 (b2.trans (mul_le_mul_of_nonneg_left b3 hC1))
    _ = _ := by ring

end XT

end FiniteEnergyPlane

/-!
# X transfer, child A, part 2: bounds in the cylinder chart from a periodic model with
exponentially decaying remainder.
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real
open ContinuousLinearMap (fst snd)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv2_apply {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y} {x : X} (hf : ContDiffAt ℝ ∞ f x)
    (h k : X) : fderiv ℝ (fderiv ℝ f) x h k = fderiv ℝ (fun y => fderiv ℝ f y k) x h := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hdd (differentiableAt_const k)]
  simp

lemma periodic_fract {Y : Type*} {g : ℝ × ℂ → Y}
    (hg : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w)) (t : ℝ) (w : ℂ) :
    g (t, w) = g (Int.fract t, w) := by
  have hp : Function.Periodic (fun t => g (t, w)) 1 := fun t => hg t w
  have := hp.sub_int_mul_eq (x := t) ⌊t⌋
  simp only [mul_one] at this
  rw [Int.self_sub_floor] at this
  exact this.symm

lemma fderiv_periodic {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {g : ℝ × ℂ → Y}
    (hg : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w)) (t : ℝ) (w : ℂ) :
    fderiv ℝ g (t + 1, w) = fderiv ℝ g (t, w) := by
  have e : (fun x : ℝ × ℂ => g (x + ((1 : ℝ), (0 : ℂ)))) = g := by
    funext x
    rcases x with ⟨t, w⟩
    simp [hg]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := (t, w)) ((1 : ℝ), (0 : ℂ))
  rw [e] at this
  simpa using this.symm

lemma isOpen_model (ρ : ℝ) : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℝ × ℂ)) :=
  isOpen_univ.prod isOpen_ball

lemma model_bounds {M : ℝ × ℂ → E} {ρ ρ' : ℝ} (hρ : ρ' < ρ)
    (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w)) :
    ∃ N₁ N₂ : ℝ, ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ' →
      ‖fderiv ℝ M (t, w)‖ ≤ N₁ ∧ ‖fderiv ℝ (fderiv ℝ M) (t, w)‖ ≤ N₂ := by
  have hd1 : ContDiffOn ℝ ∞ (fderiv ℝ M) (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    hM.fderiv_of_isOpen (isOpen_model ρ) (by simp)
  have hd2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ M)) (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    hd1.fderiv_of_isOpen (isOpen_model ρ) (by simp)
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) ρ') :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hsub : Set.Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) ρ' ⊆ Set.univ ×ˢ ball (0 : ℂ) ρ :=
    fun x hx => ⟨Set.mem_univ _,
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hx.2) hρ)⟩
  obtain ⟨N₁, hN₁⟩ := hK.exists_bound_of_continuousOn (hd1.continuousOn.mono hsub)
  have hc2 : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ M) x‖)
      (Set.Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) ρ') :=
    ContinuousOn.norm (E := ℝ × ℂ →L[ℝ] ℝ × ℂ →L[ℝ] E) (hd2.continuousOn.mono hsub)
  obtain ⟨N₂, hN₂⟩ := hK.exists_bound_of_continuousOn hc2
  refine ⟨N₁, N₂, fun t w hw => ?_⟩
  have p1 := periodic_fract (g := fderiv ℝ M) (fderiv_periodic hper) t w
  have p2 := periodic_fract (g := fderiv ℝ (fderiv ℝ M))
    (fderiv_periodic (fderiv_periodic hper)) t w
  have hmem : (Int.fract t, w) ∈ Set.Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) ρ' :=
    ⟨⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, hw⟩
  rw [p1, p2]
  have h2 := hN₂ _ hmem
  rw [Real.norm_eq_abs] at h2
  exact ⟨hN₁ _ hmem, (le_abs_self _).trans h2⟩

/-- The cylinder model `(s, t, w) ↦ s • ℓ + M (t, w)`. -/
def Mdl (ℓ : E) (M : ℝ × ℂ → E) (q : ℝ × ℝ × ℂ) : E := q.1 • ℓ + M q.2

section model

variable {ℓ : E} {M : ℝ × ℂ → E} {ρ : ℝ}

lemma contDiffAt_M (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ)) {x : ℝ × ℂ}
    (hx : x.2 ∈ ball (0 : ℂ) ρ) : ContDiffAt ℝ ∞ M x :=
  hM.contDiffAt ((isOpen_model ρ).mem_nhds ⟨Set.mem_univ _, hx⟩)

lemma hasFDerivAt_Mdl (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    {q : ℝ × ℝ × ℂ} (hq : q.2.2 ∈ ball (0 : ℂ) ρ) :
    HasFDerivAt (Mdl ℓ M) ((fst ℝ ℝ (ℝ × ℂ)).smulRight ℓ +
      (fderiv ℝ M q.2).comp (snd ℝ ℝ (ℝ × ℂ))) q := by
  have hMd : DifferentiableAt ℝ M q.2 := (contDiffAt_M hM hq).differentiableAt (by simp)
  have h1 : HasFDerivAt (fun q : ℝ × ℝ × ℂ => q.1 • ℓ) ((fst ℝ ℝ (ℝ × ℂ)).smulRight ℓ) q :=
    hasFDerivAt_fst.smul_const ℓ
  have h2 : HasFDerivAt (fun q : ℝ × ℝ × ℂ => M q.2)
      ((fderiv ℝ M q.2).comp (snd ℝ ℝ (ℝ × ℂ))) q :=
    hMd.hasFDerivAt.comp q hasFDerivAt_snd
  exact h1.add h2

lemma contDiffOn_Mdl (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiffOn ℝ ∞ (Mdl ℓ M) {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} := by
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ => q.1 • ℓ) := contDiff_fst.smul contDiff_const
  have h2 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ × ℂ => M q.2)
      {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} :=
    hM.comp contDiff_snd.contDiffOn (fun q hq => ⟨Set.mem_univ _, hq⟩)
  exact h1.contDiffOn.add h2

lemma Mdl_bounds (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    {q : ℝ × ℝ × ℂ} (hq : q.2.2 ∈ ball (0 : ℂ) ρ) :
    ‖fderiv ℝ (Mdl ℓ M) q‖ ≤ ‖ℓ‖ + ‖fderiv ℝ M q.2‖ ∧
      ‖fderiv ℝ (fderiv ℝ (Mdl ℓ M)) q‖ ≤ ‖fderiv ℝ (fderiv ℝ M) q.2‖ := by
  have hnh : {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} ∈ 𝓝 q := (isOpen_tube ρ).mem_nhds hq
  constructor
  · rw [(hasFDerivAt_Mdl hM hq).fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun k => ?_)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, add_mul]
    have a1 : ‖k.1‖ ≤ ‖k‖ := norm_fst_le k
    have a2 : ‖k.2‖ ≤ ‖k‖ := norm_snd_le k
    have a3 := (fderiv ℝ M q.2).le_opNorm k.2
    have a4 : ‖fderiv ℝ M q.2‖ * ‖k.2‖ ≤ ‖fderiv ℝ M q.2‖ * ‖k‖ :=
      mul_le_mul_of_nonneg_left a2 (norm_nonneg _)
    have a5 : ‖k.1‖ * ‖ℓ‖ ≤ ‖ℓ‖ * ‖k‖ := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left a1 (norm_nonneg _)
    linarith
  · have hMc := contDiffAt_M hM (x := q.2) hq
    have hMdlc : ContDiffAt ℝ ∞ (Mdl ℓ M) q := (contDiffOn_Mdl hM).contDiffAt hnh
    refine ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (fderiv ℝ (fderiv ℝ M) q.2)) (fun h => ?_)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun k => ?_)
    rw [fderiv2_apply hMdlc h k]
    have hev : (fun q' => fderiv ℝ (Mdl ℓ M) q' k) =ᶠ[𝓝 q]
        fun q' : ℝ × ℝ × ℂ => k.1 • ℓ + fderiv ℝ M q'.2 k.2 := by
      filter_upwards [hnh] with q' hq'
      rw [(hasFDerivAt_Mdl hM hq').fderiv]
      rfl
    have hdd : DifferentiableAt ℝ (fderiv ℝ M) q.2 :=
      (hMc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hk : HasFDerivAt (fun x : ℝ × ℂ => fderiv ℝ M x k.2)
        (fderiv ℝ (fun x : ℝ × ℂ => fderiv ℝ M x k.2) q.2) q.2 :=
      (hdd.clm_apply (differentiableAt_const k.2)).hasFDerivAt
    have key := ((hk.comp q hasFDerivAt_snd).const_add (k.1 • ℓ)).congr_of_eventuallyEq hev
    rw [key.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
      ← fderiv2_apply hMc h.2 k.2]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    have n0 : 0 ≤ ‖fderiv ℝ (fderiv ℝ M) q.2‖ := norm_nonneg (fderiv ℝ (fderiv ℝ M) q.2)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (norm_snd_le h) n0)
      (norm_snd_le k) (norm_nonneg k.2) (mul_nonneg n0 (norm_nonneg h))

end model

/-- Bounds in the cylinder chart. -/
theorem cyl_bounds {F : ℂ × ℂ → E} {ρ ρ' b : ℝ} (hb : 0 < b) (hρ : ρ' < ρ)
    (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (ℓ : E)
    (M : ℝ × ℂ → E) (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w))
    (hdec : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) ρ b) :
    ∃ s₁ C₁ C₂ : ℝ,
      (∀ q : ℝ × ℝ × ℂ, s₁ ≤ q.1 → q.2.2 ∈ closedBall (0 : ℂ) ρ' →
        ‖fderiv ℝ (fun q => F (Pc q)) q‖ ≤ C₁) ∧
      (∀ q : ℝ × ℝ × ℂ, s₁ ≤ q.1 → q.2.2 ∈ closedBall (0 : ℂ) ρ' →
        ‖fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) q‖ ≤ C₂) := by
  obtain ⟨N₁, N₂, hN⟩ := model_bounds hρ hM hper
  obtain ⟨Ca, sa, ha⟩ := hdec.2 1
  obtain ⟨Cb, sb, hbb⟩ := hdec.2 2
  have hDe : (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) =
      fun q => F (Pc q) - Mdl ℓ M q := by
    funext q
    simp only [Pc, Mdl, Prod.mk.eta]
    abel
  rw [hDe] at ha hbb
  have hexp : ∀ (C s : ℝ), 0 ≤ s → C * Real.exp (-(b * s)) ≤ |C| := by
    intro C s hs
    have h1 : Real.exp (-(b * s)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hb.le hs))
    calc C * Real.exp (-(b * s)) ≤ |C| * Real.exp (-(b * s)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ = |C| := mul_one _
  -- pointwise facts at a point of the tube
  have hpt : ∀ q : ℝ × ℝ × ℂ, q.2.2 ∈ ball (0 : ℂ) ρ →
      fderiv ℝ (fun q => F (Pc q)) q =
        fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q) q + fderiv ℝ (Mdl ℓ M) q := by
    intro q hq
    have hA := hasFDerivAt_comp_Pc hF hq
    have hB := hasFDerivAt_Mdl (ℓ := ℓ) hM hq
    have hD : HasFDerivAt (fun q => F (Pc q) - Mdl ℓ M q) _ q := hA.sub hB
    rw [hD.fderiv, hA.fderiv, hB.fderiv]
    abel
  refine ⟨max (max sa sb) 0, |Ca| + (‖ℓ‖ + N₁), |Cb| + N₂, ?_, ?_⟩
  · rintro ⟨s, t, w⟩ hs hw
    have hs0 : (0 : ℝ) ≤ s := (le_max_right _ _).trans hs
    have hsa : sa ≤ s := ((le_max_left _ _).trans (le_max_left _ _)).trans hs
    have hwb : w ∈ ball (0 : ℂ) ρ :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ)
    rw [hpt (s, t, w) hwb]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [← norm_iteratedFDeriv_one]
      exact (ha s hsa t w hwb).trans (hexp Ca s hs0)
    · exact ((Mdl_bounds hM (q := (s, t, w)) hwb).1).trans
        (add_le_add le_rfl (hN t w hw).1)
  · rintro ⟨s, t, w⟩ hs hw
    have hs0 : (0 : ℝ) ≤ s := (le_max_right _ _).trans hs
    have hsb : sb ≤ s := ((le_max_right _ _).trans (le_max_left _ _)).trans hs
    have hwb : w ∈ ball (0 : ℂ) ρ :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) hρ)
    have hnh : {q : ℝ × ℝ × ℂ | q.2.2 ∈ ball (0 : ℂ) ρ} ∈ 𝓝 ((s, t, w) : ℝ × ℝ × ℂ) :=
      (isOpen_tube ρ).mem_nhds hwb
    have hev : fderiv ℝ (fun q => F (Pc q)) =ᶠ[𝓝 ((s, t, w) : ℝ × ℝ × ℂ)]
        fun q => fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q) q + fderiv ℝ (Mdl ℓ M) q := by
      filter_upwards [hnh] with q hq using hpt q hq
    have hFc : ContDiffAt ℝ ∞ (fun q => F (Pc q)) ((s, t, w) : ℝ × ℝ × ℂ) :=
      (contDiffOn_comp_Pc hF).contDiffAt hnh
    have hMc : ContDiffAt ℝ ∞ (Mdl ℓ M) ((s, t, w) : ℝ × ℝ × ℂ) :=
      (contDiffOn_Mdl hM).contDiffAt hnh
    have hDc : ContDiffAt ℝ ∞ (fun q => F (Pc q) - Mdl ℓ M q) ((s, t, w) : ℝ × ℝ × ℂ) :=
      hFc.sub hMc
    have d1 : DifferentiableAt ℝ (fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q))
        ((s, t, w) : ℝ × ℝ × ℂ) :=
      (hDc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have d2 : DifferentiableAt ℝ (fderiv ℝ (Mdl ℓ M)) ((s, t, w) : ℝ × ℝ × ℂ) :=
      (hMc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hsum : HasFDerivAt (fun q => fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q) q +
        fderiv ℝ (Mdl ℓ M) q) _ ((s, t, w) : ℝ × ℝ × ℂ) := d1.hasFDerivAt.add d2.hasFDerivAt
    rw [hev.fderiv_eq, hsum.fderiv]
    refine le_trans (norm_add_le
      (fderiv ℝ (fderiv ℝ (fun q => F (Pc q) - Mdl ℓ M q)) ((s, t, w) : ℝ × ℝ × ℂ))
      (fderiv ℝ (fderiv ℝ (Mdl ℓ M)) ((s, t, w) : ℝ × ℝ × ℂ))) (add_le_add ?_ ?_)
    · rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact (hbb s hsb t w hwb).trans (hexp Cb s hs0)
    · exact ((Mdl_bounds hM (q := (s, t, w)) hwb).2).trans (hN t w hw).2

end XT

end FiniteEnergyPlane

/-!
# X transfer, child A: cylindrical `C²` bounds from an exponentially attained periodic model
-/

namespace FiniteEnergyPlane

namespace XT

open Metric Filter Topology
open scoped ContDiff Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma wt_far {R : ℝ} (hR : 0 < R) {ζ : ℂ} (hζ : R ≤ ‖ζ‖) (h : ℂ × ℂ) :
    ‖h.1‖ / ‖ζ‖ + ‖h.2‖ ≤ (1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := by
  have hn : 0 < ‖ζ‖ := lt_of_lt_of_le hR hζ
  have hR1 : 0 ≤ 1 / R := by positivity
  have k1 : ‖h.1‖ / ‖ζ‖ ≤ (1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖)) := by
    rw [div_le_iff₀ hn]
    have hX : 1 ≤ (1 + 1 / R) * ‖ζ‖ / (1 + ‖ζ‖) := by
      rw [le_div_iff₀ (by linarith)]
      have h1 : 1 ≤ ‖ζ‖ / R := (one_le_div hR).2 hζ
      have e : (1 + 1 / R) * ‖ζ‖ = ‖ζ‖ + ‖ζ‖ / R := by ring
      linarith
    calc ‖h.1‖ ≤ ‖h.1‖ * ((1 + 1 / R) * ‖ζ‖ / (1 + ‖ζ‖)) :=
          le_mul_of_one_le_right (norm_nonneg _) hX
      _ = _ := by ring
  have k2 : ‖h.2‖ ≤ (1 + 1 / R) * ‖h.2‖ := le_mul_of_one_le_left (norm_nonneg _) (by linarith)
  rw [mul_add]
  linarith

lemma wt_near {R : ℝ} {ζ : ℂ} (hζ : ‖ζ‖ ≤ R) (h : ℂ × ℂ) :
    ‖h‖ ≤ (1 + R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := by
  have hp : 0 < 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  have hR : 0 ≤ R := (norm_nonneg ζ).trans hζ
  have k1 : ‖h.1‖ ≤ (1 + R) * (‖h.1‖ / (1 + ‖ζ‖)) := by
    rw [← mul_div_assoc, le_div_iff₀ hp]
    nlinarith [mul_nonneg (norm_nonneg h.1) (sub_nonneg.2 hζ)]
  have k2 : ‖h.2‖ ≤ (1 + R) * ‖h.2‖ := le_mul_of_one_le_left (norm_nonneg _) (by linarith)
  have k3 : ‖h‖ ≤ ‖h.1‖ + ‖h.2‖ := by
    rw [Prod.norm_def]
    exact max_le (by linarith [norm_nonneg h.2]) (by linarith [norm_nonneg h.1])
  rw [mul_add]
  linarith

theorem exists_cylBound (ρ b ρ' : ℝ) (hb : 0 < b) (hρ' : 0 < ρ') (hρ : ρ' < ρ)
    (F : ℂ × ℂ → E) (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (ℓ : E)
    (M : ℝ × ℂ → E) (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hMper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w))
    (hdec : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) ρ b) :
    ∃ C : ℝ, CylBound F ρ' C := by
  obtain ⟨s₁, C₁, C₂, h1, h2⟩ := cyl_bounds (ρ' := ρ') hb hρ hF ℓ M hM hMper hdec
  have far := chart_bound hρ hF h1 h2
  have hR : 0 < Real.exp (2 * π * s₁) := Real.exp_pos _
  generalize Real.exp (2 * π * s₁) = R at far hR
  have hw0 : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ' := by simpa using hρ'.le
  have hC1 : 0 ≤ C₁ := (norm_nonneg _).trans (h1 (s₁, 0, 0) le_rfl hw0)
  have hC2 : 0 ≤ C₂ :=
    le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (fun q => F (Pc q))) (s₁, 0, 0)))
      (h2 (s₁, 0, 0) le_rfl hw0)
  have hd1 : ContDiffOn ℝ ∞ (fderiv ℝ F) (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    hF.fderiv_of_isOpen (isOpen_plane ρ) (by simp)
  have hd2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ F)) (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
    hd1.fderiv_of_isOpen (isOpen_plane ρ) (by simp)
  have hK : IsCompact (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) ρ') :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hsub : closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) ρ' ⊆ Set.univ ×ˢ ball (0 : ℂ) ρ :=
    fun x hx => ⟨Set.mem_univ _,
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hx.2) hρ)⟩
  obtain ⟨N₁, hN₁⟩ := hK.exists_bound_of_continuousOn (hd1.continuousOn.mono hsub)
  have hc2 : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ F) x‖)
      (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) ρ') :=
    ContinuousOn.norm (E := ℂ × ℂ →L[ℝ] ℂ × ℂ →L[ℝ] E) (hd2.continuousOn.mono hsub)
  obtain ⟨N₂, hN₂⟩ := hK.exists_bound_of_continuousOn hc2
  have hc1 : (1 : ℝ) ≤ 1 + 1 / R := by
    have : 0 ≤ 1 / R := by positivity
    linarith
  have hc0 : (0 : ℝ) ≤ 1 + 1 / R := by linarith
  have hfarC : C₁ * (1 + 1 / R) ≤ (C₁ + C₂) * (1 + 1 / R) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hC1 hc0) (sub_nonneg.2 hc1),
      mul_nonneg hC2 (sq_nonneg (1 + 1 / R))]
  have hnearC : |N₁| * (1 + R) ≤ (|N₁| + |N₂|) * (1 + R) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg N₁) (by linarith : (0 : ℝ) ≤ 1 + R)) hR.le,
      mul_nonneg (abs_nonneg N₂) (sq_nonneg (1 + R))]
  refine ⟨max ((C₁ + C₂) * (1 + 1 / R) ^ 2) ((|N₁| + |N₂|) * (1 + R) ^ 2), fun ζ w hw => ?_⟩
  have hCa : (C₁ + C₂) * (1 + 1 / R) ^ 2 ≤
      max ((C₁ + C₂) * (1 + 1 / R) ^ 2) ((|N₁| + |N₂|) * (1 + R) ^ 2) := le_max_left _ _
  have hCb : (|N₁| + |N₂|) * (1 + R) ^ 2 ≤
      max ((C₁ + C₂) * (1 + 1 / R) ^ 2) ((|N₁| + |N₂|) * (1 + R) ^ 2) := le_max_right _ _
  generalize max ((C₁ + C₂) * (1 + 1 / R) ^ 2) ((|N₁| + |N₂|) * (1 + R) ^ 2) = C at hCa hCb
  have hC0 : 0 ≤ C := le_trans (by positivity) hCa
  have hW : ∀ h : ℂ × ℂ, 0 ≤ ‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖ := fun h => by positivity
  rcases le_or_gt R ‖ζ‖ with hζ | hζ
  · obtain ⟨f1, f2⟩ := far ζ w hζ hw
    have hn : 0 < ‖ζ‖ := lt_of_lt_of_le hR hζ
    constructor
    · intro h
      calc ‖fderiv ℝ F (ζ, w) h‖ ≤ C₁ * (‖h.1‖ / ‖ζ‖ + ‖h.2‖) := f1 h
        _ ≤ C₁ * ((1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) :=
            mul_le_mul_of_nonneg_left (wt_far hR hζ h) hC1
        _ = C₁ * (1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := by ring
        _ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) :=
            mul_le_mul_of_nonneg_right (hfarC.trans hCa) (hW h)
    · intro h k
      have p1 : 0 ≤ ‖k.1‖ / ‖ζ‖ + ‖k.2‖ := by positivity
      calc ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖
          ≤ (C₁ + C₂) * (‖h.1‖ / ‖ζ‖ + ‖h.2‖) * (‖k.1‖ / ‖ζ‖ + ‖k.2‖) := f2 h k
        _ ≤ (C₁ + C₂) * ((1 + 1 / R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) *
              ((1 + 1 / R) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (wt_far hR hζ h) (by linarith))
              (wt_far hR hζ k) p1
              (mul_nonneg (by linarith) (mul_nonneg hc0 (hW h)))
        _ = (C₁ + C₂) * (1 + 1 / R) ^ 2 * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) *
              (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) := by ring
        _ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCa (hW h)) (hW k)
  · have hmem : (ζ, w) ∈ closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) ρ' :=
      ⟨mem_closedBall_zero_iff.2 hζ.le, hw⟩
    have n1 : ‖fderiv ℝ F (ζ, w)‖ ≤ |N₁| := (hN₁ _ hmem).trans (le_abs_self _)
    have n2 : ‖fderiv ℝ (fderiv ℝ F) (ζ, w)‖ ≤ |N₂| := by
      have h2' := hN₂ _ hmem
      rw [Real.norm_eq_abs] at h2'
      exact ((le_abs_self _).trans h2').trans (le_abs_self _)
    have hR1 : (0 : ℝ) ≤ 1 + R := by linarith
    constructor
    · intro h
      calc ‖fderiv ℝ F (ζ, w) h‖ ≤ ‖fderiv ℝ F (ζ, w)‖ * ‖h‖ := (fderiv ℝ F (ζ, w)).le_opNorm h
        _ ≤ |N₁| * ((1 + R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) :=
            mul_le_mul n1 (wt_near hζ.le h) (norm_nonneg _) (abs_nonneg _)
        _ = |N₁| * (1 + R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) := by ring
        _ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) :=
            mul_le_mul_of_nonneg_right (hnearC.trans hCb) (hW h)
    · intro h k
      have hN12 : |N₂| ≤ |N₁| + |N₂| := by linarith [abs_nonneg N₁]
      calc ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖
          ≤ ‖fderiv ℝ (fderiv ℝ F) (ζ, w)‖ * ‖h‖ * ‖k‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ |N₂| * ((1 + R) * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) *
              ((1 + R) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖)) :=
            mul_le_mul (mul_le_mul n2 (wt_near hζ.le h) (norm_nonneg _) (abs_nonneg _))
              (wt_near hζ.le k) (norm_nonneg _)
              (mul_nonneg (abs_nonneg _) (mul_nonneg hR1 (hW h)))
        _ = |N₂| * (1 + R) ^ 2 * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) *
              (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) := by ring
        _ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              ((mul_le_mul_of_nonneg_right hN12 (sq_nonneg _)).trans hCb) (hW h)) (hW k)

end XT

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_cylindrical_bounds_of_expDecayCInftyTube_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ρ b ρ' : ℝ) (hb : 0 < b) (hρ' : 0 < ρ') (hρ : ρ' < ρ)
    (F : ℂ × ℂ → E) (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (ℓ : E)
    (M : ℝ × ℂ → E) (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hMper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w))
    (hdec : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) ρ b) :
    ∃ C : ℝ, ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' →
      (∀ h : ℂ × ℂ, ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) ∧
      ∀ h k : ℂ × ℂ, ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) :=
  XT.exists_cylBound ρ b ρ' hb hρ' hρ F hF ℓ M hM hMper hdec

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ρ b ρ' : ℝ) (hb : 0 < b) (hρ' : 0 < ρ') (hρ : ρ' < ρ)
    (F : ℂ × ℂ → E) (hF : ContDiffOn ℝ ∞ F (Set.univ ×ˢ ball (0 : ℂ) ρ)) (ℓ : E)
    (M : ℝ × ℂ → E) (hM : ContDiffOn ℝ ∞ M (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hMper : ∀ (t : ℝ) (w : ℂ), M (t + 1, w) = M (t, w))
    (hdec : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
      F (cylInf q.1 q.2.1, q.2.2) - q.1 • ℓ - M (q.2.1, q.2.2)) ρ b) :
    ∃ C : ℝ, ∀ ζ w : ℂ, w ∈ closedBall (0 : ℂ) ρ' →
      (∀ h : ℂ × ℂ, ‖fderiv ℝ F (ζ, w) h‖ ≤ C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖)) ∧
      ∀ h k : ℂ × ℂ, ‖fderiv ℝ (fderiv ℝ F) (ζ, w) h k‖ ≤
        C * (‖h.1‖ / (1 + ‖ζ‖) + ‖h.2‖) * (‖k.1‖ / (1 + ‖ζ‖) + ‖k.2‖) :=
  exists_cylindrical_bounds_of_expDecayCInftyTube_aux ρ b ρ' hb hρ' hρ F hF ℓ M hM hMper hdec
