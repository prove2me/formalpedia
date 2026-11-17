-- Prove2me | solution 1 for FiniteEnergyPlane.exists_jbar_of_tubeMap
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T18:07:54.013275+00:00
-- url     : https://prove2.me/submissions/323d3da7-ddec-409e-a503-ed8afaa48b83

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_fderiv_tubeMap_apply_zero



/-!
# S, child C6c (local proof): the pulled-back structure `Jbar` on the tube.
-/

namespace FiniteEnergyPlane

open Filter Topology Metric Set
open scoped ContDiff

noncomputable section

namespace SMFC

lemma finrank_CC : Module.finrank ℝ (ℂ × ℂ) = 4 := by
  rw [Module.finrank_prod, Complex.finrank_real_complex]

lemma finrank_V1 : Module.finrank ℝ (V 1) = 4 := by
  simp [V]

/-- An injective map `ℂ × ℂ → V 1` is an isomorphism. -/
lemma exists_equiv_of_injective (L : ℂ × ℂ →L[ℝ] V 1) (hL : Function.Injective L) :
    ∃ e : (ℂ × ℂ) ≃L[ℝ] V 1, (e : ℂ × ℂ →L[ℝ] V 1) = L := by
  let e₀ := LinearMap.linearEquivOfInjective L.toLinearMap hL (by rw [finrank_CC, finrank_V1])
  refine ⟨e₀.toContinuousLinearEquiv, ?_⟩
  ext h <;> rfl

lemma clm_apply_complex {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (L : ℂ →L[ℝ] X) (w : ℂ) : L w = w.re • L 1 + w.im • L Complex.I := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [map_add, show (w.re : ℂ) = w.re • (1 : ℂ) by simp,
    show (w.im : ℂ) * Complex.I = w.im • Complex.I by simp, map_smul, map_smul]

/-- A map satisfying the Cauchy–Riemann equation for `K` with `K² = -1` is `K`-linear. -/
lemma apply_I_mul (K : V 1 →L[ℝ] V 1) (hK : ∀ v, K (K v) = -v) (D : ℂ →L[ℝ] V 1)
    (h : D 1 + K (D Complex.I) = 0) (Δ : ℂ) : D (Complex.I * Δ) = K (D Δ) := by
  have h1 : D 1 = -K (D Complex.I) := eq_neg_of_add_eq_zero_left h
  have h2 : K (D 1) = D Complex.I := by rw [h1, map_neg, hK, neg_neg]
  rw [clm_apply_complex D (Complex.I * Δ), clm_apply_complex D Δ, map_add, map_smul, map_smul,
    h2, h1]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, add_zero, zero_add]
  module

/-- Conjugation of `K` by an isomorphism. -/
lemma conj_facts (e : (ℂ × ℂ) ≃L[ℝ] V 1) (K : V 1 →L[ℝ] V 1) :
    (e : ℂ × ℂ →L[ℝ] V 1).comp
        ((e : ℂ × ℂ →L[ℝ] V 1).inverse.comp (K.comp (e : ℂ × ℂ →L[ℝ] V 1))) =
      K.comp (e : ℂ × ℂ →L[ℝ] V 1) ∧
    ((∀ v, K (K v) = -v) →
      ((e : ℂ × ℂ →L[ℝ] V 1).inverse.comp (K.comp (e : ℂ × ℂ →L[ℝ] V 1))).comp
        ((e : ℂ × ℂ →L[ℝ] V 1).inverse.comp (K.comp (e : ℂ × ℂ →L[ℝ] V 1))) =
        -ContinuousLinearMap.id ℝ (ℂ × ℂ)) := by
  rw [ContinuousLinearMap.inverse_equiv]
  refine ⟨?_, fun hK => ?_⟩
  · ext v <;> simp
  · ext v <;> simp [hK]

end SMFC

theorem exists_jbar_of_tubeMap_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNJ : ∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p)) :
    ∃ Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ,
      ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
        (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ)) ∧
      (∀ z : ℂ, Jbar (z, 0) = jStd) ∧
      ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
        (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
          (Jtilde H J (u p.1 + N p.1 p.2)).comp
            (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) := by
  obtain ⟨⟨hOJ, hJc, hJsq⟩, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  have hK : ∀ y : V 1, y ≠ 0 → ∀ v, Jtilde H J y (Jtilde H J y v) = -v := fun y hy v => by
    simpa using DFunLike.congr_fun (hJsq y hy) v
  set Φ : ℂ × ℂ → V 1 := fun q => u q.1 + N q.1 q.2 with hΦdef
  have hΦc : ContDiff ℝ ∞ Φ :=
    (hu.comp contDiff_fst).add ((hN.comp contDiff_fst).clm_apply contDiff_snd)
  have hDc : ContDiff ℝ ∞ (fderiv ℝ Φ) := hΦc.fderiv_right (m := ∞) (by simp)
  set Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ := fun p =>
    (fderiv ℝ Φ p).inverse.comp ((Jtilde H J (Φ p)).comp (fderiv ℝ Φ p)) with hJbar
  have hO : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (ℂ × ℂ)) := isOpen_univ.prod isOpen_ball
  refine ⟨Jbar, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hp0, hpi⟩ := hΦ p hp
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hpi
    have h1 : ContDiffAt ℝ ∞ (fun q => (fderiv ℝ Φ q).inverse) p := by
      have := contDiffAt_map_inverse (n := ∞) e
      rw [he] at this
      exact this.comp p hDc.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (Jtilde H J ∘ Φ) p :=
      (hJc.contDiffAt (hOJ.mem_nhds hp0)).comp p hΦc.contDiffAt
    exact (h1.clm_comp (h2.clm_comp hDc.contDiffAt)).contDiffWithinAt
  · intro p hp
    obtain ⟨hp0, hpi⟩ := hΦ p hp
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hpi
    have := (SMFC.conj_facts e (Jtilde H J (Φ p))).2 (hK _ hp0)
    rw [he] at this
    exact this
  · intro z
    have hz : ((z, 0) : ℂ × ℂ) ∈ Set.univ ×ˢ ball (0 : ℂ) ρ := ⟨mem_univ _, mem_ball_self hρ⟩
    obtain ⟨hp0, hpi⟩ := hΦ _ hz
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hpi
    have hΦz : Φ (z, 0) = u z := by simp [hΦdef]
    have hu0 : u z ≠ 0 := hΦz ▸ hp0
    have hdb : fderiv ℝ u z 1 + Jtilde H J (u z) (fderiv ℝ u z Complex.I) = 0 :=
      (hhol z (mem_univ z)).2
    have hD : ∀ Δ ν : ℂ, fderiv ℝ Φ (z, 0) (Δ, ν) = fderiv ℝ u z Δ + N z ν :=
      fun Δ ν => fderiv_tubeMap_apply_zero u N (hu.differentiable (by simp))
        (hN.differentiable (by simp)) z Δ ν
    have hcomm : (Jtilde H J (Φ (z, 0))).comp (e : ℂ × ℂ →L[ℝ] V 1) =
        (e : ℂ × ℂ →L[ℝ] V 1).comp jStd := by
      rw [he, hΦz]
      refine ContinuousLinearMap.ext fun v => ?_
      obtain ⟨Δ, ν⟩ := v
      have hj : jStd (Δ, ν) = (Complex.I * Δ, Complex.I * ν) := by simp [jStd]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hj, hD, map_add]
      rw [SMFC.apply_I_mul _ (hK _ hu0) _ hdb, hNJ]
    show (fderiv ℝ Φ (z, 0)).inverse.comp ((Jtilde H J (Φ (z, 0))).comp (fderiv ℝ Φ (z, 0))) = jStd
    rw [← he, hcomm, ContinuousLinearMap.inverse_equiv]
    ext v <;> simp
  · intro p hp
    obtain ⟨-, hpi⟩ := hΦ p hp
    obtain ⟨e, he⟩ := SMFC.exists_equiv_of_injective _ hpi
    have := (SMFC.conj_facts e (Jtilde H J (Φ p))).1
    rw [he] at this
    exact this

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNJ : ∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hΦ : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
      Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p)) :
    ∃ Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ,
      ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
        (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ)) ∧
      (∀ z : ℂ, Jbar (z, 0) = jStd) ∧
      ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
        (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
          (Jtilde H J (u p.1 + N p.1 p.2)).comp
            (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) :=
  exists_jbar_of_tubeMap_aux H hH J hJ u hu hhol N hN hNJ ρ hρ hΦ
