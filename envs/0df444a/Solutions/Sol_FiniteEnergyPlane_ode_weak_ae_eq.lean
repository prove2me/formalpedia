-- Prove2me | solution 1 for FiniteEnergyPlane.ode_weak_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T22:28:07.74343+00:00
-- url     : https://prove2.me/submissions/c0345063-0e39-46ed-a51e-7ca9af1ee197

import Mathlib



namespace FiniteEnergyPlane.TgInj

open Metric Set

lemma exists_R_of_hasCompactSupport {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 < R ∧ ∀ s, R < |s| → ψ s = 0 := by
  obtain ⟨R, hR⟩ := hψ.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun s hs => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have := hR h
  rw [mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left R 1]

end FiniteEnergyPlane.TgInj

/-!
# Tg-Inj layer 1 (local, NOT published): weak solutions of a first-order ODE on `ℝ`

`ode_weak_ae_eq`: if `f` is locally integrable and `∫ (-η' + Λ' η) • f = 0` for every smooth
compactly supported `η`, then `f = e^{-Λ} • C` a.e. for a constant `C`.
-/

namespace FiniteEnergyPlane.TgInj

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The primitive `∫_{-(R+1)}^s q`. -/
def prim (q : ℝ → ℝ) (R : ℝ) (s : ℝ) : ℝ := ∫ u in (-(R + 1))..s, q u

lemma prim_hasDerivAt {q : ℝ → ℝ} (hq : Continuous q) (R s : ℝ) :
    HasDerivAt (prim q R) (q s) s :=
  (hq.integral_hasStrictDerivAt (-(R + 1)) s).hasDerivAt

lemma prim_contDiff {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (R : ℝ) : ContDiff ℝ ∞ (prim q R) := by
  have hd : deriv (prim q R) = q := funext fun s => (prim_hasDerivAt hq.continuous R s).deriv
  refine contDiff_infty_iff_deriv.2
    ⟨fun s => (prim_hasDerivAt hq.continuous R s).differentiableAt, ?_⟩
  rw [hd]; exact hq

lemma prim_left {q : ℝ → ℝ} {R : ℝ} (hR0 : 0 < R) (hR : ∀ s, R < |s| → q s = 0) {s : ℝ}
    (hs : s ≤ -(R + 1)) : prim q R s = 0 := by
  unfold prim
  rw [intervalIntegral.integral_symm, neg_eq_zero]
  refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun u hu => hR u ?_)
  rw [uIoc_of_le hs] at hu
  rw [abs_of_neg (by linarith [hu.2])]
  linarith [hu.2]

lemma prim_right {q : ℝ → ℝ} (hq : Continuous q) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ s, R < |s| → q s = 0) {s : ℝ} (hs : R + 1 ≤ s) : prim q R s = ∫ u, q u := by
  unfold prim
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => hR u ?_
  rw [mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The exponential weight `e^{-Λ}`. -/
def gw (Λ : ℝ → ℝ) (s : ℝ) : ℝ := Real.exp (-Λ s)

lemma gw_contDiff {Λ : ℝ → ℝ} (hΛ : ContDiff ℝ ∞ Λ) : ContDiff ℝ ∞ (gw Λ) :=
  Real.contDiff_exp.comp hΛ.neg

lemma gw_pos (Λ : ℝ → ℝ) (s : ℝ) : 0 < gw Λ s := Real.exp_pos _

/-- Admissible test functions: `∫ ψ g = 0` makes `ψ = -η' + Λ' η` for a test `η`. -/
lemma integral_smul_eq_zero_of_admissible {Λ : ℝ → ℝ} (hΛ : ContDiff ℝ ∞ Λ) {f : ℝ → E}
    (h : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ s, (-deriv η s + deriv Λ s * η s) • f s = 0)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (h0 : ∫ s, ψ s * gw Λ s = 0) : ∫ s, ψ s • f s = 0 := by
  obtain ⟨R, hR0, hR⟩ := exists_R_of_hasCompactSupport hψc
  set q : ℝ → ℝ := fun u => gw Λ u * ψ u with hq
  have hqc : ContDiff ℝ ∞ q := (gw_contDiff hΛ).mul hψ
  have hqR : ∀ s, R < |s| → q s = 0 := fun s hs => by simp [hq, hR s hs]
  set η : ℝ → ℝ := fun s => -(Real.exp (Λ s) * prim q R s) with hη
  have hηc : ContDiff ℝ ∞ η := ((Real.contDiff_exp.comp hΛ).mul (prim_contDiff hqc R)).neg
  have hηs : HasCompactSupport η := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(R + 1)) (b := R + 1)) fun s hs => ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with hs | hs
    · simp [hη, prim_left hR0 hqR hs.le]
    · have hint : ∫ u, q u = 0 := by rw [← h0]; congr 1; funext u; simp [hq, mul_comm]
      simp [hη, prim_right hqc.continuous hR0 hqR hs.le, hint]
  have hΛd : Differentiable ℝ Λ := hΛ.differentiable (by simp)
  have hderiv : ∀ s, -deriv η s + deriv Λ s * η s = ψ s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (Λ s)) (Real.exp (Λ s) * deriv Λ s) s :=
      (hΛd s).hasDerivAt.exp
    have h2 := (h1.mul (prim_hasDerivAt hqc.continuous R s)).neg
    have h3 : deriv η s = -(Real.exp (Λ s) * deriv Λ s * prim q R s +
        Real.exp (Λ s) * q s) := h2.deriv
    rw [h3]
    have he : Real.exp (Λ s) * q s = ψ s := by
      simp only [hq, gw, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    simp only [hη]
    linear_combination he
  have := h η hηc hηs
  simp only [hderiv] at this
  exact this

lemma exists_integral_mul_gw_ne_zero (Λ : ℝ → ℝ) (hΛ : ContDiff ℝ ∞ Λ) :
    ∃ ψ₀ : ℝ → ℝ, ContDiff ℝ ∞ ψ₀ ∧ HasCompactSupport ψ₀ ∧ ∫ s, ψ₀ s * gw Λ s ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure ℝ))
    (gw_contDiff hΛ).continuous.locallyIntegrable fun ψ hψ hψc => by
      simpa only [smul_eq_mul] using hcon ψ hψ hψc
  haveI : (ae (volume : Measure ℝ)).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨s, hs⟩ := hae.exists
  exact (gw_pos Λ s).ne' hs

/-- Tg-Inj layer 1. -/
theorem ode_weak_ae_eq (Λ : ℝ → ℝ) (hΛ : ContDiff ℝ ∞ Λ) (f : ℝ → E)
    (hf : LocallyIntegrable f volume)
    (h : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ s, (-deriv η s + deriv Λ s * η s) • f s = 0) :
    ∃ C : E, ∀ᵐ s, f s = Real.exp (-Λ s) • C := by
  obtain ⟨ψ₀, hψ₀, hψ₀c, hc₀⟩ := exists_integral_mul_gw_ne_zero Λ hΛ
  set c₀ := ∫ s, ψ₀ s * gw Λ s with hc₀def
  set C : E := c₀⁻¹ • ∫ s, ψ₀ s • f s with hC
  refine ⟨C, ?_⟩
  have hgc : Continuous (gw Λ) := (gw_contDiff hΛ).continuous
  have hfg : LocallyIntegrable (fun s => f s - gw Λ s • C) volume :=
    hf.sub (hgc.smul continuous_const).locallyIntegrable
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hfg fun ψ hψ hψc => by
    set a : ℝ := ∫ s, ψ s * gw Λ s with ha
    have hint1 : Integrable (fun s => ψ s • f s) volume :=
      hf.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    have hint0 : Integrable (fun s => ψ₀ s • f s) volume :=
      hf.integrable_smul_left_of_hasCompactSupport hψ₀.continuous hψ₀c
    have hintg : Integrable (fun s => ψ s * gw Λ s) volume :=
      (hψ.continuous.mul hgc).integrable_of_hasCompactSupport hψc.mul_right
    have hintg0 : Integrable (fun s => ψ₀ s * gw Λ s) volume :=
      (hψ₀.continuous.mul hgc).integrable_of_hasCompactSupport hψ₀c.mul_right
    -- the admissible combination
    set ψ' : ℝ → ℝ := fun s => ψ s - (a / c₀) * ψ₀ s with hψ'
    have h' := integral_smul_eq_zero_of_admissible hΛ h (ψ := ψ')
      (hψ.sub (contDiff_const.mul hψ₀)) (hψc.sub hψ₀c.mul_left) (by
        have e : (fun s => ψ' s * gw Λ s) =
            fun s => ψ s * gw Λ s - (a / c₀) * (ψ₀ s * gw Λ s) := by
          funext s; simp only [hψ']; ring
        rw [e, integral_sub hintg (hintg0.const_mul _), integral_const_mul, ← hc₀def,
          div_mul_cancel₀ _ hc₀, sub_self])
    have hint0' : Integrable (fun s => (a / c₀) • (ψ₀ s • f s)) volume := hint0.smul (a / c₀)
    have h'' : (∫ s, ψ s • f s) - (a / c₀) • ∫ s, ψ₀ s • f s = 0 := by
      have e := integral_sub hint1 hint0'
      rw [integral_smul] at e
      refine e.symm.trans ((integral_congr_ae (Eventually.of_forall fun s => ?_)).trans h')
      simp only [hψ', sub_smul, mul_smul]
    rw [sub_eq_zero] at h''
    have e3 : ∫ s, ψ s • (f s - gw Λ s • C) =
        (∫ s, ψ s • f s) - ∫ s, (ψ s * gw Λ s) • C := by
      have e := integral_sub hint1 (hintg.smul_const C)
      refine (integral_congr_ae (Eventually.of_forall fun s => ?_)).trans e
      simp only [smul_sub, mul_smul]
    show ∫ s, ψ s • (f s - gw Λ s • C) = 0
    rw [e3, integral_smul_const, h'', ← ha, hC,
      smul_smul, div_eq_mul_inv, sub_self]
  filter_upwards [hae] with s hs
  rw [← sub_eq_zero]
  exact hs

end

end FiniteEnergyPlane.TgInj

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Λ : ℝ → ℝ) (hΛ : ContDiff ℝ ∞ Λ) (f : ℝ → E)
    (hf : LocallyIntegrable f volume)
    (h : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ s, (-deriv η s + deriv Λ s * η s) • f s = 0) :
    ∃ C : E, ∀ᵐ s, f s = Real.exp (-Λ s) • C :=
  FiniteEnergyPlane.TgInj.ode_weak_ae_eq Λ hΛ f hf h
