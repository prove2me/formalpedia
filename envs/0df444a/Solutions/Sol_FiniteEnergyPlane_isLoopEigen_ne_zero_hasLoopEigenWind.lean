-- Prove2me | solution 1 for FiniteEnergyPlane.isLoopEigen_ne_zero_hasLoopEigenWind
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T20:41:10.335386+00:00
-- url     : https://prove2.me/submissions/300caf07-5954-4255-98ee-51ea2fac6bda

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_apply_ne_zero
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_zero_of_forall_ne_ray



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isLoopEigen_ne_zero_hasLoopEigenWind_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (μ : ℝ)
    (e : ℝ → CauchyRiemannIndex.Vec 1) (he : IsLoopEigen Sinf μ e) :
    (∀ t : ℝ, e t ≠ 0) ∧ ∃ k : ℤ, HasLoopEigenWind Sinf μ k := by
  have hne := isLoopEigen_apply_ne_zero Sinf hSinf.1 μ
  refine ⟨hne e he, ?_⟩
  -- `vecToC` is `ℝ`-linear and injective
  have hvsub : ∀ (a b : CauchyRiemannIndex.Vec 1) (r : ℝ),
      vecToC (a - r • b) = vecToC a - r * vecToC b := fun a b r =>
    Complex.ext (by simp [vecToC]) (by simp [vecToC])
  have hvinj : ∀ a : CauchyRiemannIndex.Vec 1, vecToC a = 0 → a = 0 := by
    intro a ha
    have h1 : a (Sum.inl 0) = 0 := congrArg Complex.re ha
    have h2 : a (Sum.inr 0) = 0 := congrArg Complex.im ha
    ext i
    rcases i with i | i <;> rw [Subsingleton.elim i 0] <;> simp [h1, h2]
  have hvsmul : ∀ (b : CauchyRiemannIndex.Vec 1) (r : ℝ), vecToC (r • b) = r * vecToC b :=
    fun b r => Complex.ext (by simp [vecToC]) (by simp [vecToC])
  have hvform : ∀ a : CauchyRiemannIndex.Vec 1,
      vecToC a = ((a (Sum.inl 0) : ℝ) : ℂ) + ((a (Sum.inr 0) : ℝ) : ℂ) * Complex.I :=
    fun a => Complex.ext (by simp [vecToC]) (by simp [vecToC])
  have hcont : ∀ e', IsLoopEigen Sinf μ e' → Continuous (fun t => vecToC (e' t)) := by
    intro e' he'
    have hc := he'.1.continuous
    have h1 : Continuous fun t => e' t (Sum.inl 0) := (PiLp.continuous_apply 2 _ (Sum.inl 0)).comp hc
    have h2 : Continuous fun t => e' t (Sum.inr 0) := (PiLp.continuous_apply 2 _ (Sum.inr 0)).comp hc
    rw [show (fun t => vecToC (e' t)) = fun t => ((e' t (Sum.inl 0) : ℝ) : ℂ) +
      ((e' t (Sum.inr 0) : ℝ) : ℂ) * Complex.I from funext fun t => hvform _]
    exact (Complex.continuous_ofReal.comp h1).add
      ((Complex.continuous_ofReal.comp h2).mul continuous_const)
  have hper : ∀ e', IsLoopEigen Sinf μ e' → Function.Periodic (fun t => vecToC (e' t)) 1 :=
    fun e' he' t => by simp only [he'.2.1 t]
  have hnz : ∀ e', IsLoopEigen Sinf μ e' → ∀ t, vecToC (e' t) ≠ 0 :=
    fun e' he' t h => hne e' he' t (hvinj _ h)
  obtain ⟨k, hk⟩ := exists_hasLoopWind _ (hcont e he) (hper e he) (hnz e he)
  refine ⟨k, ⟨e, he⟩, fun e' he' => ?_⟩
  -- a real multiple of `e` agreeing with `e'` at one point agrees everywhere
  have key : ∀ (r t₀ : ℝ), vecToC (e' t₀) = r * vecToC (e t₀) → ∀ t, e' t = r • e t := by
    intro r t₀ h t
    by_contra hc
    have hd : IsLoopEigen Sinf μ (fun t => e' t - r • e t) := by
      refine ⟨he'.1.sub (he.1.const_smul r), fun s => by simp only [he'.2.1 s, he.2.1 s],
        ⟨t, sub_ne_zero.mpr hc⟩, fun s => ?_⟩
      have d1 : DifferentiableAt ℝ e' s := (he'.1.differentiable (by simp)) s
      have d2 : DifferentiableAt ℝ e s := (he.1.differentiable (by simp)) s
      have hder : deriv (fun t => e' t - r • e t) s = deriv e' s - r • deriv e s := by
        exact (d1.hasDerivAt.sub (d2.hasDerivAt.const_smul r)).deriv
      rw [hder, map_sub, map_smul, map_sub, map_smul]
      have h1 := he'.2.2.2 s
      have h2 := he.2.2.2 s
      linear_combination (norm := module) h1 - r • h2
    exact hne _ hd t₀ (hvinj _ (by rw [hvsub, h, sub_self]))
  set f := fun t => vecToC (e t) with hf
  set g := fun t => vecToC (e' t) with hg
  have hf0 : ∀ t, f t ≠ 0 := hnz e he
  have hqc : Continuous fun t => g t / f t := (hcont e' he').div (hcont e he) hf0
  have hqp : Function.Periodic (fun t => g t / f t) 1 := (hper e' he').div (hper e he)
  have hgq : (fun t => g t) = fun t => (g t / f t) * f t :=
    funext fun t => (div_mul_cancel₀ _ (hf0 t)).symm
  suffices hq : HasLoopWind (fun t => g t / f t) 0 by
    have := hasLoopWind_mul hq hk
    rw [zero_add] at this
    show HasLoopWind g k
    rw [show g = fun t => g t from rfl, hgq]
    exact this
  by_cases hs : ∀ t, g t / f t ∈ Complex.slitPlane
  · refine hasLoopWind_zero_of_forall_ne_ray _ hqc hqp (-1) (by norm_num) fun t s hs0 h => ?_
    have := hs t
    rw [h, Complex.mem_slitPlane_iff] at this
    rcases this with h' | h' <;> simp at h' <;> linarith
  · push_neg at hs
    obtain ⟨t₀, ht₀⟩ := hs
    rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at ht₀
    set r := (g t₀ / f t₀).re with hr
    have hreal : g t₀ / f t₀ = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [ht₀.2])
    have hgr : g t₀ = r * f t₀ := by rw [← hreal, div_mul_cancel₀ _ (hf0 t₀)]
    have hall := key r t₀ hgr
    have hqr : ∀ t, g t / f t = r := fun t => by
      have h3 : g t = r * f t := by
        show vecToC (e' t) = r * vecToC (e t)
        rw [hall t, hvsmul]
      rw [h3, mul_div_cancel_right₀ _ (hf0 t)]
    have hr0 : r ≠ 0 := by
      intro h0
      apply hnz e' he' t₀
      show g t₀ = 0
      rw [hgr, h0]
      simp
    have hrneg : r < 0 := lt_of_le_of_ne ht₀.1 hr0
    refine hasLoopWind_zero_of_forall_ne_ray _ hqc hqp 1 one_ne_zero fun t s hs0 h => ?_
    rw [hqr t, mul_one] at h
    have := congrArg Complex.re h
    simp at this
    linarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (μ : ℝ)
    (e : ℝ → CauchyRiemannIndex.Vec 1) (he : IsLoopEigen Sinf μ e) :
    (∀ t : ℝ, e t ≠ 0) ∧ ∃ k : ℤ, HasLoopEigenWind Sinf μ k :=
  isLoopEigen_ne_zero_hasLoopEigenWind_aux Sinf hSinf hSinf' μ e he
