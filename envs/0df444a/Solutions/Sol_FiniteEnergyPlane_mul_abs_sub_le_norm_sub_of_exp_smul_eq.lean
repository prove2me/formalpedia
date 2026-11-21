-- Prove2me | solution 1 for FiniteEnergyPlane.mul_abs_sub_le_norm_sub_of_exp_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-20T21:11:51.856194+00:00
-- url     : https://prove2.me/submissions/1b3df943-6193-4b2b-9e1c-9f6e4e89d55d

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics



/-! F helpers H1, H2. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_norm_le_and_norm_sub_le_of_tendstoZeroCInfty_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × ℝ → F}
    (hf : TendstoZeroCInfty f) (η : ℝ) (hη : 0 < η) :
    ∃ S : ℝ, ∀ p q : ℝ × ℝ, S ≤ p.1 → S ≤ q.1 → ‖f p‖ ≤ η ∧ ‖f p - f q‖ ≤ η * ‖p - q‖ := by
  obtain ⟨⟨s₀, hsm⟩, hd⟩ := hf
  obtain ⟨s₁, hs₁⟩ := hd 0 η hη
  obtain ⟨s₂, hs₂⟩ := hd 1 η hη
  set S₀ := max (max s₀ s₁) s₂ + 1 with hS₀
  have h0 : s₀ < S₀ := by
    have := le_max_left s₀ s₁; have := le_max_left (max s₀ s₁) s₂; linarith
  have h1 : s₁ ≤ S₀ := by
    have := le_max_right s₀ s₁; have := le_max_left (max s₀ s₁) s₂; linarith
  have h2 : s₂ ≤ S₀ := by have := le_max_right (max s₀ s₁) s₂; linarith
  refine ⟨S₀, fun p q hp hq => ⟨?_, ?_⟩⟩
  · have := hs₁ p.1 (le_trans h1 hp) p.2
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  · set U := Set.Ici S₀ ×ˢ (Set.univ : Set ℝ) with hU
    have hUc : Convex ℝ U := (convex_Ici _).prod convex_univ
    have hopen : IsOpen (Set.Ioi s₀ ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
    have hdiff : ∀ x ∈ U, DifferentiableAt ℝ f x := fun x hx =>
      (hsm.contDiffAt (hopen.mem_nhds ⟨lt_of_lt_of_le h0 hx.1, trivial⟩)).differentiableAt
        (by simp)
    have hb : ∀ x ∈ U, ‖fderiv ℝ f x‖ ≤ η := fun x hx => by
      have := hs₂ x.1 (le_trans h2 hx.1) x.2
      rw [norm_iteratedFDeriv_one] at this
      exact this
    exact _root_.Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) hdiff hb hUc ⟨hq, trivial⟩ ⟨hp, trivial⟩

theorem mul_abs_sub_le_norm_sub_of_exp_smul_eq_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ m : ℝ} (hμ : μ < 0)
    {V₀ r₁ r₂ : E} (hm : m ≤ ‖V₀‖) (hr₁ : ‖r₁‖ ≤ m / 2) (hr₂ : ‖r₂‖ ≤ m / 2) :
    ∀ s s' : ℝ, Real.exp (μ * s) • (V₀ + r₁) = Real.exp (μ * s') • (V₀ + r₂) →
      (-μ) * |s - s'| * (m / 2) ≤ ‖r₁ - r₂‖ := by
  have key : ∀ (a b : E), ‖a‖ ≤ m / 2 → ‖b‖ ≤ m / 2 → ∀ s s' : ℝ, s' ≤ s →
      Real.exp (μ * s) • (V₀ + a) = Real.exp (μ * s') • (V₀ + b) →
      (-μ) * |s - s'| * (m / 2) ≤ ‖a - b‖ := by
    intro a b ha hb s s' hss heq
    set x := -μ * (s - s') with hx
    have hx0 : 0 ≤ x := by rw [hx]; nlinarith
    set α := Real.exp (-x) with hα
    have hαpos : 0 < α := Real.exp_pos _
    have hsplit : Real.exp (μ * s) = α * Real.exp (μ * s') := by
      rw [hα, ← Real.exp_add]; congr 1; rw [hx]; ring
    rw [hsplit, mul_comm, mul_smul] at heq
    have heq' : α • (V₀ + a) = V₀ + b :=
      smul_right_injective E (Real.exp_pos (μ * s')).ne' heq
    have hid : (1 - α) • (V₀ + b) = α • (a - b) := by
      rw [sub_smul, one_smul]
      conv_lhs => arg 1; rw [← heq']
      rw [← smul_sub]; congr 1; abel
    have hn := congrArg norm hid
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (le_of_lt hαpos)] at hn
    have hα1 : α ≤ 1 := by rw [hα]; exact Real.exp_le_one_iff.2 (by linarith)
    rw [Real.norm_of_nonneg (by linarith)] at hn
    have hVb : m / 2 ≤ ‖V₀ + b‖ := by
      have := norm_sub_norm_le V₀ (-b)
      rw [sub_neg_eq_add, norm_neg] at this
      linarith
    have hxα : α * x ≤ 1 - α := by
      have h := Real.add_one_le_exp x
      have : α * Real.exp x = 1 := by rw [hα, ← Real.exp_add]; simp
      nlinarith
    have habs : |s - s'| = s - s' := abs_of_nonneg (by linarith)
    have hm0 : 0 ≤ m / 2 := le_trans (norm_nonneg _) ha
    have : α * (x * (m / 2)) ≤ α * ‖a - b‖ := by
      calc α * (x * (m / 2)) = (α * x) * (m / 2) := by ring
        _ ≤ (1 - α) * (m / 2) := mul_le_mul_of_nonneg_right hxα hm0
        _ ≤ (1 - α) * ‖V₀ + b‖ := mul_le_mul_of_nonneg_left hVb (by linarith)
        _ = α * ‖a - b‖ := hn
    have := le_of_mul_le_mul_left this hαpos
    rw [habs]
    calc (-μ) * (s - s') * (m / 2) = x * (m / 2) := by rw [hx]
      _ ≤ ‖a - b‖ := this
  intro s s' heq
  rcases le_total s' s with h | h
  · exact key r₁ r₂ hr₁ hr₂ s s' h heq
  · have := key r₂ r₁ hr₂ hr₁ s' s h heq.symm
    rwa [abs_sub_comm, norm_sub_rev] at this

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {μ m : ℝ} (hμ : μ < 0)
    {V₀ r₁ r₂ : E} (hm : m ≤ ‖V₀‖) (hr₁ : ‖r₁‖ ≤ m / 2) (hr₂ : ‖r₂‖ ≤ m / 2) :
    ∀ s s' : ℝ, Real.exp (μ * s) • (V₀ + r₁) = Real.exp (μ * s') • (V₀ + r₂) →
      (-μ) * |s - s'| * (m / 2) ≤ ‖r₁ - r₂‖ :=
  mul_abs_sub_le_norm_sub_of_exp_smul_eq_aux hμ hm hr₁ hr₂
