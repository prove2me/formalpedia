-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityC.prop_3_22_periodic_local_optimality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:23:27.767973+00:00
-- url     : https://prove2.me/submissions/6483eba5-1a15-4a68-a4c1-033f90dd3658

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_DomZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IndicatorVec



namespace DiscreteConvex.IntegralConvexityC

lemma p322_shift {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hper : ∀ z : Fin n → ℤ, f (z + fun _ => (1 : ℤ)) = f z) (z : Fin n → ℤ) :
    ∀ k : ℕ, f (z + fun _ => (k : ℤ)) = f z := by
  intro k
  induction k with
  | zero => congr 1; funext i; simp
  | succ k ih =>
    have : (z + fun _ => ((k+1 : ℕ) : ℤ)) = (z + fun _ => (k : ℤ)) + fun _ => (1 : ℤ) := by
      funext i; simp; ring
    rw [this, hper, ih]

theorem p322_core {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hic : IntegrallyConvex f) (hper : ∀ z : Fin n → ℤ, f (z + fun _ => (1 : ℤ)) = f z)
    (x : Fin n → ℤ) (hx : x ∈ DomZ f) :
    (∀ y : Fin n → ℤ, f x ≤ f y) ↔
      (∀ Y : Finset (Fin n), f x ≤ f (x + IndicatorVec Y)) := by
  constructor
  · intro h Y; exact h _
  intro hloc y
  by_contra hlt
  push_neg at hlt
  have hx' : f x ≠ ⊤ := hx
  set fx : ℝ := (f x).untop hx' with hfx_def
  have hfx : f x = (fx : WithTop ℝ) := (WithTop.coe_untop _ hx').symm
  have hy' : f y ≠ ⊤ := ne_top_of_lt hlt
  set fy : ℝ := (f y).untop hy' with hfy_def
  have hfy : f y = (fy : WithTop ℝ) := (WithTop.coe_untop _ hy').symm
  have hlt' : fy < fx := by rw [hfx, hfy] at hlt; exact_mod_cast hlt
  -- shifted y
  set K : ℕ := ∑ i, (x i - y i).toNat with hK
  set y2 : Fin n → ℤ := y + fun _ => (K : ℤ) with hy2
  have hfy2 : f y2 = f y := p322_shift f hper y K
  have hge : ∀ i, x i ≤ y2 i := by
    intro i
    have h1 : (x i - y i).toNat ≤ K :=
      Finset.single_le_sum (f := fun i => (x i - y i).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : ((x i - y i).toNat : ℤ) ≤ (K : ℤ) := by exact_mod_cast h1
    have h3 : x i - y i ≤ ((x i - y i).toNat : ℤ) := Int.self_le_toNat _
    simp only [hy2, Pi.add_apply]
    linarith
  set D : ℝ := ∑ i, ((y2 i : ℝ) - x i) with hD
  have hdi : ∀ i, 0 ≤ (y2 i : ℝ) - x i := fun i => by
    have := hge i; have : (x i : ℝ) ≤ y2 i := by exact_mod_cast this
    linarith
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun i _ => hdi i)
  have hdiD : ∀ i, (y2 i : ℝ) - x i ≤ D := fun i =>
    Finset.single_le_sum (f := fun i => ((y2 i : ℝ) - x i)) (fun i _ => hdi i)
      (Finset.mem_univ i)
  set ε : ℝ := 1 / (D + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by linarith)]; linarith
  have hεd : ∀ i, ε * ((y2 i : ℝ) - x i) ≤ 1 := by
    intro i
    rw [hε, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
    linarith [hdiD i]
  set z : Fin n → ℝ := fun i => (x i : ℝ) + ε * ((y2 i : ℝ) - x i) with hz
  -- lower bound
  have hlow : ((fx : ℝ) : EReal) ≤ LocalConvexExtension f z := by
    unfold LocalConvexExtension
    refine le_sSup ⟨0, fx, fun w hw => ?_, by simp⟩
    have hw1 : ∀ i, x i ≤ w i := by
      intro i
      have := (hw i).1
      have h2 : x i ≤ ⌊z i⌋ := Int.le_floor.mpr (by
        simp only [hz]; have := mul_nonneg hε0.le (hdi i); linarith)
      linarith
    have hw2 : ∀ i, w i ≤ x i + 1 := by
      intro i
      have := (hw i).2
      have h2 : ⌈z i⌉ ≤ x i + 1 := Int.ceil_le.mpr (by
        simp only [hz]; push_cast; linarith [hεd i])
      linarith
    have hweq : w = x + IndicatorVec (Finset.univ.filter (fun i => w i ≠ x i)) := by
      funext i
      simp only [Pi.add_apply, IndicatorVec, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h
      · have := hw1 i; have := hw2 i; omega
      · push_neg at h; omega
    have hfw : f x ≤ f w := by rw [hweq]; exact hloc _
    rw [hfx] at hfw
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    exact WithBot.coe_le_coe.mpr hfw
  -- upper bound
  have hup : ConvexClosure f z ≤ (((1 - ε) * fx + ε * fy : ℝ) : EReal) := by
    unfold ConvexClosure
    refine sSup_le (fun v hv => ?_)
    obtain ⟨p, a, hmin, rfl⟩ := hv
    have h1 := hmin x
    have h2 := hmin y2
    rw [hfx] at h1
    rw [hfy2, hfy] at h2
    have h1' : a + ∑ i, p i * (x i : ℝ) ≤ fx := EReal.coe_le_coe_iff.mp h1
    have h2' : a + ∑ i, p i * (y2 i : ℝ) ≤ fy := EReal.coe_le_coe_iff.mp h2
    have hs : ∑ i, p i * z i = ∑ i, p i * (x i : ℝ) +
        ε * (∑ i, p i * (y2 i : ℝ) - ∑ i, p i * (x i : ℝ)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hz]; ring
    rw [EReal.coe_le_coe_iff, hs]
    nlinarith
  have := hic z
  rw [this] at hlow
  have hfin := le_trans hlow hup
  have hfin' : fx ≤ (1 - ε) * fx + ε * fy := EReal.coe_le_coe_iff.mp hfin
  nlinarith

end DiscreteConvex.IntegralConvexityC

open DiscreteConvex.IntegralConvexityC


theorem solution {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ)
    (hic : IntegrallyConvex f) (hper : ∀ z : Fin n → ℤ, f (z + fun _ => (1 : ℤ)) = f z)
    (x : Fin n → ℤ) (hx : x ∈ DomZ f) :
    (∀ y : Fin n → ℤ, f x ≤ f y) ↔
      (∀ Y : Finset (Fin n), f x ≤ f (x + IndicatorVec Y)) := by
  exact p322_core f hic hper x hx
