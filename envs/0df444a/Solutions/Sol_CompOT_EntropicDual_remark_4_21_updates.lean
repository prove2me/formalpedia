-- Prove2me | solution 1 for CompOT.EntropicDual.remark_4_21_updates
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:35:22.560844+00:00
-- url     : https://prove2.me/submissions/173e4798-58c7-48e1-9c9a-b242e6423412

import Mathlib
import Definitions.Def_CompOT_EntropicDual_Defs

set_option autoImplicit false
open CompOT.EntropicDual

theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ j, 0 < b j) :
    (∀ g f, dualObjEnt C a b ε f g ≤ dualObjEnt C a b ε (updateF C a ε g) g ∧
      (dualObjEnt C a b ε f g = dualObjEnt C a b ε (updateF C a ε g) g →
        f = updateF C a ε g)) ∧
    (∀ f g, dualObjEnt C a b ε f g ≤ dualObjEnt C a b ε f (updateG C b ε f) ∧
      (dualObjEnt C a b ε f g = dualObjEnt C a b ε f (updateG C b ε f) →
        g = updateG C b ε f)) := by
  -- scalar maximisation
  have sc : ∀ (A T : ℝ), 0 < A → 0 < T → ∀ x : ℝ,
      x * A - ε * Real.exp (x / ε) * T ≤
        (ε * Real.log A - ε * Real.log T) * A -
          ε * Real.exp ((ε * Real.log A - ε * Real.log T) / ε) * T ∧
      (x * A - ε * Real.exp (x / ε) * T =
        (ε * Real.log A - ε * Real.log T) * A -
          ε * Real.exp ((ε * Real.log A - ε * Real.log T) / ε) * T →
        x = ε * Real.log A - ε * Real.log T) := by
    intro A T hA hT x
    have hx0 : Real.exp ((ε * Real.log A - ε * Real.log T) / ε) = A / T := by
      have : (ε * Real.log A - ε * Real.log T) / ε = Real.log A - Real.log T := by
        field_simp
      rw [this, Real.exp_sub, Real.exp_log hA, Real.exp_log hT]
    set r : ℝ := Real.exp (x / ε) * T / A with hr
    have hrpos : 0 < r := by positivity
    have hlogr : Real.log r = x / ε + Real.log T - Real.log A := by
      rw [hr, Real.log_div (by positivity) hA.ne', Real.log_mul (Real.exp_pos _).ne' hT.ne',
        Real.log_exp]
    have hxr : x - (ε * Real.log A - ε * Real.log T) = ε * Real.log r := by
      rw [hlogr]; field_simp; ring
    have hrA : Real.exp (x / ε) * T = r * A := by rw [hr]; field_simp
    rw [hx0]
    have hdiff : x * A - ε * Real.exp (x / ε) * T -
        ((ε * Real.log A - ε * Real.log T) * A - ε * (A / T) * T) =
        ε * A * (Real.log r - r + 1) := by
      have e : ε * (A / T) * T = ε * A := by field_simp
      have e2 : ε * Real.exp (x / ε) * T = ε * (r * A) := by rw [mul_assoc, hrA]
      rw [e, e2]
      have : x = (ε * Real.log A - ε * Real.log T) + ε * Real.log r := by linarith
      conv_lhs => rw [this]
      ring
    have hεA : 0 < ε * A := mul_pos hε hA
    constructor
    · have := Real.log_le_sub_one_of_pos hrpos
      nlinarith [mul_nonneg hεA.le (sub_nonneg.2 this)]
    · intro heq
      by_contra hne
      have hr1 : r ≠ 1 := by
        intro h1
        apply hne
        have : Real.log r = 0 := by rw [h1]; simp
        rw [this, mul_zero] at hxr
        linarith [hxr]
      have := Real.log_lt_sub_one_of_pos hrpos hr1
      nlinarith [mul_pos hεA (sub_pos.2 this)]
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hQf : ∀ f g, dualObjEnt C a b ε f g =
      ∑ i, (f i * a i - ε * Real.exp (f i / ε) * ∑ j, gibbs C ε i j * Real.exp (g j / ε)) +
        ∑ j, g j * b j := by
    intro f g
    unfold dualObjEnt
    have h1 : ∑ i, ∑ j, Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε) =
        ∑ i, Real.exp (f i / ε) * ∑ j, gibbs C ε i j * Real.exp (g j / ε) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    have h2 : ∑ i, (f i * a i - ε * Real.exp (f i / ε) * ∑ j, gibbs C ε i j * Real.exp (g j / ε)) =
        ∑ i, f i * a i - ε * ∑ i, Real.exp (f i / ε) * ∑ j, gibbs C ε i j * Real.exp (g j / ε) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intros; ring
    rw [h1, h2]; ring
  have hQg : ∀ f g, dualObjEnt C a b ε f g =
      ∑ j, (g j * b j - ε * Real.exp (g j / ε) * ∑ i, gibbs C ε i j * Real.exp (f i / ε)) +
        ∑ i, f i * a i := by
    intro f g
    unfold dualObjEnt
    have h1 : ∑ i, ∑ j, Real.exp (f i / ε) * gibbs C ε i j * Real.exp (g j / ε) =
        ∑ j, Real.exp (g j / ε) * ∑ i, gibbs C ε i j * Real.exp (f i / ε) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    have h2 : ∑ j, (g j * b j - ε * Real.exp (g j / ε) * ∑ i, gibbs C ε i j * Real.exp (f i / ε)) =
        ∑ j, g j * b j - ε * ∑ j, Real.exp (g j / ε) * ∑ i, gibbs C ε i j * Real.exp (f i / ε) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intros; ring
    rw [h1, h2]; ring
  have hSpos : ∀ (g : Fin m → ℝ) (i : Fin n), 0 < ∑ j, gibbs C ε i j * Real.exp (g j / ε) := fun g i =>
    Finset.sum_pos (fun j _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) Finset.univ_nonempty
  have hTpos : ∀ (f : Fin n → ℝ) (j : Fin m), 0 < ∑ i, gibbs C ε i j * Real.exp (f i / ε) := fun f j =>
    Finset.sum_pos (fun i _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) Finset.univ_nonempty
  constructor
  · intro g f
    rw [hQf f g, hQf (updateF C a ε g) g]
    have hle : ∀ i, f i * a i - ε * Real.exp (f i / ε) * ∑ j, gibbs C ε i j * Real.exp (g j / ε) ≤
        updateF C a ε g i * a i - ε * Real.exp (updateF C a ε g i / ε) *
          ∑ j, gibbs C ε i j * Real.exp (g j / ε) := fun i =>
      (sc (a i) _ (ha_pos i) (hSpos g i) (f i)).1
    refine ⟨by linarith [Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)], ?_⟩
    intro heq
    have heq' : ∑ i, (f i * a i - ε * Real.exp (f i / ε) * ∑ j, gibbs C ε i j * Real.exp (g j / ε)) =
        ∑ i, (updateF C a ε g i * a i - ε * Real.exp (updateF C a ε g i / ε) *
          ∑ j, gibbs C ε i j * Real.exp (g j / ε)) := by linarith
    have := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ Finset.univ) => hle i)).1 heq'
    funext i
    exact (sc (a i) _ (ha_pos i) (hSpos g i) (f i)).2 (this i (Finset.mem_univ i))
  · intro f g
    rw [hQg f g, hQg f (updateG C b ε f)]
    have hle : ∀ j, g j * b j - ε * Real.exp (g j / ε) * ∑ i, gibbs C ε i j * Real.exp (f i / ε) ≤
        updateG C b ε f j * b j - ε * Real.exp (updateG C b ε f j / ε) *
          ∑ i, gibbs C ε i j * Real.exp (f i / ε) := fun j =>
      (sc (b j) _ (hb_pos j) (hTpos f j) (g j)).1
    refine ⟨by linarith [Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hle j)], ?_⟩
    intro heq
    have heq' : ∑ j, (g j * b j - ε * Real.exp (g j / ε) * ∑ i, gibbs C ε i j * Real.exp (f i / ε)) =
        ∑ j, (updateG C b ε f j * b j - ε * Real.exp (updateG C b ε f j / ε) *
          ∑ i, gibbs C ε i j * Real.exp (f i / ε)) := by linarith
    have := (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ Finset.univ) => hle j)).1 heq'
    funext j
    exact (sc (b j) _ (hb_pos j) (hTpos f j) (g j)).2 (this j (Finset.mem_univ j))
