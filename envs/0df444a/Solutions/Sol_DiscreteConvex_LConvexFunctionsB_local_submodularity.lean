-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.local_submodularity
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T00:06:50.724894+00:00
-- url     : https://prove2.me/submissions/a23214aa-3011-407a-8dac-ad0def856d50

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LNatConvexSet

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsB

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma dom_max_sub_one {D : Set (V → ℤ)} (hdom : LNatConvexSet D)
    {p q : V → ℤ} (hp : p ∈ D) (hq : q ∈ D) :
    (fun v => max (p v - 1) (q v)) ∈ D := by
  let x₁ : Option V → ℤ := fun o => Option.elim o (-1) (fun v => p v - 1)
  let x₂ : Option V → ℤ := fun o => Option.elim o 0 q
  have hx₁ : x₁ ∈ LiftedSetL D := by
    change (fun v => x₁ (some v) - x₁ none) ∈ D
    have hEq : (fun v => x₁ (some v) - x₁ none) = p := by
      ext v
      dsimp [x₁]
      ring
    rwa [hEq]
  have hx₂ : x₂ ∈ LiftedSetL D := by
    change (fun v => x₂ (some v) - x₂ none) ∈ D
    have hEq : (fun v => x₂ (some v) - x₂ none) = q := by
      ext v
      dsimp [x₂]
      ring
    rwa [hEq]
  have hmax := (hdom.2.1 x₁ hx₁ x₂ hx₂).1
  change (fun v => max (x₁ (some v)) (x₂ (some v)) - max (x₁ none) (x₂ none)) ∈ D at hmax
  have hEq : (fun v => max (x₁ (some v)) (x₂ (some v)) - max (x₁ none) (x₂ none)) =
      (fun v => max (p v - 1) (q v)) := by
    ext v
    dsimp [x₁, x₂]
    omega
  rwa [hEq] at hmax

private lemma dom_min {D : Set (V → ℤ)} (hdom : LNatConvexSet D)
    {p q : V → ℤ} (hp : p ∈ D) (hq : q ∈ D) :
    (fun v => min (p v) (q v)) ∈ D := by
  let x₁ : Option V → ℤ := fun o => Option.elim o 0 p
  let x₂ : Option V → ℤ := fun o => Option.elim o 0 q
  have hx₁ : x₁ ∈ LiftedSetL D := by
    change (fun v => x₁ (some v) - x₁ none) ∈ D
    have hEq : (fun v => x₁ (some v) - x₁ none) = p := by
      ext v
      dsimp [x₁]
      ring
    rwa [hEq]
  have hx₂ : x₂ ∈ LiftedSetL D := by
    change (fun v => x₂ (some v) - x₂ none) ∈ D
    have hEq : (fun v => x₂ (some v) - x₂ none) = q := by
      ext v
      dsimp [x₂]
      ring
    rwa [hEq]
  have hmin := (hdom.2.1 x₁ hx₁ x₂ hx₂).2
  change (fun v => min (x₁ (some v)) (x₂ (some v)) - min (x₁ none) (x₂ none)) ∈ D at hmin
  have hEq : (fun v => min (x₁ (some v)) (x₂ (some v)) - min (x₁ none) (x₂ none)) =
      (fun v => min (p v) (q v)) := by
    ext v
    dsimp [x₁, x₂]
    omega
  rwa [hEq] at hmin

private lemma withtop_chain {gp gq gy gz gsup ginf : WithTop ℝ}
    (hy : gy ≠ ⊤) (hz : gz ≠ ⊤)
    (h1 : gp + gy ≥ gsup + gz) (h2 : gz + gq ≥ gy + ginf) :
    gp + gq ≥ gsup + ginf := by
  lift gy to ℝ using hy
  lift gz to ℝ using hz
  cases gp <;> cases gq <;> cases gsup <;> cases ginf <;>
    simp [← WithTop.coe_add, WithTop.coe_le_coe] at h1 h2 ⊢ <;> linarith

private def distMeasure (p q : V → ℤ) : ℕ :=
  ∑ v : V, (p v - min (p v) (q v)).natAbs

private lemma distMeasure_lt {p q : V → ℤ} {v₀ : V} (hv₀ : q v₀ < p v₀) :
    let y : V → ℤ := fun v => max (p v - 1) (q v)
    let z : V → ℤ := fun v => min (p v) (y v)
    distMeasure z q < distMeasure p q := by
  intro y z
  unfold distMeasure
  apply Finset.sum_lt_sum
  · intro v _
    dsimp [y, z]
    omega
  · refine ⟨v₀, Finset.mem_univ v₀, ?_⟩
    dsimp [y, z]
    omega

private lemma submod_one_sided (g : (V → ℤ) → WithTop ℝ) (hdom : LNatConvexSet (DomZ g))
    (hloc : ∀ p q : V → ℤ, (∀ v, |p v - q v| ≤ 1) →
      g p + g q ≥ g (fun v => max (p v) (q v)) + g (fun v => min (p v) (q v))) :
    ∀ (n : ℕ) (p q : V → ℤ), distMeasure p q ≤ n → (∀ v, q v - p v ≤ 1) →
      g p + g q ≥ g (fun v => max (p v) (q v)) + g (fun v => min (p v) (q v)) := by
  intro n
  induction n with
  | zero =>
    intro p q hdist _
    have hle : ∀ v, p v ≤ q v := by
      intro v
      have h0 : ∑ u : V, (p u - min (p u) (q u)).natAbs = 0 := Nat.eq_zero_of_le_zero hdist
      have hv : (p v - min (p v) (q v)).natAbs = 0 :=
        Finset.sum_eq_zero_iff.mp h0 v (Finset.mem_univ v)
      omega
    have hmax : (fun v => max (p v) (q v)) = q := by ext v; have := hle v; omega
    have hmin : (fun v => min (p v) (q v)) = p := by ext v; have := hle v; omega
    rw [hmax, hmin, add_comm]
  | succ n ih =>
    intro p q hdist hqp
    by_cases hp : g p = ⊤
    · simp [hp]
    by_cases hq : g q = ⊤
    · simp [hq]
    by_cases hle : ∀ v, p v ≤ q v
    · have hmax : (fun v => max (p v) (q v)) = q := by ext v; have := hle v; omega
      have hmin : (fun v => min (p v) (q v)) = p := by ext v; have := hle v; omega
      rw [hmax, hmin, add_comm]
    · push_neg at hle
      rcases hle with ⟨v₀, hv₀⟩
      let y : V → ℤ := fun v => max (p v - 1) (q v)
      let z : V → ℤ := fun v => min (p v) (y v)
      have hy_dom : y ∈ DomZ g := dom_max_sub_one hdom hp hq
      have hz_dom : z ∈ DomZ g := dom_min hdom hp hy_dom
      have hpy_loc : ∀ v, |p v - y v| ≤ 1 := by
        intro v
        have := hqp v
        dsimp [y]
        rw [abs_le]
        constructor <;> omega
      have hzq_step : ∀ v, q v - z v ≤ 1 := by
        intro v
        have := hqp v
        dsimp [y, z]
        omega
      have hlt : distMeasure z q < distMeasure p q := distMeasure_lt hv₀
      have hdist_z : distMeasure z q ≤ n := by omega
      have h1 := hloc p y hpy_loc
      have hmax_py : (fun v => max (p v) (y v)) = (fun v => max (p v) (q v)) := by
        ext v; dsimp [y]; omega
      have hmin_py : (fun v => min (p v) (y v)) = z := rfl
      rw [hmax_py, hmin_py] at h1
      have h2 := ih z q hdist_z hzq_step
      have hmax_zq : (fun v => max (z v) (q v)) = y := by
        ext v; dsimp [y, z]; omega
      have hmin_zq : (fun v => min (z v) (q v)) = (fun v => min (p v) (q v)) := by
        ext v; dsimp [y, z]; omega
      rw [hmax_zq, hmin_zq] at h2
      exact withtop_chain hy_dom hz_dom h1 h2

private lemma submod_general (g : (V → ℤ) → WithTop ℝ) (hdom : LNatConvexSet (DomZ g))
    (hloc : ∀ p q : V → ℤ, (∀ v, |p v - q v| ≤ 1) →
      g p + g q ≥ g (fun v => max (p v) (q v)) + g (fun v => min (p v) (q v))) :
    ∀ (n : ℕ) (p q : V → ℤ), distMeasure p q ≤ n →
      g p + g q ≥ g (fun v => max (p v) (q v)) + g (fun v => min (p v) (q v)) := by
  intro n
  induction n with
  | zero =>
    intro p q hdist
    have hle : ∀ v, p v ≤ q v := by
      intro v
      have h0 : ∑ u : V, (p u - min (p u) (q u)).natAbs = 0 := Nat.eq_zero_of_le_zero hdist
      have hv : (p v - min (p v) (q v)).natAbs = 0 :=
        Finset.sum_eq_zero_iff.mp h0 v (Finset.mem_univ v)
      omega
    have hmax : (fun v => max (p v) (q v)) = q := by ext v; have := hle v; omega
    have hmin : (fun v => min (p v) (q v)) = p := by ext v; have := hle v; omega
    rw [hmax, hmin, add_comm]
  | succ n ih =>
    intro p q hdist
    by_cases hp : g p = ⊤
    · simp [hp]
    by_cases hq : g q = ⊤
    · simp [hq]
    by_cases hle : ∀ v, p v ≤ q v
    · have hmax : (fun v => max (p v) (q v)) = q := by ext v; have := hle v; omega
      have hmin : (fun v => min (p v) (q v)) = p := by ext v; have := hle v; omega
      rw [hmax, hmin, add_comm]
    · push_neg at hle
      rcases hle with ⟨v₀, hv₀⟩
      let y : V → ℤ := fun v => max (p v - 1) (q v)
      let z : V → ℤ := fun v => min (p v) (y v)
      have hy_dom : y ∈ DomZ g := dom_max_sub_one hdom hp hq
      have hz_dom : z ∈ DomZ g := dom_min hdom hp hy_dom
      have hyp_step : ∀ v, p v - y v ≤ 1 := by
        intro v
        dsimp [y]
        omega
      have h1_sym := submod_one_sided g hdom hloc (distMeasure y p) y p le_rfl hyp_step
      have hmax_yp : (fun v => max (y v) (p v)) = (fun v => max (p v) (q v)) := by
        ext v; dsimp [y]; omega
      have hmin_yp : (fun v => min (y v) (p v)) = z := by
        ext v; dsimp [y, z]; omega
      rw [hmax_yp, hmin_yp, add_comm (g y) (g p)] at h1_sym
      have hlt : distMeasure z q < distMeasure p q := distMeasure_lt hv₀
      have hdist_z : distMeasure z q ≤ n := by omega
      have h2 := ih z q hdist_z
      have hmax_zq : (fun v => max (z v) (q v)) = y := by
        ext v; dsimp [y, z]; omega
      have hmin_zq : (fun v => min (z v) (q v)) = (fun v => min (p v) (q v)) := by
        ext v; dsimp [y, z]; omega
      rw [hmax_zq, hmin_zq] at h2
      exact withtop_chain hy_dom hz_dom h1_sym h2

theorem solution (g : (V → ℤ) → WithTop ℝ) (hdom : LNatConvexSet (DomZ g)) :
    (∀ p q : V → ℤ, g p + g q ≥ g (fun v => max (p v) (q v)) + g (fun v => min (p v) (q v))) ↔
    (∀ p q : V → ℤ, (∀ v, |p v - q v| ≤ 1) →
      g p + g q ≥ g (fun v => max (p v) (q v)) + g (fun v => min (p v) (q v))) := by
  constructor
  · intro h p q _
    exact h p q
  · intro hloc p q
    exact submod_general g hdom hloc (distMeasure p q) p q le_rfl
