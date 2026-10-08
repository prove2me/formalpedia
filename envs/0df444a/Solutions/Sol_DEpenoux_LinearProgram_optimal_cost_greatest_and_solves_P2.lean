-- Prove2me | solution 1 for DEpenoux.LinearProgram.optimal_cost_greatest_and_solves_P2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:03:30.491676+00:00
-- url     : https://prove2.me/submissions/471c9740-0a33-4a86-a1ed-8695505f0e26

import Mathlib
import Definitions.Def_DEpenoux_LinearProgram_Model

set_option autoImplicit false

namespace DEpenoux44319b0f

open DEpenoux.LinearProgram

/-- If `f ≤ g + r` pointwise on `s`, then `inf' f ≤ inf' g + r`. -/
theorem inf'_le_inf'_add {ι : Type} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) (r : ℝ)
    (h : ∀ j ∈ s, f j ≤ g j + r) : s.inf' hs f ≤ s.inf' hs g + r := by
  obtain ⟨j, hj, hjg⟩ := Finset.exists_mem_eq_inf' hs g
  rw [hjg]
  exact le_trans (Finset.inf'_le f hj) (h j hj)

theorem bellman_apply (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) (lam : ℝ)
    (u : Fin (σ + 1) → ℝ) (i : Fin (σ + 1)) :
    BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam u i =
      (admissible σ i).inf' ((model σ p d hp0 hp1).hU i)
        (fun j => d i j + lam * ∑ s, p j s * u s) := rfl

theorem mem_admissible (σ : ℕ) (i j : Fin (σ + 1)) : j ∈ admissible σ i ↔ i ≤ j := by
  simp [admissible]

/-- weighted average bound -/
theorem wsum_le (σ : ℕ) (p : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) (j : Fin (σ + 1))
    (w : Fin (σ + 1) → ℝ) (m : ℝ) (hw : ∀ s, w s ≤ m) : ∑ s, p j s * w s ≤ m := by
  calc ∑ s, p j s * w s ≤ ∑ s, p j s * m :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hw s) (hp0 j s)
    _ = m := by rw [← Finset.sum_mul, hp1 j, one_mul]

theorem bellman_lipschitz (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) (lam : ℝ) (hlam0 : 0 ≤ lam)
    (u v : Fin (σ + 1) → ℝ) (i : Fin (σ + 1)) :
    BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam u i ≤
      BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam v i + lam * dist u v := by
  rw [bellman_apply, bellman_apply]
  apply inf'_le_inf'_add
  intro j _
  have h1 : ∑ s, p j s * u s - ∑ s, p j s * v s ≤ dist u v := by
    rw [← Finset.sum_sub_distrib]
    have : ∑ s, (p j s * u s - p j s * v s) = ∑ s, p j s * (u s - v s) := by
      refine Finset.sum_congr rfl fun s _ => by ring
    rw [this]
    apply wsum_le σ p hp0 hp1 j
    intro s
    have h2 : dist (u s) (v s) ≤ dist u v := dist_le_pi_dist u v s
    rw [Real.dist_eq] at h2
    exact le_trans (le_abs_self _) h2
  nlinarith [mul_le_mul_of_nonneg_left h1 hlam0]

theorem bellman_fixed_exists (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∃ u : Fin (σ + 1) → ℝ, BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam u = u := by
  set T := BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam with hT
  let K : NNReal := ⟨lam, hlam0.le⟩
  have hK : K < 1 := NNReal.coe_lt_coe.mp (show (K : ℝ) < ((1 : NNReal) : ℝ) by
    rw [NNReal.coe_one]; exact hlam1)
  have hL : LipschitzWith K T := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hnn : 0 ≤ (K : ℝ) * dist u v := mul_nonneg hlam0.le dist_nonneg
    rw [dist_pi_le_iff hnn]
    intro i
    rw [Real.dist_eq, abs_le]
    have a := bellman_lipschitz σ p d hp0 hp1 lam hlam0.le u v i
    have b := bellman_lipschitz σ p d hp0 hp1 lam hlam0.le v u i
    rw [dist_comm] at b
    show -(lam * dist u v) ≤ T u i - T v i ∧ T u i - T v i ≤ lam * dist u v
    constructor <;> linarith
  have hC : ContractingWith K T := ⟨hK, hL⟩
  obtain ⟨x, hx, -⟩ := hC.exists_fixedPoint (x := (0 : Fin (σ + 1) → ℝ))
    (edist_ne_top _ _)
  exact ⟨x, hx⟩

theorem fixed_mem_A (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) (lam : ℝ)
    (uStar : Fin (σ + 1) → ℝ)
    (h : BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam uStar = uStar) :
    uStar ∈ setA p d lam := by
  intro i j hij
  have := congrFun h i
  rw [bellman_apply] at this
  have hle : (admissible σ i).inf' ((model σ p d hp0 hp1).hU i)
      (fun j => d i j + lam * ∑ s, p j s * uStar s) ≤ d i j + lam * ∑ s, p j s * uStar s :=
    Finset.inf'_le (fun j => d i j + lam * ∑ s, p j s * uStar s)
      ((mem_admissible σ i j).2 hij)
  rw [this] at hle
  unfold Uij
  linarith

theorem A_le_fixed (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1) (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (uStar : Fin (σ + 1) → ℝ)
    (h : BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam uStar = uStar)
    (u : Fin (σ + 1) → ℝ) (hu : u ∈ setA p d lam) : u ≤ uStar := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => u i - uStar i)
    Finset.univ_nonempty
  set m := u i0 - uStar i0 with hm
  have hall : ∀ s, u s - uStar s ≤ m := fun s => hi0 s (Finset.mem_univ s)
  have hfix := congrFun h i0
  rw [bellman_apply] at hfix
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (s := admissible σ i0)
    ((model σ p d hp0 hp1).hU i0)
    (fun j => d i0 j + lam * ∑ s, p j s * uStar s)
  rw [hjeq] at hfix
  have hij : i0 ≤ j := (mem_admissible σ i0 j).1 hj
  have hA := hu i0 j hij
  unfold Uij at hA
  have hw := wsum_le σ p hp0 hp1 j (fun s => u s - uStar s) m hall
  have hsplit : ∑ s, p j s * (u s - uStar s) = ∑ s, p j s * u s - ∑ s, p j s * uStar s := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsplit] at hw
  have key : m ≤ lam * m := by
    have := mul_le_mul_of_nonneg_left hw hlam0.le
    nlinarith
  have hm0 : m ≤ 0 := by nlinarith
  intro s
  have := hall s
  linarith

end DEpenoux44319b0f

open DEpenoux44319b0f in
open DEpenoux.LinearProgram in
theorem solution (σ : ℕ) (p d : Fin (σ + 1) → Fin (σ + 1) → ℝ)
    (hp0 : ∀ j s, 0 ≤ p j s) (hp1 : ∀ j, ∑ s, p j s = 1)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    (∃ u : Fin (σ + 1) → ℝ, BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam u = u) ∧
    ∀ uStar : Fin (σ + 1) → ℝ,
      BertsekasDiscountedBellmanOp (model σ p d hp0 hp1) lam uStar = uStar →
        IsGreatest (setA p d lam) uStar ∧
        ∀ c : Fin (σ + 1) → ℝ, (∀ i, 0 < c i) → ∑ i, c i = 1 →
          IsP2Optimal p d lam c uStar ∧
          ∀ v : Fin (σ + 1) → ℝ, IsP2Optimal p d lam c v → v = uStar := by
  refine ⟨bellman_fixed_exists σ p d hp0 hp1 lam hlam0 hlam1, ?_⟩
  intro uStar h
  have hmem := fixed_mem_A σ p d hp0 hp1 lam uStar h
  have hle : ∀ v ∈ setA p d lam, v ≤ uStar :=
    fun v hv => A_le_fixed σ p d hp0 hp1 lam hlam0 hlam1 uStar h v hv
  have h1 : 0 < 1 - lam := by linarith
  refine ⟨⟨hmem, fun v hv => hle v hv⟩, ?_⟩
  intro c hc _
  have hopt : IsP2Optimal p d lam c uStar := by
    refine ⟨hmem, fun v hv => ?_⟩
    apply mul_le_mul_of_nonneg_left _ h1.le
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle v hv i) (hc i).le
  refine ⟨hopt, fun v hv => ?_⟩
  have hvle := hle v hv.1
  have hge := hv.2 uStar hmem
  have hge' : ∑ i, c i * uStar i ≤ ∑ i, c i * v i := le_of_mul_le_mul_left hge h1
  have hzero : ∑ i, c i * (uStar i - v i) = 0 := by
    apply le_antisymm
    · have : ∑ i, c i * (uStar i - v i) = ∑ i, c i * uStar i - ∑ i, c i * v i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]; linarith
    · exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (sub_nonneg.2 (hvle i))
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hc i).le (sub_nonneg.2 (hvle i)))] at hzero
  funext i
  have := hzero i (Finset.mem_univ i)
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 (hc i).ne'
  · linarith
