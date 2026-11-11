-- Prove2me | solution 1 for DetConnSketch.Main.fact_7_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:26:24.511742+00:00
-- url     : https://prove2.me/submissions/4a815656-99a6-4aca-b259-6c153616405d

import Mathlib

/-- Fact 7.3 (Lovász): let `H` be a graph on `N` vertices and `M` a real positive semidefinite
`N × N` matrix with `M_xx = 1` for every `x` and `M_xy = 0` whenever `x ≠ y` and `xy` is not an
edge of `H`. Then `χ(H) ≥ 1ᵀ M 1 / N`: every proper colouring of `H` with `c` colours has
`1ᵀ M 1 / N ≤ c`. -/
theorem solution {V : Type} [Fintype V] (H : SimpleGraph V) (M : Matrix V V ℝ)
    (hpsd : M.PosSemidef) (hdiag : ∀ x, M x x = 1)
    (hsupp : ∀ x y, x ≠ y → ¬ H.Adj x y → M x y = 0) :
    ∀ c : ℕ, H.Colorable c → (∑ x, ∑ y, M x y) / (Fintype.card V : ℝ) ≤ c := by
  intro c ⟨col⟩
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact (col (Classical.arbitrary V)).elim0
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  set t : ℝ := 1 / c with ht
  have h1 : (c : ℝ) * t = 1 := by rw [ht]; field_simp
  have key : ∀ x y, ∑ i : Fin c, ((if col x = i then (1:ℝ) else 0) - t) *
      ((if col y = i then (1:ℝ) else 0) - t) = (if col x = col y then 1 else 0) - t := by
    intro x y
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h2 : (c : ℝ) * (t * t) = t := by rw [← mul_assoc, h1, one_mul]
    linarith
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin c))) (fun i _ =>
    hpsd.dotProduct_mulVec_nonneg (fun x => (if col x = i then (1:ℝ) else 0) - t))
  have e : ∑ i : Fin c, dotProduct (star (fun x => (if col x = i then (1:ℝ) else 0) - t))
      (Matrix.mulVec M (fun x => (if col x = i then (1:ℝ) else 0) - t)) =
      ∑ x, ∑ y, M x y * ((if col x = col y then (1:ℝ) else 0) - t) := by
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← key x y, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [e] at h
  have e2 : ∑ x, ∑ y, M x y * ((if col x = col y then (1:ℝ) else 0) - t) =
      (Fintype.card V : ℝ) - t * ∑ x, ∑ y, M x y := by
    have e3 : ∀ x, ∑ y, M x y * (if col x = col y then (1:ℝ) else 0) = 1 := by
      intro x
      rw [Finset.sum_eq_single x]
      · simp [hdiag]
      · intro y _ hyx
        by_cases hc : col x = col y
        · have : ¬ H.Adj x y := fun hadj => col.valid hadj hc
          rw [hsupp x y (Ne.symm hyx) this]; simp
        · simp [hc]
      · simp
    simp only [mul_sub, Finset.sum_sub_distrib, e3, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
  rw [e2] at h
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hN]
  have h3 : t * ∑ x, ∑ y, M x y ≤ Fintype.card V := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hcR.le
  rw [← mul_assoc, h1, one_mul] at h4
  linarith
