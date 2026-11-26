-- Prove2me | solution 1 for Erdos287.grouped_moment_barrier_for_commuting_projections
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:25:00.532142+00:00
-- url     : https://prove2.me/submissions/d0b6f754-952b-445c-b06a-3f327945cb8c

import Mathlib

open Finset
open scoped RealInnerProductSpace

set_option autoImplicit false

private theorem projection_moment_bound {ι E : Type*} [DecidableEq ι] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Finset ι) (P : ι → E → E) (f : E)
    (hself : ∀ i x y, ⟪P i x, y⟫ = ⟪x, P i y⟫)
    (hidem : ∀ i x, P i (P i x) = P i x)
    (hcomm : ∀ i j x, P i (P j x) = P j (P i x)) (a : ℝ) :
    let J := a * ∑ i ∈ S, ‖P i f‖ ^ 2
    let K := a ^ 2 * ∑ i ∈ S, ∑ j ∈ S.filter (fun j => j ≠ i), ‖P i (P j f)‖ ^ 2
    J ^ 2 ≤ ‖f‖ ^ 2 * (a * J + K) := by
  classical
  dsimp only
  have hproject (i : ι) (x y : E) : ⟪P i x, P i y⟫ = ⟪x, P i y⟫ := by
    rw [hself, hidem]
  have hcross (i j : ι) : ⟪P i f, P j f⟫ = ‖P i (P j f)‖ ^ 2 := by
    symm
    calc
      ‖P i (P j f)‖ ^ 2 = ⟪P i (P j f), P i (P j f)⟫ :=
        (real_inner_self_eq_norm_sq _).symm
      _ = ⟪P j f, P i (P j f)⟫ := hproject i _ _
      _ = ⟪P j f, P j (P i f)⟫ := by rw [hcomm i j f]
      _ = ⟪f, P j (P i f)⟫ := hproject j _ _
      _ = ⟪f, P i (P j f)⟫ := by rw [hcomm i j f]
      _ = ⟪P i f, P j f⟫ := (hself i _ _).symm
  let v := ∑ i ∈ S, P i f
  let B := ∑ i ∈ S, ‖P i f‖ ^ 2
  let C := ∑ i ∈ S, ∑ j ∈ S.filter (fun j => j ≠ i), ‖P i (P j f)‖ ^ 2
  have hv : ⟪f, v⟫ = B := by
    dsimp only [v, B]
    rw [inner_sum]
    exact sum_congr rfl fun i _ => (hproject i f f).symm.trans (real_inner_self_eq_norm_sq _)
  have hvv : ‖v‖ ^ 2 = B + C := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp only [v, B, C]
    simp only [sum_inner, inner_sum, hcross]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hdiag :
        (∑ j ∈ S.filter (fun j => j ≠ i), ‖P i (P j f)‖ ^ 2) +
          ‖P i (P i f)‖ ^ 2 = ∑ j ∈ S, ‖P i (P j f)‖ ^ 2 := by
      have hfilter : S.filter (fun j => j ≠ i) = S.erase i := by ext j; simp [and_comm]
      simpa only [hfilter] using sum_erase_add S (fun j => ‖P i (P j f)‖ ^ 2) hi
    rw [hidem, add_comm] at hdiag
    calc
      (∑ j ∈ S, ‖P j (P i f)‖ ^ 2) = ∑ j ∈ S, ‖P i (P j f)‖ ^ 2 :=
        sum_congr rfl fun j _ => by rw [hcomm j i f]
      _ = _ := hdiag.symm
  have hcs := real_inner_le_norm f v
  rw [hv] at hcs
  have hB : 0 ≤ B := sum_nonneg (fun _ _ => sq_nonneg _)
  have hsquare : B ^ 2 ≤ ‖f‖ ^ 2 * (B + C) := by
    have h := mul_le_mul hcs hcs hB (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [← hvv]
    nlinarith only [h]
  change (a * B) ^ 2 ≤ ‖f‖ ^ 2 * (a * (a * B) + a ^ 2 * C)
  calc
    (a * B) ^ 2 = a ^ 2 * B ^ 2 := by ring
    _ ≤ a ^ 2 * (‖f‖ ^ 2 * (B + C)) := mul_le_mul_of_nonneg_left hsquare (sq_nonneg a)
    _ = _ := by ring

/-- The support length bounds the improvement available from redistributing
coordinate-average moments among groups. The double sum counts ordered pairs. -/
theorem solution {ι κ E : Type*} [DecidableEq ι] [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Finset κ) (S : κ → Finset ι) (P : ι → E → E) (f : E)
    (hself : ∀ i x y, inner ℝ (P i x) y = inner ℝ x (P i y))
    (hidem : ∀ i x, P i (P i x) = P i x)
    (hcomm : ∀ i j x, P i (P j x) = P j (P i x))
    (a A r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (hrA : r ≤ A) (hsize : r * a ≤ 1) :
    let J (g : κ) := a * ∑ i ∈ S g, ‖P i f‖ ^ 2
    let K (g : κ) := a ^ 2 * ∑ i ∈ S g, ∑ j ∈ (S g).filter (fun j => j ≠ i),
      ‖P i (P j f)‖ ^ 2
    r * (∑ g ∈ G, J g) ^ 2 ≤
      (G.card : ℝ) * ‖f‖ ^ 2 * ∑ g ∈ G, (J g + A * K g) := by
  classical
  intro J K
  have hlocal (g : κ) : r * (J g) ^ 2 ≤ ‖f‖ ^ 2 * (J g + A * K g) := by
    have hmom : (J g) ^ 2 ≤ ‖f‖ ^ 2 * (a * J g + K g) :=
      projection_moment_bound (S g) P f hself hidem hcomm a
    have hJ : 0 ≤ J g := mul_nonneg ha (sum_nonneg (fun _ _ => sq_nonneg _))
    have hK : 0 ≤ K g := mul_nonneg (sq_nonneg _)
      (sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _)
    calc
      r * (J g) ^ 2 ≤ r * (‖f‖ ^ 2 * (a * J g + K g)) :=
        mul_le_mul_of_nonneg_left hmom hr
      _ = ‖f‖ ^ 2 * ((r * a) * J g + r * K g) := by ring
      _ ≤ ‖f‖ ^ 2 * (J g + A * K g) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        have hleft : (r * a) * J g ≤ J g := by
          simpa using mul_le_mul_of_nonneg_right hsize hJ
        exact add_le_add hleft (mul_le_mul_of_nonneg_right hrA hK)
  have hsum : r * (∑ g ∈ G, (J g) ^ 2) ≤
      ‖f‖ ^ 2 * ∑ g ∈ G, (J g + A * K g) := by
    rw [mul_sum, mul_sum]
    exact sum_le_sum fun g _ => hlocal g
  have hcs : (∑ g ∈ G, J g) ^ 2 ≤ (G.card : ℝ) * ∑ g ∈ G, (J g) ^ 2 := by
    simpa using sum_mul_sq_le_sq_mul_sq G (fun _ => (1 : ℝ)) J
  calc
    r * (∑ g ∈ G, J g) ^ 2 ≤ r * ((G.card : ℝ) * ∑ g ∈ G, (J g) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs hr
    _ = (G.card : ℝ) * (r * ∑ g ∈ G, (J g) ^ 2) := by ring
    _ ≤ (G.card : ℝ) * (‖f‖ ^ 2 * ∑ g ∈ G, (J g + A * K g)) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = _ := by ring

