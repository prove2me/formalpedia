-- Prove2me | solution 1 for DynAssortPers.TypeDist.display_p44_rademacher
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:14:46.404367+00:00
-- url     : https://prove2.me/submissions/de64c8d4-d7ac-40a6-b614-e11074ecfd43

import Mathlib
import Definitions.Def_DynAssortPers_TypeDist_IIDSampling
import Definitions.Def_DynAssortPers_TypeDist_Estimator

set_option autoImplicit false

open Finset DynAssortPers.TypeDist

namespace DynAssortPers.TypeDist.RadProof

theorem sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> norm_num [sgn]

theorem ortho_signs {N : ℕ} (s t : Fin N) (hst : s ≠ t) :
    ∑ ε : Fin N → Bool, sgn (ε s) * sgn (ε t) = 0 := by
  let φ : (Fin N → Bool) ≃ (Fin N → Bool) :=
    { toFun := fun ε => Function.update ε s (!ε s)
      invFun := fun ε => Function.update ε s (!ε s)
      left_inv := fun ε => by
        ext u; by_cases h : u = s <;> simp [h]
      right_inv := fun ε => by
        ext u; by_cases h : u = s <;> simp [h] }
  have hswap : ∑ ε : Fin N → Bool, sgn (ε s) * sgn (ε t) =
      ∑ ε : Fin N → Bool, sgn ((φ ε) s) * sgn ((φ ε) t) :=
    (Equiv.sum_comp φ (fun ε => sgn (ε s) * sgn (ε t))).symm
  have hneg : ∑ ε : Fin N → Bool, sgn ((φ ε) s) * sgn ((φ ε) t) =
      -∑ ε : Fin N → Bool, sgn (ε s) * sgn (ε t) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ε _
    simp only [φ, Equiv.coe_fn_mk, Function.update_self, Function.update_of_ne hst.symm,
      sgn_not, neg_mul]
  linarith

end DynAssortPers.TypeDist.RadProof

open DynAssortPers.TypeDist.RadProof in
theorem solution {m N : ℕ} (hN : 0 < N) (x : Fin N → Fin m) :
    radHat x = (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool,
        ∑ i : Fin m, |(1 / N : ℝ) * ∑ t, sgn (ε t) * (if x t = i then 1 else 0)| ∧
    (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool,
        ∑ i : Fin m, |(1 / N : ℝ) * ∑ t, sgn (ε t) * (if x t = i then 1 else 0)|
      = (1 / N : ℝ) * ∑ i : Fin m, (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool,
        |∑ t, (if x t = i then 1 else 0) * sgn (ε t)| ∧
    (1 / N : ℝ) * ∑ i : Fin m, (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool,
        |∑ t, (if x t = i then 1 else 0) * sgn (ε t)|
      ≤ (1 / N : ℝ) * ∑ i : Fin m, Real.sqrt (N * muHat x i) ∧
    (1 / N : ℝ) * ∑ i : Fin m, Real.sqrt (N * muHat x i)
      = (1 / Real.sqrt N) * ∑ i : Fin m, Real.sqrt (muHat x i) ∧
    (1 / Real.sqrt N) * ∑ i : Fin m, Real.sqrt (muHat x i) ≤ Real.sqrt (m / N) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1. Exact supremum over the L∞ unit ball
    unfold radHat
    congr 1
    apply Finset.sum_congr rfl
    intro ε _
    let c : Fin m → ℝ := fun i => (1 / N : ℝ) * ∑ t, sgn (ε t) * (if x t = i then 1 else 0)
    have hrew : ∀ v : Fin m → ℝ,
        (1 / N : ℝ) * ∑ t, sgn (ε t) * v (x t) = ∑ i : Fin m, v i * c i := by
      intro v
      simp only [c]
      have hvx : ∀ t : Fin N, v (x t) = ∑ i : Fin m, v i * (if x t = i then 1 else 0) := by
        intro t; simp
      simp_rw [hvx, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => by ring
    let S := {v : Fin m → ℝ // ∀ i, |v i| ≤ 1}
    have _ : Nonempty S := ⟨⟨fun _ => 0, fun _ => by norm_num⟩⟩
    have hupper : ∀ v : S, (1 / N : ℝ) * ∑ t, sgn (ε t) * v.1 (x t) ≤ ∑ i : Fin m, |c i| := by
      intro v
      rw [hrew v.1]
      apply Finset.sum_le_sum
      intro i _
      have h1 : v.1 i * c i ≤ |v.1 i| * |c i| := by rw [← abs_mul]; exact le_abs_self _
      have h2 : |v.1 i| * |c i| ≤ 1 * |c i| :=
        mul_le_mul_of_nonneg_right (v.2 i) (abs_nonneg _)
      linarith
    have hbdd : BddAbove (Set.range fun v : S => (1 / N : ℝ) * ∑ t, sgn (ε t) * v.1 (x t)) :=
      ⟨∑ i, |c i|, by rintro _ ⟨v, rfl⟩; exact hupper v⟩
    let vstar : S := ⟨fun i => if 0 ≤ c i then 1 else -1,
      fun i => by dsimp only; split_ifs <;> norm_num⟩
    have hatt : (1 / N : ℝ) * ∑ t, sgn (ε t) * vstar.1 (x t) = ∑ i : Fin m, |c i| := by
      rw [hrew vstar.1]
      apply Finset.sum_congr rfl
      intro i _
      simp only [vstar]
      split_ifs with hci
      · rw [abs_of_nonneg hci, one_mul]
      · rw [abs_of_neg (lt_of_not_ge hci)]; ring
    exact le_antisymm (ciSup_le hupper) (hatt ▸ le_ciSup hbdd vstar)
  · -- 2. Factor 1/N and exchange finite sums
    have habs : ∀ (ε : Fin N → Bool) (i : Fin m),
        |(1 / N : ℝ) * ∑ t, sgn (ε t) * (if x t = i then 1 else 0)| =
          (1 / N : ℝ) * |∑ t, (if x t = i then 1 else 0) * sgn (ε t)| := by
      intro ε i
      rw [abs_mul, abs_of_pos (by positivity)]
      congr 2
      exact Finset.sum_congr rfl fun t _ => mul_comm _ _
    simp_rw [habs, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    ring
  · -- 3. Khintchine / second-moment bound via Cauchy-Schwarz and sign orthogonality
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    let a : Fin N → ℝ := fun t => if x t = i then 1 else 0
    let Z : (Fin N → Bool) → ℝ := fun ε => ∑ t, a t * sgn (ε t)
    change (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool, |Z ε| ≤ Real.sqrt (N * muHat x i)
    have hcs : (∑ ε : Fin N → Bool, (1 : ℝ) * |Z ε|) ^ 2 ≤
        (∑ ε : Fin N → Bool, (1 : ℝ) ^ 2) * ∑ ε : Fin N → Bool, |Z ε| ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => 1) (fun ε => |Z ε|)
    have hcard : (∑ _ : Fin N → Bool, (1 : ℝ) ^ 2) = 2 ^ N := by simp
    simp only [one_mul, sq_abs] at hcs
    rw [hcard] at hcs
    have hZ2 : ∑ ε : Fin N → Bool, Z ε ^ 2 = (2 ^ N : ℝ) * ∑ s : Fin N, a s ^ 2 := by
      have hexp : ∀ ε : Fin N → Bool, Z ε ^ 2 =
          ∑ s : Fin N, ∑ t : Fin N, a s * a t * (sgn (ε s) * sgn (ε t)) := by
        intro ε
        simp only [Z, sq, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      simp_rw [hexp]
      rw [Finset.sum_comm]
      have h1 : ∑ s : Fin N, ∑ ε : Fin N → Bool,
            ∑ t : Fin N, a s * a t * (sgn (ε s) * sgn (ε t)) =
          ∑ s : Fin N, ∑ t : Fin N,
            a s * a t * ∑ ε : Fin N → Bool, sgn (ε s) * sgn (ε t) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [← Finset.mul_sum]
      rw [h1, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_eq_single s]
      · simp [sgn_sq, sq]
        ring
      · intro t _ hts
        rw [ortho_signs s t hts.symm, mul_zero]
      · intro hs; exact absurd (Finset.mem_univ s) hs
    have ha_sum : ∑ s : Fin N, a s ^ 2 = N * muHat x i := by
      unfold muHat
      have ha2 : ∀ s : Fin N, a s ^ 2 = if x s = i then (1 : ℝ) else 0 := by
        intro s; simp only [a]; split_ifs <;> norm_num
      simp_rw [ha2]
      rw [Finset.sum_boole, mul_div_cancel₀ _ hNR.ne']
    rw [hZ2, ha_sum] at hcs
    have hnonneg : 0 ≤ (1 / 2 ^ N : ℝ) * ∑ ε : Fin N → Bool, |Z ε| :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have hmu0 : 0 ≤ (N : ℝ) * muHat x i := by
      rw [← ha_sum]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine (Real.le_sqrt hnonneg hmu0).mpr ?_
    rw [mul_pow, one_div, inv_pow]
    have hmul_cs := mul_le_mul_of_nonneg_left hcs (show 0 ≤ ((2 ^ N : ℝ) ^ 2)⁻¹ by positivity)
    have hcancel : ((2 ^ N : ℝ) ^ 2)⁻¹ * ((2 ^ N : ℝ) * ((2 ^ N : ℝ) * (N * muHat x i))) =
        N * muHat x i := by field_simp
    linarith
  · -- 4. Pull out √N
    have hpull : ∀ i : Fin m,
        Real.sqrt (N * muHat x i) = Real.sqrt N * Real.sqrt (muHat x i) :=
      fun i => Real.sqrt_mul (Nat.cast_nonneg N) (muHat x i)
    simp_rw [hpull, ← Finset.mul_sum]
    have hsq_pos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNR
    have hcoeff : (1 / (N : ℝ)) * Real.sqrt N = 1 / Real.sqrt N := by
      rw [eq_div_iff hsq_pos.ne', mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg N),
        div_mul_cancel₀ 1 hNR.ne']
    rw [← mul_assoc, hcoeff]
  · -- 5. Second Cauchy-Schwarz using ∑_i muHat x i = 1
    have hmu_nonneg : ∀ i : Fin m, 0 ≤ muHat x i := by
      intro i; unfold muHat; positivity
    have hmu_sum : ∑ i : Fin m, muHat x i = 1 := by
      unfold muHat
      rw [← Finset.sum_div]
      have hcnt : (∑ i : Fin m, ((univ.filter (fun t => x t = i)).card : ℝ)) = N := by
        have h1 : ∀ i : Fin m, ((univ.filter (fun t => x t = i)).card : ℝ) =
            ∑ t : Fin N, if x t = i then (1 : ℝ) else 0 := by
          intro i; rw [Finset.sum_boole]
        simp_rw [h1]
        rw [Finset.sum_comm]
        simp
      rw [hcnt, div_self hNR.ne']
    have hcs2 : (∑ i : Fin m, (1 : ℝ) * Real.sqrt (muHat x i)) ^ 2 ≤
        (∑ i : Fin m, (1 : ℝ) ^ 2) * ∑ i : Fin m, (Real.sqrt (muHat x i)) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq univ (fun _ => 1) (fun i => Real.sqrt (muHat x i))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hcs2
    have hsq_mu : ∑ i : Fin m, (Real.sqrt (muHat x i)) ^ 2 = 1 := by
      rw [Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hmu_nonneg i)), hmu_sum]
    rw [hsq_mu, mul_one] at hcs2
    have hsum_le : ∑ i : Fin m, Real.sqrt (muHat x i) ≤ Real.sqrt m :=
      (Real.le_sqrt (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _) (Nat.cast_nonneg m)).mpr hcs2
    rw [Real.sqrt_div (Nat.cast_nonneg m) N]
    have := mul_le_mul_of_nonneg_left hsum_le (show 0 ≤ (1 / Real.sqrt N : ℝ) by positivity)
    linarith [show (1 / Real.sqrt N : ℝ) * Real.sqrt m = Real.sqrt m / Real.sqrt N by ring]
