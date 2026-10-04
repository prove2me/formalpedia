-- Prove2me | solution 1 for BJNAdAuctions.Basic.x_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:08:41.027055+00:00
-- url     : https://prove2.me/submissions/12f8ed8d-12a8-491f-9242-d7f4f29e1d99

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

set_option autoImplicit false

namespace XLB_ec205554

open BJNAdAuctions.Basic

lemma key_ineq (R t : ℝ) (hR : 0 < R) (ht0 : 0 ≤ t) (htR : t ≤ R) :
    ((1 + R) ^ (1 / R)) ^ t ≤ 1 + t := by
  rw [← Real.rpow_mul (by linarith)]
  have hp2 : 1 / R * t ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hR]; exact htR
  have h := rpow_one_add_le_one_add_mul_self (s := R) (p := 1 / R * t)
    (by linarith) (by positivity) hp2
  calc _ ≤ 1 + 1 / R * t * R := h
    _ = 1 + t := by field_simp

lemma alg_ineq (u A E X t : ℝ) (hu : 0 ≤ u) (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hE : E ≤ 1 + t) (hx : u * (A - 1) ≤ X) :
    u * (A * E - 1) ≤ X * (1 + t) + u * t := by
  have h1 : u * (A - 1) * (1 + t) ≤ X * (1 + t) := mul_le_mul_of_nonneg_right hx (by linarith)
  have h2 : u * A * E ≤ u * A * (1 + t) := mul_le_mul_of_nonneg_left hE (mul_nonneg hu hA)
  nlinarith

theorem inv_all {I : Type*} [Fintype I] {m : ℕ} (inst : Instance I m)
    (R : ℝ) (hR : 0 < R) (hbR : ∀ i j, inst.b i j ≤ R * inst.B i)
    (sel : (I → ℝ) → Fin m → I) (k : ℕ) :
    (∀ i j, 0 ≤ (runPrefix inst ((1 + R) ^ (1 / R)) sel k).y i j) ∧
    ∀ i, 1 / ((1 + R) ^ (1 / R) - 1) *
        (((1 + R) ^ (1 / R)) ^ ((∑ j, inst.b i j * (runPrefix inst ((1 + R) ^ (1 / R)) sel k).y i j)
          / inst.B i) - 1)
      ≤ (runPrefix inst ((1 + R) ^ (1 / R)) sel k).x i := by
  set c := (1 + R) ^ (1 / R) with hc
  have hc1 : 1 < c := Real.one_lt_rpow (by linarith) (by positivity)
  have hc0 : 0 < c := by linarith
  induction k with
  | zero =>
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · simp [runPrefix, State.init]
    · simp [runPrefix, State.init]
  | succ k ih =>
    obtain ⟨hy, hx⟩ := ih
    rw [runPrefix]
    split_ifs with hkm
    · set s := runPrefix inst c sel k with hs
      set j0 : Fin m := ⟨k, hkm⟩ with hj0
      unfold step
      simp only
      split_ifs with h1
      · exact ⟨hy, hx⟩
      · set i0 := sel s.x j0 with hi0
        refine ⟨fun i j => ?_, fun i => ?_⟩
        · simp only [Function.update_apply]
          split_ifs with h2
          · subst h2
            by_cases hj : j = j0
            · subst hj; simp
            · simp [Function.update_apply, hj, hy]
          · exact hy i j
        · by_cases hi : i = i0
          · subst hi
            simp only [Function.update_self]
            set i := sel s.x j0
            set S := ∑ j, inst.b i j * s.y i j with hS
            set b := inst.b i j0
            set B := inst.B i
            have hB : 0 < B := inst.B_pos i
            have hb0 : 0 ≤ b := inst.b_nonneg i j0
            have hbB : b ≤ R * B := hbR i j0
            -- new sum ≤ S + b
            have hsum : (∑ j, inst.b i j * Function.update (s.y i) j0 1 j) ≤ S + b := by
              have hterm : ∀ j, inst.b i j * Function.update (s.y i) j0 1 j ≤
                  inst.b i j * s.y i j + (if j = j0 then b else 0) := by
                intro j
                by_cases hj : j = j0
                · subst hj
                  simp only [Function.update_self, if_true, mul_one]
                  have := mul_nonneg (inst.b_nonneg i j0) (hy i j0)
                  linarith
                · simp [hj]
              calc _ ≤ ∑ j, (inst.b i j * s.y i j + (if j = j0 then b else 0)) :=
                    Finset.sum_le_sum (fun j _ => hterm j)
                _ = S + b := by
                    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
                    simp [hS]
            have hmono : c ^ ((∑ j, inst.b i j * Function.update (s.y i) j0 1 j) / B)
                ≤ c ^ ((S + b) / B) :=
              Real.rpow_le_rpow_of_exponent_le hc1.le
                (div_le_div_of_nonneg_right hsum hB.le)
            have hsplit : c ^ ((S + b) / B) = c ^ (S / B) * c ^ (b / B) := by
              rw [add_div, Real.rpow_add hc0]
            have hE : c ^ (b / B) ≤ 1 + b / B := by
              apply key_ineq R (b / B) hR (div_nonneg hb0 hB.le)
              rw [div_le_iff₀ hB]; linarith
            have hu : 0 ≤ 1 / (c - 1) := by
              have : 0 < c - 1 := by linarith
              positivity
            have hA : 0 ≤ c ^ (S / B) := Real.rpow_nonneg hc0.le _
            have key := alg_ineq (1 / (c - 1)) (c ^ (S / B)) (c ^ (b / B)) (s.x i) (b / B)
              hu hA (div_nonneg hb0 hB.le) hE (hx i)
            have hlast : b / ((c - 1) * B) = 1 / (c - 1) * (b / B) := by
              have : c - 1 ≠ 0 := by linarith
              field_simp
            rw [hlast]
            calc 1 / (c - 1) * (c ^ ((∑ j, inst.b i j * Function.update (s.y i) j0 1 j) / B) - 1)
                ≤ 1 / (c - 1) * (c ^ ((S + b) / B) - 1) := by
                  apply mul_le_mul_of_nonneg_left _ hu; linarith
              _ = 1 / (c - 1) * (c ^ (S / B) * c ^ (b / B) - 1) := by rw [hsplit]
              _ ≤ _ := key
          · simp only [Function.update_apply, if_neg hi]
            exact hx i
    · exact ⟨hy, hx⟩

end XLB_ec205554

open BJNAdAuctions.Basic in
theorem solution {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : Instance I m)
    (R : ℝ) (hR : 0 < R) (hbR : ∀ i j, inst.b i j ≤ R * inst.B i)
    (sel : (I → ℝ) → Fin m → I) (k : ℕ) (hk : k ≤ m) (i : I) :
    1 / ((1 + R) ^ (1 / R) - 1) *
        (((1 + R) ^ (1 / R)) ^ ((∑ j, inst.b i j * (runPrefix inst ((1 + R) ^ (1 / R)) sel k).y i j)
          / inst.B i) - 1)
      ≤ (runPrefix inst ((1 + R) ^ (1 / R)) sel k).x i := by
  exact (XLB_ec205554.inv_all inst R hR hbR sel k).2 i
