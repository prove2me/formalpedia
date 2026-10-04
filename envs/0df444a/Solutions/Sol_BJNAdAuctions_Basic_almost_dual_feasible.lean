-- Prove2me | solution 1 for BJNAdAuctions.Basic.almost_dual_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:21:17.719899+00:00
-- url     : https://prove2.me/submissions/e675ff89-46f1-4960-85b0-1540ed7c484e

import Mathlib
import Definitions.Def_BJNAdAuctions_Basic_Instance
import Definitions.Def_BJNAdAuctions_Basic_AllocationAlgorithm

set_option autoImplicit false

namespace ADF_3bc97140

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


theorem inv2 {I : Type*} [Fintype I] {m : ℕ} (inst : Instance I m)
    (R : ℝ) (hR : 0 < R) (hbR : ∀ i j, inst.b i j ≤ R * inst.B i)
    (sel : (I → ℝ) → Fin m → I) (k : ℕ) :
    (∀ i (j : Fin m), k ≤ j.val → (runPrefix inst ((1 + R) ^ (1 / R)) sel k).y i j = 0) ∧
    (∀ i, (runPrefix inst ((1 + R) ^ (1 / R)) sel k).spent i =
      min (∑ j, inst.b i j * (runPrefix inst ((1 + R) ^ (1 / R)) sel k).y i j) (inst.B i)) ∧
    (∀ i, ∑ j, inst.b i j * (runPrefix inst ((1 + R) ^ (1 / R)) sel k).y i j
      ≤ inst.B i + ⨆ j, inst.b i j) := by
  have hxl := inv_all inst R hR hbR sel
  set c := (1 + R) ^ (1 / R) with hc
  have hc1 : 1 < c := Real.one_lt_rpow (by linarith) (by positivity)
  have hc0 : 0 < c := by linarith
  have hM : ∀ i, 0 ≤ ⨆ j, inst.b i j := fun i =>
    Real.iSup_nonneg (fun j => inst.b_nonneg i j)
  induction k with
  | zero =>
    refine ⟨fun i j _ => ?_, fun i => ?_, fun i => ?_⟩
    · simp [runPrefix, State.init]
    · simp [runPrefix, State.init, min_eq_left (inst.B_pos i).le]
    · simp only [runPrefix, State.init, mul_zero, Finset.sum_const_zero]
      have := inst.B_pos i
      linarith [hM i]
  | succ k ih =>
    obtain ⟨ha, hsp, hS⟩ := ih
    have hx := hxl k
    rw [runPrefix]
    split_ifs with hkm
    · set s := runPrefix inst c sel k with hs
      set j0 : Fin m := ⟨k, hkm⟩ with hj0
      unfold step
      simp only
      split_ifs with h1
      · exact ⟨fun i j hj => ha i j (by omega), hsp, hS⟩
      · set i0 := sel s.x j0 with hi0
        have hx1 : s.x i0 < 1 := lt_of_not_ge h1
        have hB0 : 0 < inst.B i0 := inst.B_pos i0
        -- S < B for the selected buyer
        have hSlt : ∑ j, inst.b i0 j * s.y i0 j < inst.B i0 := by
          have h2 := hx.2 i0
          have hcm : 0 < c - 1 := by linarith
          have h3 : c ^ ((∑ j, inst.b i0 j * s.y i0 j) / inst.B i0) < c ^ (1 : ℝ) := by
            rw [Real.rpow_one]
            have h4 : 1 / (c - 1) * (c ^ ((∑ j, inst.b i0 j * s.y i0 j) / inst.B i0) - 1) < 1 :=
              lt_of_le_of_lt h2 hx1
            rw [one_div, inv_mul_lt_iff₀ hcm] at h4
            linarith
          rw [Real.rpow_lt_rpow_left_iff hc1, div_lt_one hB0] at h3
          exact h3
        have hy0 : s.y i0 j0 = 0 := ha i0 j0 (le_refl _)
        have hsum : ∑ j, inst.b i0 j * Function.update (s.y i0) j0 1 j
            = ∑ j, inst.b i0 j * s.y i0 j + inst.b i0 j0 := by
          have hterm : ∀ j, inst.b i0 j * Function.update (s.y i0) j0 1 j =
              inst.b i0 j * s.y i0 j + (if j = j0 then inst.b i0 j0 else 0) := by
            intro j
            by_cases hj : j = j0
            · subst hj; simp [hy0]
            · simp [hj]
          rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
            Finset.sum_ite_eq']
          simp
        refine ⟨fun i j hj => ?_, fun i => ?_, fun i => ?_⟩
        · by_cases hi : i = i0
          · subst hi
            simp only [Function.update_self]
            have hjne : j ≠ j0 := by
              intro h; rw [h] at hj; simp [hj0] at hj
            rw [Function.update_of_ne hjne]
            exact ha _ j (by omega)
          · simp only [Function.update_apply, if_neg hi]
            exact ha i j (by omega)
        · by_cases hi : i = i0
          · subst hi
            simp only [Function.update_self]
            rw [hsum, hsp, min_eq_left hSlt.le, ← min_add_add_left, add_sub_cancel]
          · simp only [Function.update_apply, if_neg hi]
            exact hsp i
        · by_cases hi : i = i0
          · subst hi
            simp only [Function.update_self]
            rw [hsum]
            have : inst.b i0 j0 ≤ ⨆ j, inst.b i0 j :=
              le_ciSup (Set.finite_range _).bddAbove j0
            linarith
          · simp only [Function.update_apply, if_neg hi]
            exact hS i
    · exact ⟨fun i j hj => ha i j (by omega), hsp, hS⟩

end ADF_3bc97140

open BJNAdAuctions.Basic in
theorem solution {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : Instance I m)
    (R : ℝ) (hR : 0 < R) (hbR : ∀ i j, inst.b i j ≤ R * inst.B i)
    (sel : (I → ℝ) → Fin m → I) (i : I) :
    ∑ j, inst.b i j * (run inst ((1 + R) ^ (1 / R)) sel).y i j ≤ inst.B i + (⨆ j, inst.b i j) ∧
    (1 - R) * ∑ j, inst.b i j * (run inst ((1 + R) ^ (1 / R)) sel).y i j ≤
      (run inst ((1 + R) ^ (1 / R)) sel).spent i := by
  obtain ⟨_, hsp, hS⟩ := ADF_3bc97140.inv2 inst R hR hbR sel m
  have hy := (ADF_3bc97140.inv_all inst R hR hbR sel m).1
  unfold run
  refine ⟨hS i, ?_⟩
  rw [hsp i]
  set S := ∑ j, inst.b i j * (runPrefix inst ((1 + R) ^ (1 / R)) sel m).y i j with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => mul_nonneg (inst.b_nonneg i j) (hy i j))
  have hB := inst.B_pos i
  have hMR : (⨆ j, inst.b i j) ≤ R * inst.B i := by
    rcases isEmpty_or_nonempty (Fin m) with h | h
    · rw [Real.iSup_of_isEmpty]; positivity
    · exact ciSup_le (fun j => hbR i j)
  have hS1 := hS i
  rcases le_total S (inst.B i) with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]
    rcases le_total R 1 with hR1 | hR1
    · nlinarith
    · nlinarith
