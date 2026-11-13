-- Prove2me | solution 1 for AutoregLTF.eq_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:59.099204+00:00
-- url     : https://prove2.me/submissions/b73ea548-f1fa-4368-ae74-3e79cb2dfaad

import Mathlib
import Definitions.Def_AutoregLTF_gen16
import Definitions.Def_AutoregLTF_prompt

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Eq39
open AutoregLTF

lemma zAt_step {d : ℕ} (P : ℕ) (hP : P + 1 ≤ d) (B : ℤ) (hB : 0 < B) (a : ℕ → ℤ)
    (x : Fin d → Bool) (n : ℤ) (hn : 1 ≤ n) :
    zAt (wOf d P B a) x n = decide (0 ≤ -B + ∑ ℓ : Fin (P + 1),
      a (ℓ.val + 1) * ((zAt (wOf d P B a) x (n - (ℓ.val + 1))).toNat : ℤ)) := by
  set k : ℕ := (n + d - 1).toNat with hk
  have hkd : ¬ k < d := by omega
  have h1 : zAt (wOf d P B a) x n =
      decide (1 ≤ ∑ ℓ : Fin d, wOf d P B a ℓ * ((traj (wOf d P B a) x (k - 1 - ℓ.val)).toNat : ℚ)) := by
    unfold zAt
    rw [← hk, traj, dif_neg hkd]
  have hz : ∀ ℓ : ℕ, ℓ + 1 ≤ d → (zAt (wOf d P B a) x (n - (ℓ + 1))) =
      traj (wOf d P B a) x (k - 1 - ℓ) := by
    intro ℓ hℓ
    unfold zAt
    congr 1
    omega
  set c : ℕ → ℚ := fun ℓ => ((zAt (wOf d P B a) x (n - (ℓ + 1))).toNat : ℚ) with hc
  have h2 : ∑ ℓ : Fin d, wOf d P B a ℓ * ((traj (wOf d P B a) x (k - 1 - ℓ.val)).toNat : ℚ) =
      ∑ ℓ ∈ Finset.range d, (if ℓ ≤ P then (a (ℓ + 1) : ℚ) / B * c ℓ else 0) := by
    rw [Finset.sum_range (fun ℓ => (if ℓ ≤ P then (a (ℓ + 1) : ℚ) / B * c ℓ else 0))]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    have := ℓ.isLt
    simp only [wOf, hc]
    rw [hz ℓ.val (by omega)]
    by_cases h : ℓ.val ≤ P
    · simp [h]
    · simp [h]
  have h3 : ∑ ℓ ∈ Finset.range d, (if ℓ ≤ P then (a (ℓ + 1) : ℚ) / B * c ℓ else 0) =
      ∑ ℓ : Fin (P + 1), (a (ℓ.val + 1) : ℚ) / B * c ℓ.val := by
    rw [← Finset.sum_range_add_sum_Ico _ hP, Finset.sum_eq_zero (s := Finset.Ico (P + 1) d)]
    · rw [add_zero, Finset.sum_range (fun ℓ => if ℓ ≤ P then (a (ℓ + 1) : ℚ) / B * c ℓ else 0)]
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      have := ℓ.isLt
      have : ℓ.val ≤ P := by omega
      simp [this]
    · intro ℓ hℓ
      rw [Finset.mem_Ico] at hℓ
      have : ¬ ℓ ≤ P := by omega
      simp [this]
  rw [h1, h2, h3]
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  have h4 : ∑ ℓ : Fin (P + 1), (a (ℓ.val + 1) : ℚ) / B * c ℓ.val =
      ((∑ ℓ : Fin (P + 1), a (ℓ.val + 1) * ((zAt (wOf d P B a) x (n - (ℓ.val + 1))).toNat : ℤ) : ℤ) : ℚ) / B := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun ℓ _ => ?_)
    simp only [hc]; ring
  rw [h4]
  apply decide_eq_decide.mpr
  rw [le_div_iff₀ hBq, one_mul]
  constructor
  · intro h
    have : (B : ℚ) ≤ ((∑ ℓ : Fin (P + 1), a (ℓ.val + 1) * ((zAt (wOf d P B a) x (n - (ℓ.val + 1))).toNat : ℤ) : ℤ) : ℚ) := h
    have := (Int.cast_le (R := ℚ)).mp this
    omega
  · intro h
    have : B ≤ ∑ ℓ : Fin (P + 1), a (ℓ.val + 1) * ((zAt (wOf d P B a) x (n - (ℓ.val + 1))).toNat : ℤ) := by omega
    exact_mod_cast this

lemma block_last (m : ℕ) (f : St) : block m f (p m - 1) = false := by
  have hp : p m = 378 * (m + 2) := rfl
  by_contra h
  have h' : block m f (p m - 1) = true := by simpa using h
  simp only [block, Bool.or_eq_true, List.any_eq_true, List.mem_range', Bool.and_eq_true,
    piRow, piTest, piOut, piPtr] at h'
  rcases h' with (((h | ⟨j, ⟨i, hi, hj⟩, h, -⟩) | ⟨h, -⟩) | ⟨j, ⟨i, hi, hj⟩, h, -⟩) |
    ⟨j, ⟨i, hi, hj⟩, h, -⟩
  all_goals first
    | omega
    | (have := of_decide_eq_true h; omega)
    | (rcases h with h | h <;> (have := of_decide_eq_true h; omega))

lemma zAt_prompt {d : ℕ} (w : Fin d → ℚ) (x : Fin d → Bool) (n : ℤ) (h1 : 1 - (d : ℤ) ≤ n)
    (h2 : n ≤ 0) : zAt w x n = x ⟨(n + d - 1).toNat, by omega⟩ := by
  unfold zAt
  rw [traj, dif_pos (by omega)]

lemma prompt0_val {d : ℕ} (w : Fin d → ℚ) (m : ℕ) (θ : ℕ → ℤ) (i : ℕ) (n : ℤ)
    (h1 : 1 - (d : ℤ) ≤ n) (h2 : n ≤ 0) :
    zAt w (prompt0 m d θ i) n =
      if n ≤ -(p m : ℤ) then false else E m θ i 0 (n + p m - 1).toNat := by
  rw [zAt_prompt w _ n h1 h2]
  have : (((n + d - 1).toNat : ℕ) : ℤ) + 1 - d = n := by omega
  simp only [prompt0, this]

end AutoregLTF.Dev.Eq39

namespace AutoregLTF
open AutoregLTF.Dev.Eq39 in
theorem chk_eq_39 (m : ℕ) (hm : 2 ≤ m) (lab : ℕ → ℕ → Bool) (d : ℕ) (hd : p m + 1 ≤ d)
    (B : ℤ) (hB : 0 < B) (a : ℕ → ℤ)
    (ha : ∀ i ∈ Finset.Icc 1 m, ∀ t : ℕ, ∀ r < p m,
      gen16 (p m) B a (hist m (enc m lab) i t) (p m + 1 + r) = E m (enc m lab) i (t + 1) r)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 m) (t : ℕ) :
    zAt (wOf d (p m) B a) (prompt0 m d (enc m lab) i) (((t : ℤ) - 1) * p m) = false ∧
    ∀ r < p m, zAt (wOf d (p m) B a) (prompt0 m d (enc m lab) i)
      (((t : ℤ) - 1) * p m + 1 + r) = E m (enc m lab) i t r := by
  have hP : p m = 378 * (m + 2) := rfl
  induction t with
  | zero =>
    have e1 : (((0 : ℕ) : ℤ) - 1) * (p m : ℤ) = -(p m : ℤ) := by push_cast; ring
    rw [e1]
    refine ⟨?_, ?_⟩
    · rw [prompt0_val _ _ _ _ _ (by omega) (by omega)]
      simp
    · intro r hr
      have e2 : -(p m : ℤ) + 1 + r = -(p m : ℤ) + 1 + r := rfl
      rw [prompt0_val _ _ _ _ _ (by omega) (by omega), if_neg (by omega)]
      have : (-(p m : ℤ) + 1 + r + p m - 1).toNat = r := by omega
      rw [this]
  | succ t ih =>
    have hu : -(p m : ℤ) ≤ ((t : ℤ) - 1) * p m := by
      have : (0 : ℤ) ≤ (t : ℤ) * p m := by positivity
      linarith
    have hnext : (((t + 1 : ℕ) : ℤ) - 1) * (p m : ℤ) = ((t : ℤ) - 1) * p m + p m := by
      push_cast; ring
    rw [hnext]
    generalize ((t : ℤ) - 1) * p m = u at *
    have hgen : ∀ k : ℕ, k ≤ 2 * p m →
        gen16 (p m) B a (hist m (enc m lab) i t) k = zAt (wOf d (p m) B a) (prompt0 m d (enc m lab) i) (u + k) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ihk =>
        intro hk
        by_cases hkP : k ≤ p m
        · rw [gen16, if_pos hkP]
          rcases k with _ | j
          · simp [hist, ih.1]
          · have := ih.2 j (by omega)
            rw [hist, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
            rw [← this, show u + ((j + 1 : ℕ) : ℤ) = u + 1 + j by push_cast; ring]
        · rw [gen16, if_neg hkP]
          rw [zAt_step (p m) hd B hB a _ (u + k) (by omega)]
          refine decide_eq_decide.mpr ?_
          have : ∑ ℓ : Fin (p m + 1), a (ℓ.val + 1) *
              ((gen16 (p m) B a (hist m (enc m lab) i t) (k - (ℓ.val + 1))).toNat : ℤ) =
              ∑ ℓ : Fin (p m + 1), a (ℓ.val + 1) *
              ((zAt (wOf d (p m) B a) (prompt0 m d (enc m lab) i) (u + k - (ℓ.val + 1))).toNat : ℤ) := by
            refine Finset.sum_congr rfl (fun ℓ _ => ?_)
            have hl := ℓ.isLt
            rw [ihk (k - (ℓ.val + 1)) (by omega) (by omega)]
            rw [show u + ((k - (ℓ.val + 1) : ℕ) : ℤ) = u + k - (ℓ.val + 1) by omega]
          rw [this]
    have hPpos : 0 < p m := by omega
    refine ⟨?_, ?_⟩
    · have h := ih.2 (p m - 1) (by omega)
      have e : u + 1 + ((p m - 1 : ℕ) : ℤ) = u + p m := by omega
      rw [e] at h
      rw [h]
      exact block_last m _
    · intro r hr
      rw [← ha i hi t r hr, hgen (p m + 1 + r) (by omega)]
      congr 1
      push_cast; ring

end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_eq_39 := @AutoregLTF.chk_eq_39
