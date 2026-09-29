-- Prove2me | solution 1 for Freiman.upper_large_noncentral
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:16:53.333061+00:00
-- url     : https://prove2.me/submissions/221d5992-d30b-4f00-8db2-24feff94648a

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_cf_convergence

open Freiman

private theorem pad_right (n : ℕ+) (l r : ℕ → ℕ+) (j k : ℕ) :
    upperPad (upperCentral n l r) j ((k : ℤ)+1) = if k+1 ≤ j then r k else 3 := by
  have habs : ((k : ℤ)+1).natAbs=k+1 := by omega
  have hnat : ((k : ℤ)+1).toNat-1=k := by omega
  simp only [upperPad,habs]
  split_ifs
  · rw [upperCentral,if_neg (by omega),if_pos (by omega),hnat]
  · rfl

private theorem pad_reflection (n : ℕ+) (l r : ℕ → ℕ+) (j : ℕ) (i : ℤ) :
    upperPad (upperCentral n l r) j (-i) = upperPad (upperCentral n r l) j i := by
  by_cases hz : i = 0
  · simp [hz, upperPad, upperCentral]
  by_cases hp : 0 < i
  · simp [upperPad, upperCentral, hz, hp, neg_ne_zero.mpr hz,
      show ¬i < 0 by omega]
  · have hn : i < 0 := by omega
    simp [upperPad, upperCentral, hz, hp, neg_ne_zero.mpr hz,
      hn]

private theorem local_reflection (a : ℤ → ℕ+) (i : ℤ) :
    localValue (fun k => a (-k)) i = localValue a (-i) := by
  have hl : (fun n : ℕ => a (-(i-(n:ℤ)-1))) = (fun n : ℕ => a (-i+(n:ℤ)+1)) := by
    funext n
    congr 1
    ring
  have hr : (fun n : ℕ => a (-(i+(n:ℤ)+1))) = (fun n : ℕ => a (-i-(n:ℤ)-1)) := by
    funext n
    congr 1
    ring
  unfold localValue
  rw [hl,hr]
  ring

private theorem cf_at_most_third (b : ℕ → ℕ+) (hb : 3 ≤ (b 0 : ℕ)) :
    cfValue b ≤ (1/3 : ℝ) := by
  have h := cf_convergence b
  have ht := (cf_convergence (fun n => b (n+1))).2.2.1
  have hd : (3 : ℝ) ≤ (b 0 : ℕ) := by exact_mod_cast hb
  rw [h.2.2.2.2]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

private theorem positive_large_bound (n : ℕ+) (hn : 5 ≤ (n : ℕ))
    (l r : ℕ → ℕ+) (hr : upperAdmissible r) (j k : ℕ) :
    localValue (upperPad (upperCentral n l r) j) ((k : ℤ)+1) ≤ (16/3 : ℝ) := by
  let a := upperPad (upperCentral n l r) j
  have hadigit : (a ((k : ℤ)+1) : ℕ) ≤ 4 := by
    dsimp [a]
    rw [pad_right]
    split_ifs
    · exact hr.1 k
    · norm_num
  have hleft := (cf_convergence (fun m : ℕ => a (((k : ℤ)+1)-(m:ℤ)-1))).2.2.2.1
  have hright := (cf_convergence (fun m : ℕ => a (((k : ℤ)+1)+(m:ℤ)+1))).2.2.2.1
  by_cases h4 : (a ((k : ℤ)+1) : ℕ) = 4
  · have hnear : 3 ≤ (a (k : ℤ) : ℕ) := by
      have hin : k+1 ≤ j := by
        by_contra hh
        dsimp [a] at h4
        rw [pad_right, if_neg hh] at h4
        norm_num at h4
      cases k with
      | zero =>
        change 3 ≤ (upperPad (upperCentral n l r) j 0 : ℕ)
        simpa [upperPad,upperCentral] using (show 3 ≤ (n:ℕ) by omega)
      | succ k =>
        have hc : (r (k+1) : ℕ)=4 := by
          dsimp [a] at h4
          change (upperPad (upperCentral n l r) j (((k+1:ℕ):ℤ)+1) : ℕ) = 4 at h4
          simpa only [pad_right, if_pos hin] using h4
        have hprev : 3 ≤ (r k : ℕ) := by
          by_contra hh
          have ht := hr.2 k (by omega)
          omega
        dsimp [a]
        rw [pad_right, if_pos (by omega)]
        exact hprev
    have hsmall := cf_at_most_third
      (fun m : ℕ => a (((k : ℤ)+1)-(m:ℤ)-1)) (by simpa using hnear)
    have hd : ((a ((k : ℤ)+1) : ℕ) : ℝ)=4 := by exact_mod_cast h4
    change ((a ((k : ℤ)+1) : ℕ) : ℝ) + _ + _ ≤ _
    linarith
  · have hd : ((a ((k : ℤ)+1) : ℕ) : ℝ) ≤ 3 := by
      exact_mod_cast (show (a ((k : ℤ)+1) : ℕ) ≤ 3 by omega)
    change ((a ((k : ℤ)+1) : ℕ) : ℝ) + _ + _ ≤ _
    linarith

theorem solution (n : ℕ+) (hn : 5 ≤ (n : ℕ)) (l r : ℕ → ℕ+)
    (hl : upperAdmissible l) (hr : upperAdmissible r) (j : ℕ) (i : ℤ) (hi : i ≠ 0) :
    localValue (upperPad (upperCentral n l r) j) i ≤ (16 / 3 : ℝ) := by
  by_cases hip : 0 < i
  · obtain ⟨k,hk⟩ : ∃ k : ℕ, i=((k+1 : ℕ):ℤ) := by
      refine ⟨i.toNat-1, ?_⟩
      omega
    rw [hk]
    exact positive_large_bound n hn l r hr j k
  · have hin : 0 < -i := by omega
    obtain ⟨k,hk⟩ : ∃ k : ℕ, -i=((k+1 : ℕ):ℤ) := by
      refine ⟨(-i).toNat-1, ?_⟩
      omega
    have hreflect : (fun t => upperPad (upperCentral n l r) j (-t)) =
        upperPad (upperCentral n r l) j := funext (pad_reflection n l r j)
    have ht := positive_large_bound n hn r l hl j k
    have hk' : -i = (k : ℤ)+1 := by omega
    rw [← hk', ← hreflect, local_reflection, neg_neg] at ht
    exact ht
