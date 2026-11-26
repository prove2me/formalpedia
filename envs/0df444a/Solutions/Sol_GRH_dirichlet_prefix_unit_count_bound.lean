-- Prove2me | solution 1 for GRH.dirichlet_prefix_unit_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T16:16:19.463104+00:00
-- url     : https://prove2.me/submissions/fa4e2644-9118-4b5e-b089-9c32f849f06b

import Definitions.Def_GRH_DirichletPrefix
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

open GRH.DirichletPrefix

private lemma period_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range q, χ ((n+i+1:ℕ) : ZMod q) = 0 := by
  have reindex (f : ZMod q → ℂ) :
      ∑ i ∈ Finset.range q, f (i : ZMod q) = ∑ b : ZMod q, f b := by
    refine Finset.sum_nbij' (i := fun j => ((j : ℕ) : ZMod q)) (j := fun b => b.val)
      (fun _ _ => Finset.mem_univ _) (fun b _ => Finset.mem_range.mpr (ZMod.val_lt b))
      (fun _ hj => ZMod.val_natCast_of_lt (Finset.mem_range.mp hj))
      (fun b _ => ZMod.natCast_rightInverse b) (fun _ _ => rfl)
  calc _ = ∑ i ∈ Finset.range q, (fun b : ZMod q => χ ((n+1:ℕ)+b)) i := by
          apply Finset.sum_congr rfl
          intro i _
          push_cast
          congr 1
          abel
       _ = ∑ b : ZMod q, χ ((n+1:ℕ)+b) := reindex (fun b : ZMod q => χ ((n+1:ℕ)+b))
       _ = ∑ b : ZMod q, χ b := Fintype.sum_equiv (Equiv.addLeft ((n+1:ℕ) : ZMod q)) _ _ (fun _ => rfl)
       _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- Every prefix differs from one by at most the smaller of its forward
and backward unit counts. A complete period contributes zero. -/
theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, χ ((k+1:ℕ):ZMod q))-1‖ ≤ (weight q n:ℝ) := by
  let a (k : ℕ) := χ ((k+1:ℕ):ZMod q)
  let v (k : ℕ) : ℕ := if (k+1).Coprime q then 1 else 0
  let A (r : ℕ) := ∑ k ∈ Finset.range r,a k
  have cz : A q=0 := by simpa [A,a] using period_zero χ hχ 0
  have shift (r : ℕ) : A (r+q)=A r := by
    dsimp [A,a]
    rw [Finset.sum_range_add,period_zero χ hχ,add_zero]
  have reduce (r l : ℕ) : A (r+q*l)=A r := by
    induction l with
    | zero => simp
    | succ l ih => rw [Nat.mul_succ,← Nat.add_assoc,shift,ih]
  have eqr : A n=A (n%q) := by
    simpa only [Nat.mod_add_div] using reduce (n%q) (n/q)
  have size (k : ℕ) : ‖a k‖ ≤ (v k:ℝ) := by
    by_cases h : (k+1).Coprime q
    · rw [show v k=1 from if_pos h,Nat.cast_one]
      exact χ.norm_le_one _
    · have e := MulChar.map_nonunit χ (fun hu => h ((ZMod.isUnit_iff_coprime (k+1) q).1 hu))
      rw [show v k=0 from if_neg h,Nat.cast_zero]
      change ‖χ ((k+1:ℕ):ZMod q)‖ ≤ 0
      rw [e,norm_zero]
  have budget (S : Finset ℕ) : ‖∑ k ∈ S,a k‖ ≤ ((∑ k ∈ S,v k : ℕ):ℝ) := by
    apply (norm_sum_le _ _).trans
    push_cast
    exact Finset.sum_le_sum (fun k _ => size k)
  have total : count q q=q.totient := by
    have h : (∑ k ∈ Finset.Ico 1 (1+q), if q.Coprime k then 1 else 0) = q.totient := by
      simpa only [Finset.sum_boole, Nat.cast_id] using Nat.filter_coprime_Ico_eq_totient q 1
    rw [Finset.sum_Ico_eq_sum_range,show 1+q-1=q by omega] at h
    simpa only [count,Nat.add_comm 1,Nat.coprime_comm] using h
  let r := n%q
  have hr : r ≤ q := (Nat.mod_lt _ (NeZero.pos q)).le
  change ‖A n-1‖ ≤ (weightAt q r:ℝ)
  rw [eqr]
  change ‖A r-1‖ ≤ (weightAt q r:ℝ)
  by_cases h : r=0
  · simp [h,A,weightAt]
  · have hr1 : 1 ≤ r := by omega
    have aone : A 1=1 := by simp [A,a]
    have cone : count q 1=1 := by
      simp only [count,Finset.sum_range_one,Nat.zero_add]
      exact if_pos (by simp [Nat.Coprime])
    have hpre : A 1+(∑ k ∈ Finset.Ico 1 r,a k)=A r := Finset.sum_range_add_sum_Ico a hr1
    have ct : count q 1+(∑ k ∈ Finset.Ico 1 r,v k)=count q r := Finset.sum_range_add_sum_Ico v hr1
    have ht : A r+(∑ k ∈ Finset.Ico r q,a k)=A q := Finset.sum_range_add_sum_Ico a hr
    have cr : count q r+(∑ k ∈ Finset.Ico r q,v k)=count q q := Finset.sum_range_add_sum_Ico v hr
    rw [aone] at hpre
    rw [cone] at ct
    rw [cz] at ht
    rw [total] at cr
    rw [weightAt,if_neg h,Nat.cast_min]
    apply le_min
    · rw [← hpre,add_sub_cancel_left]
      have ec : count q r-1=∑ k ∈ Finset.Ico 1 r,v k := by omega
      rw [ec]
      exact budget _
    · have comp : A r = -(∑ k ∈ Finset.Ico r q,a k) := eq_neg_of_add_eq_zero_left ht
      have ec : q.totient+1-count q r=(∑ k ∈ Finset.Ico r q,v k)+1 := by omega
      rw [comp,ec,Nat.cast_add,Nat.cast_one]
      apply (norm_sub_le _ _).trans
      rw [norm_neg,norm_one]
      linarith only [budget (Finset.Ico r q)]
