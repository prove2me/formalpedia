-- Prove2me | solution 1 for GRH.centered_prefix_character_unit_rows
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:44:17.941028+00:00
-- url     : https://prove2.me/submissions/9cee4ff9-b074-4b8f-a5b1-796d694370a4

import Definitions.Def_GRH_CharacterMoment
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

open GRH.CharacterMoment

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

private lemma zero_off {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ℕ} (h : ¬ a.Coprime q) :
    χ (a:ZMod q)=0 :=
  MulChar.map_nonunit χ (fun hu => h ((ZMod.isUnit_iff_coprime a q).1 hu))

/-- One period of a nonprincipal character has zero sum on its units. Every
other centered prefix is exactly its indicated Fourier coefficient. -/
theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    (∑ a ∈ units q, χ (a:ZMod q))=0 ∧ ∀ n : ℕ,
      (∑ k ∈ Finset.range n,χ ((k+1:ℕ):ZMod q))-1 =
        if n%q=0 then -1 else ∑ a ∈ units q,(entry (n%q) a:ℂ)*χ (a:ZMod q) := by
  have hz : ∑ a ∈ units q, χ (a:ZMod q)=0 := by
    have sumAll : ∑ i ∈ Finset.range q, χ (i:ZMod q) = ∑ a : ZMod q, χ a := by
      exact Finset.sum_nbij' (i:=fun j => ((j:ℕ):ZMod q)) (j:=fun b => b.val)
        (fun _ _ => Finset.mem_univ _) (fun b _ => Finset.mem_range.mpr (ZMod.val_lt b))
        (fun _ hj => ZMod.val_natCast_of_lt (Finset.mem_range.mp hj))
        (fun b _ => ZMod.natCast_rightInverse b) (fun _ _ => rfl)
    apply Eq.trans _ (sumAll.trans (MulChar.sum_eq_zero_of_ne_one hχ))
    rw [units,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs with h
    · rfl
    · exact (zero_off χ h).symm
  refine ⟨hz,?_⟩
  intro n
  let A (k : ℕ) := ∑ i ∈ Finset.range k, χ ((i+1:ℕ):ZMod q)
  have shift (k : ℕ) : A (k+q)=A k := by
    simp only [A,Finset.sum_range_add,period_zero χ hχ,add_zero]
  have reduce (k l : ℕ) : A (k+q*l)=A k := by
    induction l with
    | zero => simp
    | succ l ih => rw [Nat.mul_succ,← Nat.add_assoc,shift,ih]
  let r := n%q
  have hr : r<q := Nat.mod_lt _ (NeZero.pos q)
  change A n-1=if r=0 then -1 else _
  rw [show A n=A r by simpa only [Nat.mod_add_div] using reduce (n%q) (n/q)]
  by_cases e : r=0
  · simp [e,A]
  rw [if_neg e]
  have identify : A r-1=∑ a ∈ units q,(entry r a:ℂ)*χ (a:ZMod q) := by
    have sub := Finset.sum_range_add_sum_Ico (fun k => χ ((k+1:ℕ):ZMod q))
      (show 1 ≤ r by omega)
    change A 1 + _ = A r at sub
    rw [show A 1=1 by simp [A]] at sub
    rw [← sub,add_sub_cancel_left]
    calc _ = ∑ k ∈ Finset.Ico 2 (r+1),χ (k:ZMod q) := by
              refine Finset.sum_nbij' (i:=fun k : ℕ => k+1) (j:=fun k : ℕ => k-1)
                (fun k hk => ?_) (fun k hk => ?_) (fun k _ => by omega)
                (fun k hk => ?_) (fun _ _ => rfl)
              all_goals simp only [Finset.mem_Ico] at *; omega
         _ = ∑ k ∈ Finset.range q, if 1<k ∧ k≤r then χ (k:ZMod q) else 0 := by
              rw [← Finset.sum_filter]
              congr 1
              ext k
              simp only [Finset.mem_Ico,Finset.mem_filter,Finset.mem_range]
              omega
         _ = _ := by
              rw [units,Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro k _
              by_cases hc : k.Coprime q
              · by_cases he : 1<k ∧ k≤r <;> simp [entry,hc,he]
              · simp [hc,zero_off χ hc]
  exact identify
