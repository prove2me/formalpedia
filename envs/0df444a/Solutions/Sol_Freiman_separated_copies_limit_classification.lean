-- Prove2me | solution 1 for Freiman.separated_copies_limit_classification
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:47:13.322669+00:00
-- url     : https://prove2.me/submissions/529f8e85-78ec-44b5-9555-8454502d53c3

import Definitions.Def_Freiman_wordRealization
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.IntervalCases

open Freiman

namespace M8_separated_copies_limit_classification

theorem start_succ (N j : ℕ) :
    copyStart N (j+1) = copyStart N j + 2*(N+j)+2 := by
  simp only [copyStart]
  ring

theorem start_strict (N : ℕ) : StrictMono (copyStart N) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [start_succ]
  omega

theorem block_at (N n : ℕ) :
    ∃ j : ℕ, copyStart N j ≤ n ∧ n < copyStart N (j+1) := by
  induction n with
  | zero => exact ⟨0, by simp [copyStart], by simp [copyStart]⟩
  | succ n ih =>
    obtain ⟨j,hj0,hj1⟩ := ih
    by_cases h : n+1 < copyStart N (j+1)
    · exact ⟨j,by omega,h⟩
    · refine ⟨j+1,by omega,?_⟩
      rw [start_succ]
      omega

theorem block_unique (N n j k : ℕ)
    (hj0 : copyStart N j ≤ n) (hj1 : n < copyStart N (j+1))
    (hk0 : copyStart N k ≤ n) (hk1 : n < copyStart N (k+1)) : j=k := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have := (start_strict N).monotone (show j+1≤k by omega)
    omega
  · have := (start_strict N).monotone (show k+1≤j by omega)
    omega

theorem copies_exist (a : ℤ → ℕ+) (N : ℕ) : ∃ b : ℤ → ℕ+, SeparatedCopies a b N := by
  classical
  let f : ℕ → ℕ+ := fun n =>
    let j := (block_at N n).choose
    if n-copyStart N j ≤ 2*(N+j)
    then a ((n:ℤ)-(copyStart N j:ℤ)-((N+j:ℕ):ℤ)) else 2
  let b : ℤ → ℕ+ := fun i => if i<0 then 2 else f i.toNat
  refine ⟨b,?_,?_,?_⟩
  · intro i hi
    dsimp only [b]
    rw [if_pos hi]
    rfl
  · intro j k hk
    have hj0 : copyStart N j ≤ copyStart N j+k := by omega
    have hj1 : copyStart N j+k < copyStart N (j+1) := by rw [start_succ]; omega
    have hi := (block_at N (copyStart N j+k)).choose_spec
    have hidx : (block_at N (copyStart N j+k)).choose=j :=
      block_unique N _ _ _ hi.1 hi.2 hj0 hj1
    change (if ((copyStart N j+k:ℕ):ℤ)<0 then (2:ℕ+)
      else f (((copyStart N j+k:ℕ):ℤ).toNat))=_
    rw [if_neg (by omega),Int.toNat_natCast]
    dsimp only [f]
    rw [hidx,if_pos (by omega)]
    congr 1
    push_cast
    ring
  · intro j
    let n := copyStart N j+2*(N+j)+1
    have hj0 : copyStart N j≤n := by dsimp [n]; omega
    have hj1 : n<copyStart N (j+1) := by dsimp [n]; rw [start_succ]; omega
    have hi := (block_at N n).choose_spec
    have hidx : (block_at N n).choose=j :=
      block_unique N _ _ _ hi.1 hi.2 hj0 hj1
    change ((if (n:ℤ)<0 then (2:ℕ+) else f ((n:ℤ).toNat)):ℕ)=2
    rw [if_neg (by omega),Int.toNat_natCast]
    dsimp only [f]
    rw [hidx,if_neg (by dsimp [n]; omega)]
    rfl

theorem copy_offset (a b : ℤ → ℕ+) (N : ℕ) (hcopy : SeparatedCopies a b N)
    (j : ℕ) (x : ℤ) (hx0 : 0≤x) (hx1 : x≤((2*(N+j):ℕ):ℤ)) :
    b ((copyStart N j:ℤ)+x)=a (x-((N+j:ℕ):ℤ)) := by
  have hx : (x.toNat:ℤ)=x := Int.toNat_of_nonneg hx0
  simpa only [Nat.cast_add,hx] using hcopy.2.1 j x.toNat (by omega)

theorem copies_alphabet (a b : ℤ → ℕ+) (N : ℕ) (hcopy : SeparatedCopies a b N)
    (ha : HasFiniteAlphabet a) : HasFiniteAlphabet b := by
  obtain ⟨M,hM⟩ := ha
  refine ⟨max M 2,?_⟩
  intro i
  by_cases hi : i<0
  · rw [hcopy.1 i hi]
    exact le_max_right _ _
  have hi0 : (i.toNat:ℤ)=i := Int.toNat_of_nonneg (by omega)
  obtain ⟨j,hj0,hj1⟩ := block_at N i.toNat
  rw [start_succ] at hj1
  let k := i.toNat-copyStart N j
  have hik : i=((copyStart N j+k:ℕ):ℤ) := by dsimp [k]; omega
  by_cases hk : k≤2*(N+j)
  · rw [hik,hcopy.2.1 j k hk]
    exact (hM _).trans (le_max_left _ _)
  · have hkeq : k=2*(N+j)+1 := by dsimp [k]; omega
    rw [hik,hkeq]
    have heq : copyStart N j+(2*(N+j)+1)=copyStart N j+2*(N+j)+1 := by omega
    rw [heq,hcopy.2.2]
    exact le_max_right _ _

theorem forbidden_ne_two (k : ℕ) (hk : k<5) :
    ([3,1,3,1,3]:List ℕ).getD k 0 ≠ 2 := by
  interval_cases k <;> decide

theorem copies_avoid (a b : ℤ → ℕ+) (N : ℕ) (hcopy : SeparatedCopies a b N)
    (ha : AvoidsBlock a [3,1,3,1,3]) : AvoidsBlock b [3,1,3,1,3] := by
  intro i hm
  have hne (k : ℕ) (hk : k<5) : (b (i+(k:ℤ)):ℕ)≠2 := by
    rw [hm k hk]
    exact forbidden_ne_two k hk
  have hi : 0 ≤ i := by
    by_contra h
    have hc := hcopy.1 i (by omega)
    exact hne 0 (by omega) (by simpa using hc)
  have hi0 : (i.toNat:ℤ)=i := Int.toNat_of_nonneg hi
  obtain ⟨j,hj0,hj1⟩ := block_at N i.toNat
  rw [start_succ] at hj1
  let x := i.toNat-copyStart N j
  have hix : i=((copyStart N j+x:ℕ):ℤ) := by dsimp [x]; omega
  have hx : x+4≤2*(N+j) := by
    by_contra h
    let k := 2*(N+j)+1-x
    have hk : k<5 := by dsimp [k,x]; omega
    have heq : i+(k:ℤ)=((copyStart N j+2*(N+j)+1:ℕ):ℤ) := by
      dsimp [k,x]
      omega
    exact hne k hk (by rw [heq]; exact hcopy.2.2 j)
  apply ha ((x:ℤ)-((N+j:ℕ):ℤ))
  intro k hk
  have hk5 : k<5 := hk
  have hcopyk := hcopy.2.1 j (x+k) (by omega)
  have heq1 : ((copyStart N j+(x+k):ℕ):ℤ)=i+(k:ℤ) := by omega
  have heq2 : ((x+k:ℕ):ℤ)-((N+j:ℕ):ℤ)=(x:ℤ)-((N+j:ℕ):ℤ)+(k:ℤ) := by
    push_cast
    ring
  rw [heq1,heq2] at hcopyk
  rw [←hcopyk]
  exact hm k hk

theorem high_position (a b : ℤ → ℕ+) (N : ℕ) (hcopy : SeparatedCopies a b N)
    (hfinite : ∀ i : ℤ, N ≤ i.natAbs → (a i : ℕ) ≤ 3)
    (z : ℤ) (hz : 3 < (b z : ℕ)) :
    ∃ j : ℕ, ∃ e : ℤ, -(N:ℤ)<e ∧ e<(N:ℤ) ∧
      z=(copyStart N j:ℤ)+((N+j:ℕ):ℤ)+e ∧ b z=a e := by
  have hz0 : 0 ≤ z := by
    by_contra h
    have := hcopy.1 z (by omega)
    omega
  have hcast : (z.toNat:ℤ)=z := Int.toNat_of_nonneg hz0
  obtain ⟨j,hj0,hj1⟩ := block_at N z.toNat
  rw [start_succ] at hj1
  let k := z.toNat-copyStart N j
  have hzk : z=((copyStart N j+k:ℕ):ℤ) := by dsimp [k]; omega
  have hk : k≤2*(N+j) := by
    by_contra h
    have hkeq : k=2*(N+j)+1 := by dsimp [k]; omega
    have heq : z=((copyStart N j+2*(N+j)+1:ℕ):ℤ) := by omega
    rw [heq,hcopy.2.2 j] at hz
    omega
  let e : ℤ := (k:ℤ)-((N+j:ℕ):ℤ)
  have heq : b z=a e := by rw [hzk]; exact hcopy.2.1 j k hk
  have habs : e.natAbs<N := by
    by_contra h
    have := hfinite e (by omega)
    rw [heq] at hz
    omega
  have hbound := Int.natCast_natAbs e
  have hlo : -(N:ℤ)<e := by
    have := neg_le_abs e
    omega
  have hhi : e<(N:ℤ) := by
    have := le_abs_self e
    omega
  exact ⟨j,e,hlo,hhi,by dsimp [e]; omega,heq⟩

theorem large_block (N J j n : ℕ) (u : ℕ → ℕ) (hu : StrictMono u)
    (i e : ℤ) (he : e<(N:ℤ))
    (hn : copyStart N J+i.natAbs ≤ n)
    (hpos : (u n:ℤ)+i=(copyStart N j:ℤ)+((N+j:ℕ):ℤ)+e) : J≤j := by
  have hun : n ≤ u n := hu.id_le n
  have hiabs : -(i.natAbs:ℤ)≤ i := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le i
  by_contra h
  have hstart := (start_strict N).monotone (show j+1≤J by omega)
  rw [start_succ] at hstart
  omega

theorem copies_limit_classification (a b : ℤ → ℕ+) (N : ℕ)
    (hcopy : SeparatedCopies a b N)
    (hfinite : ∀ i : ℤ, N≤ i.natAbs → (a i:ℕ)≤3)
    (u : ℕ → ℕ) (hu : StrictMono u) (y : ℤ → ℕ+)
    (hy : CoordinateLimit (fun j i => b ((u j:ℤ)+i)) y) : BackgroundOrShift a y := by
  classical
  by_cases hsmall : ∀ i : ℤ, (y i:ℕ)≤3
  · exact Or.inr hsmall
  push_neg at hsmall
  obtain ⟨i0,hi0⟩ := hsmall
  let S : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  have hex : ∀ᶠ n in Filter.atTop, ∃ e∈S, ∃ j : ℕ,
      -(N:ℤ)<e ∧ e<(N:ℤ) ∧
      (u n:ℤ)+i0=(copyStart N j:ℤ)+((N+j:ℕ):ℤ)+e := by
    filter_upwards [hy i0] with n hn
    have hhigh : 3<(b ((u n:ℤ)+i0):ℕ) := by rw [hn]; exact hi0
    obtain ⟨j,e,hlo,hhi,hpos,_⟩ := high_position a b N hcopy hfinite _ hhigh
    exact ⟨e,by simp only [S,Finset.mem_Icc]; omega,j,hlo,hhi,hpos⟩
  obtain ⟨e,_,hefreq⟩ := (Filter.frequently_exists_finset S).1 hex.frequently
  refine Or.inl ⟨e-i0,?_⟩
  intro i
  let J := (i-i0).natAbs
  have hlarge : ∀ᶠ n in Filter.atTop, copyStart N J+i0.natAbs≤n :=
    Filter.eventually_ge_atTop _
  obtain ⟨n,⟨j,hlo,hhi,hpos⟩,hyn,hn⟩ :=
    (hefreq.and_eventually ((hy i).and hlarge)).exists
  have hJj : J≤j := large_block N J j n u hu i0 e hhi hn hpos
  let x : ℤ := ((N+j:ℕ):ℤ)+e+(i-i0)
  have hdiff := Int.natCast_natAbs (i-i0)
  have hlowdiff := neg_abs_le (i-i0)
  have hhighdiff := le_abs_self (i-i0)
  have hx0 : 0≤x := by dsimp [x,J] at *; omega
  have hx1 : x≤((2*(N+j):ℕ):ℤ) := by dsimp [x,J] at *; omega
  have hc := copy_offset a b N hcopy j x hx0 hx1
  have hz : (copyStart N j:ℤ)+x=(u n:ℤ)+i := by dsimp [x]; omega
  have heq : x-((N+j:ℕ):ℤ)=e-i0+i := by dsimp [x]; ring
  rw [hz,heq] at hc
  exact hyn.symm.trans hc

end M8_separated_copies_limit_classification


theorem solution (a b : ℤ → ℕ+) (N : ℕ)
    (hcopy : SeparatedCopies a b N)
    (hfinite : ∀ i : ℤ, N ≤ i.natAbs → (a i : ℕ) ≤ 3)
    (u : ℕ → ℕ) (hu : StrictMono u) (y : ℤ → ℕ+)
    (hy : CoordinateLimit (fun j i => b ((u j : ℤ) + i)) y) :
    BackgroundOrShift a y := by exact M8_separated_copies_limit_classification.copies_limit_classification a b N hcopy hfinite u hu y hy

#print axioms solution
