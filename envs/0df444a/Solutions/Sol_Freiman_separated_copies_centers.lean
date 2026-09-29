-- Prove2me | solution 1 for Freiman.separated_copies_centers
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:46:53.134311+00:00
-- url     : https://prove2.me/submissions/c071262c-f739-46d0-9938-f0ce9c17380c

import Definitions.Def_Freiman_wordRealization
import Theorems.Thm_Freiman_localValue_window_bound
import Theorems.Thm_Freiman_localValue_shift
import Theorems.Thm_Freiman_cylinder_bound_tendsto
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

open Freiman

namespace M8_separated_copies_centers

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

theorem value_comparison (a b : ℤ → ℕ+) (i j : ℤ) (R : ℕ)
    (h : ∀ k : ℤ, -(R:ℤ)≤k → k≤(R:ℤ) → a (i+k)=b (j+k)) :
    |localValue a i-localValue b j|≤2/((Nat.fib (R+1):ℝ)^2) := by
  have hw := localValue_window_bound (fun k : ℤ => a (i+k))
    (fun k : ℤ => b (j+k)) 0 R (by
      intro k hk0 hk1
      exact h k (by simpa using hk0) (by simpa using hk1))
  simpa only [localValue_shift,add_zero] using hw

theorem copies_centers (a b : ℤ → ℕ+) (N : ℕ) (hcopy : SeparatedCopies a b N) :
    ∃ p : ℕ → ℕ, StrictMono p ∧
      Filter.Tendsto (fun j : ℕ => localValue b (p j:ℤ)) Filter.atTop (nhds (localValue a 0)) := by
  let p : ℕ → ℕ := fun j => copyStart N j+N+j
  have hp : StrictMono p := by
    apply strictMono_nat_of_lt_succ
    intro j
    change copyStart N j+N+j<copyStart N (j+1)+N+(j+1)
    rw [start_succ]
    omega
  have hwindow (j : ℕ) : ∀ k : ℤ, -(j:ℤ)≤k → k≤(j:ℤ) →
      b ((p j:ℤ)+k)=a (0+k) := by
    intro k hk0 hk1
    have hx0 : (0:ℤ)≤((N+j:ℕ):ℤ)+k := by omega
    have hx1 : ((N+j:ℕ):ℤ)+k≤((2*(N+j):ℕ):ℤ) := by omega
    have hc := copy_offset a b N hcopy j (((N+j:ℕ):ℤ)+k) hx0 hx1
    have heq : (((N+j:ℕ):ℤ)+k)-((N+j:ℕ):ℤ)=k := by omega
    rw [heq] at hc
    simpa only [p,Nat.cast_add,add_assoc,zero_add] using hc
  have hbound (j : ℕ) : |localValue b (p j:ℤ)-localValue a 0|≤
      2/((Nat.fib (j+1):ℝ)^2) :=
    value_comparison b a (p j:ℤ) 0 j (hwindow j)
  refine ⟨p,hp,Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  obtain ⟨J,hJ⟩ := Metric.tendsto_atTop.1 cylinder_bound_tendsto ε hε
  refine ⟨J,?_⟩
  intro j hj
  rw [Real.dist_eq]
  apply (hbound j).trans_lt
  apply (le_abs_self _).trans_lt
  simpa only [Real.dist_eq,sub_zero] using hJ j hj

end M8_separated_copies_centers


theorem solution (a b : ℤ → ℕ+) (N : ℕ) (hcopy : SeparatedCopies a b N) :
    ∃ p : ℕ → ℕ, StrictMono p ∧ Filter.Tendsto (fun j : ℕ => localValue b (p j : ℤ)) Filter.atTop (nhds (localValue a 0)) := by exact M8_separated_copies_centers.copies_centers a b N hcopy

#print axioms solution
