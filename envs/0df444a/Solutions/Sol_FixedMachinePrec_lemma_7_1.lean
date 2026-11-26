-- Prove2me | solution 1 for FixedMachinePrec.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:03:07.11719+00:00
-- url     : https://prove2.me/submissions/fb59652a-1da8-48f0-958e-f503a7d53d89

import Mathlib
import Definitions.Def_FixedMachinePrec_Separator
import Theorems.Thm_FixedMachinePrec_replace_middle_block
import Theorems.Thm_FixedMachinePrec_priority_exchange_decreases_encoding

open FixedMachinePrec


private theorem union_mem {N} (s : List (Finset (Fin N))) (x) : x ∈ unionSlots s ↔ ∃ A ∈ s, x ∈ A := by
  unfold unionSlots; induction s with | nil => simp | cons A s ih => simp [ih]


theorem solution {N : ℕ} (m : ℕ) (hm : 3 ≤ m) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (hprec : IsStrictOrder' prec) (σ : List (Finset (Fin N)))
    (hσ : IsFullSchedule prec m Finset.univ σ) (a b : ℕ) (hab : a < b) (hb : b ≤ σ.length + 1) :
    let Zs := (σ.drop a).take (b - 1 - a)
    let U := slotsBetween σ a b
    (∀ π : List (Finset (Fin N)), IsFullSchedule prec m U π →
      IsFullSchedule prec m Finset.univ (σ.take a ++ π ++ σ.drop (b - 1))) ∧
    (∀ pri : List (Fin N), IsPriorityList prec U pri → IsNormalized prec m U pri Zs →
      ∀ r : ℕ, 1 ≤ r → r ≤ Zs.length →
      ∀ ρ : List (Finset (Fin N)), IsFullSchedule prec m U ρ → ρ.take r = Zs.take r →
      ∀ x y : Fin N, y ∈ ρ.getD (r - 1) ∅ → x ∈ U → r < localTime ρ x →
        pri.idxOf x < pri.idxOf y → ¬ IsFullSchedule prec m U (swapJobs ρ x y)) := by
  let Z := (σ.drop a).take (b-1-a)
  have e : a+(b-1-a) = b-1 := by omega
  have orig : σ.take a ++ Z ++ σ.drop (b-1) = σ := by
    rw [← e,List.append_assoc]; simp [Z,List.drop_drop,Nat.add_comm,List.take_append_drop]
  have hmid : unionSlots Z = slotsBetween σ a b := by
    ext x; rw [union_mem]; simp only [slotsBetween,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_range]
    constructor
    · rintro ⟨A,hA,hx⟩
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hA
      have len : j < min (b-1-a) (σ.length-a) := by simpa [Z] using hj
      refine ⟨a+j,⟨by omega,by omega,by omega⟩,?_⟩
      simpa [Z,List.getD_eq_getElem?_getD,show a+j < σ.length by omega] using hx
    · rintro ⟨i,⟨hi,ha,hb'⟩,hx⟩
      have hj : i-a < Z.length := by simp [Z];omega
      refine ⟨Z[i-a],List.getElem_mem hj,?_⟩
      have eq : a+(i-a) = i := by omega
      simpa [Z,eq,List.getD_eq_getElem?_getD,hi] using hx
  dsimp only
  refine ⟨fun π hπ => replace_middle_block m prec Finset.univ _ (σ.take a) Z (σ.drop (b-1)) π (by rw [orig]; exact hσ) hmid hπ,?_⟩
  intro pri hp hn r hr hb' ρ hρ he x y hy hx hl hprio hswap
  exact (not_lt_of_ge (hn.2 _ hswap)) (priority_exchange_decreases_encoding m prec _ pri hp Z ρ hn.1 hρ r hr hb' he x y hy hx hl hprio)
