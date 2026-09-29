-- Prove2me | solution 1 for CannonFloydParry.isStandardDyadicPartition_marks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-16T21:25:06.251114+00:00
-- url     : https://prove2.me/submissions/dc9d9eff-a06f-4604-952c-076746cae9f3

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

/-- The subdivision of a standard dyadic interval at its midpoint, in the form the recursion
produces it: level `k` with numerator `c` splits into two intervals of level `k + 1` with
numerators `2 * c` and `2 * c + 1`. -/
lemma midpoint_halves {c k : ℕ} :
    ((c : ℝ) / 2 ^ k + ((c : ℝ) + 1) / 2 ^ k) / 2 = (2 * (c : ℝ) + 1) / 2 ^ (k + 1) := by
  have h : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  ring

/-- The statement generalised from `[0,1]` to an arbitrary standard dyadic interval, which is what
the recursion needs: it descends into halves, and a half of a standard dyadic interval is again
one, at one level deeper. -/
lemma isChain_marksAux (t : TTree) :
    ∀ (c k : ℕ), c + 1 ≤ 2 ^ k →
      List.IsChain IsStandardDyadicInterval
        (((c : ℝ) / 2 ^ k) :: (t.marksAux ((c : ℝ) / 2 ^ k) (((c : ℝ) + 1) / 2 ^ k)
          ++ [((c : ℝ) + 1) / 2 ^ k])) := by
  induction t with
  | leaf =>
      intro c k hc
      simp only [TTree.marksAux, List.nil_append]
      exact List.isChain_pair.mpr ⟨c, k, hc, rfl, rfl⟩
  | node l r ihl ihr =>
      intro c k hc
      -- the two halves, as standard dyadic intervals of level `k + 1`
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hc2 : 2 * c + 1 + 1 ≤ 2 ^ (k + 1) := by rw [hpow]; omega
      have hmid : ((c : ℝ) / 2 ^ k + ((c : ℝ) + 1) / 2 ^ k) / 2 = (2 * (c : ℝ) + 1) / 2 ^ (k + 1) :=
        midpoint_halves
      have hlow : ((2 * c : ℕ) : ℝ) / 2 ^ (k + 1) = (c : ℝ) / 2 ^ k := by
        have h : (2 : ℝ) ^ k ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      have hhigh : (((2 * c : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = (2 * (c : ℝ) + 1) / 2 ^ (k + 1) := by
        push_cast; ring
      have htop : (((2 * c + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1) = ((c : ℝ) + 1) / 2 ^ k := by
        have h : (2 : ℝ) ^ k ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      have hmid' : (((2 * c + 1 : ℕ) : ℝ)) / 2 ^ (k + 1) = (2 * (c : ℝ) + 1) / 2 ^ (k + 1) := by
        push_cast; ring
      -- the left half carries `l`, the right half carries `r`
      have Hl := ihl (2 * c) (k + 1) (by omega)
      have Hr := ihr (2 * c + 1) (k + 1) hc2
      rw [hlow, hhigh] at Hl
      rw [hmid', htop] at Hr
      rw [TTree.marksAux, hmid]
      -- split the chain at the midpoint
      have := List.IsChain.append_overlap (R := IsStandardDyadicInterval)
        (l₁ := ((c : ℝ) / 2 ^ k) ::
          TTree.marksAux l ((c : ℝ) / 2 ^ k) ((2 * (c : ℝ) + 1) / 2 ^ (k + 1)))
        (l₂ := [(2 * (c : ℝ) + 1) / 2 ^ (k + 1)])
        (l₃ := TTree.marksAux r ((2 * (c : ℝ) + 1) / 2 ^ (k + 1)) (((c : ℝ) + 1) / 2 ^ k)
          ++ [((c : ℝ) + 1) / 2 ^ k])
        (by simpa using Hl) (by simpa using Hr) (by simp)
      simpa using this

end CannonFloydParry

open CannonFloydParry

theorem solution (t : TTree) : IsStandardDyadicPartition t.marks := by
  refine ⟨rfl, ?_, ?_⟩
  · show ((0 : ℝ) :: (t.marksAux 0 1 ++ [1])).getLast? = some 1
    rw [← List.cons_append,
      List.getLast?_append_of_ne_nil _ (by simp : ([(1 : ℝ)] : List ℝ) ≠ [])]
    rfl
  · have h := isChain_marksAux t 0 0 (by norm_num)
    norm_num at h
    simpa [TTree.marks] using h
