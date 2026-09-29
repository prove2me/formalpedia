-- Prove2me | solution 1 for BanditAlgorithm.tsum_chargeStackInterleaving_le_greedy
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T21:10:17.572466+00:00
-- url     : https://prove2.me/submissions/95e3fe88-1dba-47ad-bc77-a3773601abc7

import Definitions.Def_GittinsChargeInterleaving
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

namespace BanditAlgorithm
@[simp] lemma stackPullCountBefore_zero
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) :
    stackPullCountBefore a i 0 = 0 := by
  simp [stackPullCountBefore]

lemma stackPullCountBefore_succ
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) (n : ℕ) :
    stackPullCountBefore a i (n + 1) =
      stackPullCountBefore a i n + if a n = i then 1 else 0 := by
  rw [stackPullCountBefore, stackPullCountBefore,
    Finset.sum_range_succ]

lemma stackPullCountBefore_le_succ
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) (n : ℕ) :
    stackPullCountBefore a i n ≤ stackPullCountBefore a i (n + 1) := by
  rw [stackPullCountBefore_succ]
  omega
theorem sum_chargeStackInterleaving_eq_allocationValue
    {k : ℕ} (H : Fin k → ℕ → ℝ) (a : ℕ → Fin k) :
    ∀ N : ℕ,
      (∑ n ∈ Finset.range N, chargeStackInterleaving H a n) =
        chargeStackAllocationValue H
          (fun i ↦ stackPullCountBefore a i N) := by
  intro N
  induction N with
  | zero => simp [chargeStackAllocationValue]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      classical
      let j : Fin k := a N
      rw [chargeStackAllocationValue, chargeStackAllocationValue]
      let F0 : Fin k → ℝ := fun i ↦
        ∑ u ∈ Finset.range (stackPullCountBefore a i N), H i u
      let F1 : Fin k → ℝ := fun i ↦
        ∑ u ∈ Finset.range (stackPullCountBefore a i (N + 1)), H i u
      have hsplit0 : (∑ i : Fin k, F0 i) =
          F0 j + ∑ i ∈ Finset.univ \ {j}, F0 i := by
        simpa using Finset.sum_eq_add_sum_diff_singleton
          (s := Finset.univ) j F0 (by simp)
      have hsplit1 : (∑ i : Fin k, F1 i) =
          F1 j + ∑ i ∈ Finset.univ \ {j}, F1 i := by
        simpa using Finset.sum_eq_add_sum_diff_singleton
          (s := Finset.univ) j F1 (by simp)
      change (∑ i : Fin k, F0 i) + chargeStackInterleaving H a N =
        ∑ i : Fin k, F1 i
      rw [hsplit0, hsplit1]
      have hj : stackPullCountBefore a j (N + 1) =
          stackPullCountBefore a j N + 1 := by
        simp [stackPullCountBefore_succ, j]
      change F0 j + (∑ i ∈ Finset.univ \ {j}, F0 i) +
          chargeStackInterleaving H a N =
        F1 j + ∑ i ∈ Finset.univ \ {j}, F1 i
      rw [show F1 j = F0 j +
          H j (stackPullCountBefore a j N) by
        dsimp [F0, F1]
        rw [hj, Finset.sum_range_succ]]
      have hother :
          (∑ i ∈ Finset.univ \ {j}, F1 i) =
            ∑ i ∈ Finset.univ \ {j}, F0 i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : a N ≠ i := by
          have hne : i ≠ j := by
            simpa using (Finset.mem_sdiff.1 hi).2
          exact fun h ↦ hne (by simpa [j] using h.symm)
        dsimp [F0, F1]
        simp [stackPullCountBefore_succ, hij]
      rw [hother]
      dsimp [chargeStackInterleaving, j]
      ring

/-- The pull-count vector after `N` rounds has total mass `N`. -/
theorem sum_stackPullCountBefore
    {k : ℕ} (a : ℕ → Fin k) :
    ∀ N : ℕ, ∑ i : Fin k, stackPullCountBefore a i N = N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      simp_rw [stackPullCountBefore_succ]
      rw [Finset.sum_add_distrib, ih]
      have hone : (∑ i : Fin k, if a N = i then 1 else 0) = 1 := by
        classical
        simp
      rw [hone]
lemma antitone_advanceChargeStack
    {k : ℕ} {H : Fin k → ℕ → ℝ}
    (hH : ∀ i, Antitone (H i)) (j i : Fin k) :
    Antitone (advanceChargeStack H j i) := by
  intro u v huv
  by_cases hij : i = j
  · subst i
    simp only [advanceChargeStack, if_pos]
    exact hH j (Nat.add_le_add_right huv 1)
  · simp only [advanceChargeStack, if_neg hij]
    exact hH i huv

/-- Pull counts after deleting the first global action. -/
lemma stackPullCountBefore_tail
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) :
    ∀ n : ℕ,
      stackPullCountBefore a i (n + 1) =
        stackPullCountBefore (fun t ↦ a (t + 1)) i n +
          if a 0 = i then 1 else 0 := by
  intro n
  simp only [stackPullCountBefore]
  rw [Finset.sum_range_succ']

/-- Deleting the first selected head turns the remaining interleaving into an
interleaving of the advanced stack family. -/
lemma chargeStackInterleaving_tail
    {k : ℕ} (H : Fin k → ℕ → ℝ) (a : ℕ → Fin k)
    (n : ℕ) :
    chargeStackInterleaving H a (n + 1) =
      chargeStackInterleaving
        (advanceChargeStack H (a 0)) (fun t ↦ a (t + 1)) n := by
  rw [chargeStackInterleaving, chargeStackInterleaving]
  rw [stackPullCountBefore_tail]
  by_cases h : a (n + 1) = a 0
  · rw [if_pos (Eq.symm h)]
    simp only [advanceChargeStack, h, if_pos]
  · have h' : a 0 ≠ a (n + 1) := Ne.symm h
    rw [if_neg h']
    simp only [advanceChargeStack, h, if_false, Nat.add_zero]

/-- Greediness is preserved after deleting the first greedy action and
advancing the selected stack. -/
lemma isGreedyChargeStackInterleaving_tail
    {k : ℕ} {H : Fin k → ℕ → ℝ} {a : ℕ → Fin k}
    (ha : IsGreedyChargeStackInterleaving H a) :
    IsGreedyChargeStackInterleaving
      (advanceChargeStack H (a 0)) (fun t ↦ a (t + 1)) := by
  intro n i
  have hmain := ha (n + 1) i
  rw [stackPullCountBefore_tail, stackPullCountBefore_tail] at hmain
  by_cases hi : i = a 0
  · subst i
    by_cases ha0 : a (n + 1) = a 0
    · have ha0' : a 0 = a (n + 1) := ha0.symm
      simpa only [advanceChargeStack, if_pos rfl, if_true, eq_self_iff_true, if_pos ha0,
        if_pos ha0'] using hmain
    · have ha0' : a 0 ≠ a (n + 1) := Ne.symm ha0
      simpa only [advanceChargeStack, if_pos rfl, if_true, eq_self_iff_true, if_neg ha0,
        if_neg ha0', Nat.add_zero] using hmain
  · by_cases ha0 : a (n + 1) = a 0
    · have hi' : a 0 ≠ i := fun h ↦ hi h.symm
      have ha0' : a 0 = a (n + 1) := ha0.symm
      simpa only [advanceChargeStack, if_neg hi, if_neg hi',
        if_pos ha0, if_pos ha0', Nat.add_zero] using hmain
    · have hi' : a 0 ≠ i := fun h ↦ hi h.symm
      have ha0' : a 0 ≠ a (n + 1) := Ne.symm ha0
      simpa only [advanceChargeStack, if_neg hi, if_neg hi',
        if_neg ha0, if_neg ha0', Nat.add_zero] using hmain

lemma sum_decrementChargeAllocation
    {k : ℕ} (m : Fin k → ℕ) (i : Fin k) (hi : 0 < m i) :
    (∑ j : Fin k, decrementChargeAllocation m i j) + 1 =
      ∑ j : Fin k, m j := by
  classical
  let d : Fin k → ℕ := decrementChargeAllocation m i
  have hsplitM : (∑ j : Fin k, m j) =
      m i + ∑ j ∈ Finset.univ \ {i}, m j := by
    rw [Finset.sdiff_singleton_eq_erase]
    exact (Finset.add_sum_erase Finset.univ m (Finset.mem_univ i)).symm
  have hsplitD : (∑ j : Fin k, d j) =
      d i + ∑ j ∈ Finset.univ \ {i}, d j := by
    rw [Finset.sdiff_singleton_eq_erase]
    exact (Finset.add_sum_erase Finset.univ d (Finset.mem_univ i)).symm
  rw [hsplitM, hsplitD]
  have hrest : (∑ j ∈ Finset.univ \ {i}, d j) =
      ∑ j ∈ Finset.univ \ {i}, m j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by
      simpa using (Finset.mem_sdiff.1 hj).2
    simp [d, decrementChargeAllocation, hji]
  rw [hrest]
  dsimp [d, decrementChargeAllocation]
  simp only [if_pos]
  omega

lemma chargeStackAllocationValue_decrement_selected
    {k : ℕ} (H : Fin k → ℕ → ℝ) (m : Fin k → ℕ)
    (j : Fin k) (hj : 0 < m j) :
    chargeStackAllocationValue H m =
      H j 0 + chargeStackAllocationValue
        (advanceChargeStack H j) (decrementChargeAllocation m j) := by
  classical
  rw [chargeStackAllocationValue, chargeStackAllocationValue]
  let F : Fin k → ℝ := fun i ↦
    ∑ u ∈ Finset.range (m i), H i u
  let G : Fin k → ℝ := fun i ↦
    ∑ u ∈ Finset.range (decrementChargeAllocation m j i),
      advanceChargeStack H j i u
  have hsplitF : (∑ i : Fin k, F i) =
      F j + ∑ i ∈ Finset.univ \ {j}, F i := by
    simpa using Finset.sum_eq_add_sum_diff_singleton
      (s := Finset.univ) j F (by simp)
  have hsplitG : (∑ i : Fin k, G i) =
      G j + ∑ i ∈ Finset.univ \ {j}, G i := by
    simpa using Finset.sum_eq_add_sum_diff_singleton
      (s := Finset.univ) j G (by simp)
  change (∑ i : Fin k, F i) = H j 0 + ∑ i : Fin k, G i
  rw [hsplitF, hsplitG]
  have hFj : F j = H j 0 + G j := by
    have hm : m j = (m j - 1) + 1 := (Nat.sub_add_cancel hj).symm
    dsimp [F, G, decrementChargeAllocation, advanceChargeStack]
    simp only [if_pos]
    rw [hm, Finset.sum_range_succ']
    rw [show m j - 1 + 1 - 1 = m j - 1 by omega]
    ring
  have hrest : (∑ i ∈ Finset.univ \ {j}, F i) =
      ∑ i ∈ Finset.univ \ {j}, G i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := by
      simpa using (Finset.mem_sdiff.1 hi).2
    simp [F, G, decrementChargeAllocation, advanceChargeStack, hij]
  rw [hFj, hrest]
  ring

lemma chargeStackAllocationValue_decrement_other
    {k : ℕ} (H : Fin k → ℕ → ℝ) (m : Fin k → ℕ)
    (j i : Fin k) (hj : m j = 0) (hi : 0 < m i) :
    chargeStackAllocationValue H m =
      H i (m i - 1) + chargeStackAllocationValue
        (advanceChargeStack H j) (decrementChargeAllocation m i) := by
  classical
  have hij : i ≠ j := by
    intro h
    subst i
    omega
  rw [chargeStackAllocationValue, chargeStackAllocationValue]
  let F : Fin k → ℝ := fun l ↦
    ∑ u ∈ Finset.range (m l), H l u
  let G : Fin k → ℝ := fun l ↦
    ∑ u ∈ Finset.range (decrementChargeAllocation m i l),
      advanceChargeStack H j l u
  have hsplitF : (∑ l : Fin k, F l) =
      F i + ∑ l ∈ Finset.univ \ {i}, F l := by
    simpa using Finset.sum_eq_add_sum_diff_singleton
      (s := Finset.univ) i F (by simp)
  have hsplitG : (∑ l : Fin k, G l) =
      G i + ∑ l ∈ Finset.univ \ {i}, G l := by
    simpa using Finset.sum_eq_add_sum_diff_singleton
      (s := Finset.univ) i G (by simp)
  change (∑ l : Fin k, F l) = H i (m i - 1) + ∑ l : Fin k, G l
  rw [hsplitF, hsplitG]
  have hFi : F i = G i + H i (m i - 1) := by
    have hm : m i = (m i - 1) + 1 := (Nat.sub_add_cancel hi).symm
    dsimp [F, G, decrementChargeAllocation, advanceChargeStack]
    simp only [if_pos, if_neg hij]
    rw [hm, Finset.sum_range_succ]
    rw [show m i - 1 + 1 - 1 = m i - 1 by omega]
  have hrest : (∑ l ∈ Finset.univ \ {i}, F l) =
      ∑ l ∈ Finset.univ \ {i}, G l := by
    apply Finset.sum_congr rfl
    intro l hl
    have hli : l ≠ i := by
      simpa using (Finset.mem_sdiff.1 hl).2
    by_cases hlj : l = j
    · subst l
      simp [F, G, decrementChargeAllocation, advanceChargeStack,
        hli, hj]
    · simp [F, G, decrementChargeAllocation, advanceChargeStack,
        hli, hlj]
  rw [hFi, hrest]
  ring

/-- For decreasing stacks, the greedy interleaving maximizes every
undiscounted prefix sum among all allocations of the same total size. -/
theorem chargeStackAllocationValue_le_greedy_prefix
    {k : ℕ} : ∀ N : ℕ,
    ∀ (H : Fin k → ℕ → ℝ) (a : ℕ → Fin k),
      (∀ i, Antitone (H i)) →
      IsGreedyChargeStackInterleaving H a →
      ∀ m : Fin k → ℕ, (∑ i : Fin k, m i) = N →
        chargeStackAllocationValue H m ≤
          ∑ n ∈ Finset.range N, chargeStackInterleaving H a n := by
  intro N
  induction N with
  | zero =>
      intro H a hH ha m hm
      have hm0 : ∀ i : Fin k, m i = 0 := by
        intro i
        have hle : m i ≤ ∑ j : Fin k, m j :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        omega
      simp [chargeStackAllocationValue, hm0]
  | succ N ih =>
      intro H a hH ha m hm
      let j : Fin k := a 0
      let H' := advanceChargeStack H j
      let a' : ℕ → Fin k := fun n ↦ a (n + 1)
      have hH' : ∀ i, Antitone (H' i) :=
        fun i ↦ antitone_advanceChargeStack hH j i
      have ha' : IsGreedyChargeStackInterleaving H' a' := by
        exact isGreedyChargeStackInterleaving_tail ha
      have hhead : ∀ i : Fin k, H i 0 ≤ H j 0 := by
        intro i
        simpa [j] using ha 0 i
      have htailSum :
          (∑ n ∈ Finset.range N, chargeStackInterleaving H' a' n) =
            ∑ n ∈ Finset.range N,
              chargeStackInterleaving H a (n + 1) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (chargeStackInterleaving_tail H a n).symm
      by_cases hmj : 0 < m j
      · let m' := decrementChargeAllocation m j
        have hm' : (∑ i : Fin k, m' i) = N := by
          have hd := sum_decrementChargeAllocation m j hmj
          dsimp [m'] at hd ⊢
          omega
        have hih := ih H' a' hH' ha' m' hm'
        have halloc := chargeStackAllocationValue_decrement_selected H m j hmj
        rw [halloc]
        calc
          H j 0 + chargeStackAllocationValue H' m' ≤
              H j 0 + ∑ n ∈ Finset.range N,
                chargeStackInterleaving H' a' n := by gcongr
          _ = ∑ n ∈ Finset.range (N + 1),
                chargeStackInterleaving H a n := by
            rw [Finset.sum_range_succ']
            rw [htailSum]
            rw [show chargeStackInterleaving H a 0 = H j 0 by
              simp [chargeStackInterleaving, j]]
            ring

      · have hmj0 : m j = 0 := Nat.eq_zero_of_not_pos hmj
        have hsumne : (∑ i : Fin k, m i) ≠ 0 := by omega
        obtain ⟨i, hiuniv, hi0⟩ :=
          Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) hsumne
        have hi : 0 < m i := Nat.pos_of_ne_zero hi0
        let m' := decrementChargeAllocation m i
        have hm' : (∑ l : Fin k, m' l) = N := by
          have hd := sum_decrementChargeAllocation m i hi
          dsimp [m'] at hd ⊢
          omega
        have hih := ih H' a' hH' ha' m' hm'
        have halloc := chargeStackAllocationValue_decrement_other
          H m j i hmj0 hi
        have hlast : H i (m i - 1) ≤ H j 0 :=
          (hH i (Nat.zero_le _)).trans (hhead i)
        rw [halloc]
        calc
          H i (m i - 1) + chargeStackAllocationValue H' m' ≤
              H j 0 + ∑ n ∈ Finset.range N,
                chargeStackInterleaving H' a' n := by
            exact add_le_add hlast hih
          _ = ∑ n ∈ Finset.range (N + 1),
                chargeStackInterleaving H a n := by
            rw [Finset.sum_range_succ']
            rw [htailSum]
            rw [show chargeStackInterleaving H a 0 = H j 0 by
              simp [chargeStackInterleaving, j]]
            ring

/-- Greedy interleaving dominates the undiscounted sum of every finite prefix
of every competing interleaving. -/
theorem sum_chargeStackInterleaving_le_greedy
    {k : ℕ} {H : Fin k → ℕ → ℝ} {astar : ℕ → Fin k}
    (hH : ∀ i, Antitone (H i))
    (hastar : IsGreedyChargeStackInterleaving H astar)
    (a : ℕ → Fin k) (N : ℕ) :
    (∑ n ∈ Finset.range N, chargeStackInterleaving H a n) ≤
      ∑ n ∈ Finset.range N, chargeStackInterleaving H astar n := by
  rw [sum_chargeStackInterleaving_eq_allocationValue]
  exact chargeStackAllocationValue_le_greedy_prefix N H astar
    hH hastar (fun i ↦ stackPullCountBefore a i N)
      (sum_stackPullCountBefore a N)

private lemma finite_abel_discounted_sum
    (α : ℝ) (z : ℕ → ℝ) : ∀ N : ℕ,
    (∑ n ∈ Finset.range (N + 1), α ^ n * z n) =
      α ^ N * (∑ t ∈ Finset.range (N + 1), z t) +
        ∑ n ∈ Finset.range N,
          (α ^ n - α ^ (n + 1)) *
            (∑ t ∈ Finset.range (n + 1), z t) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ n ∈ Finset.range (N + 1 + 1), α ^ n * z n) =
            (∑ n ∈ Finset.range (N + 1), α ^ n * z n) +
              α ^ (N + 1) * z (N + 1) := by
                rw [Finset.sum_range_succ]
        _ = (α ^ N * (∑ t ∈ Finset.range (N + 1), z t) +
              ∑ n ∈ Finset.range N,
                (α ^ n - α ^ (n + 1)) *
                  (∑ t ∈ Finset.range (n + 1), z t)) +
              α ^ (N + 1) * z (N + 1) := by rw [ih]
        _ = α ^ (N + 1) *
              (∑ t ∈ Finset.range (N + 1 + 1), z t) +
            ∑ n ∈ Finset.range (N + 1),
              (α ^ n - α ^ (n + 1)) *
                (∑ t ∈ Finset.range (n + 1), z t) := by
                  simp only [Finset.sum_range_succ, pow_succ]
                  ring

/-- Finite Hardy--Littlewood/Abel form of Lemma 35.10: for geometric weights,
the greedy interleaving of decreasing stacks dominates every competing
interleaving on every finite horizon. -/
theorem discounted_sum_chargeStackInterleaving_le_greedy
    {k : ℕ} {H : Fin k → ℕ → ℝ} {astar : ℕ → Fin k}
    (hH : ∀ i, Antitone (H i))
    (hastar : IsGreedyChargeStackInterleaving H astar)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (a : ℕ → Fin k) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        α ^ n * chargeStackInterleaving H a n) ≤
      ∑ n ∈ Finset.range N,
        α ^ n * chargeStackInterleaving H astar n := by
  cases N with
  | zero => simp
  | succ N =>
      let za : ℕ → ℝ := chargeStackInterleaving H a
      let zg : ℕ → ℝ := chargeStackInterleaving H astar
      rw [finite_abel_discounted_sum α za N,
        finite_abel_discounted_sum α zg N]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hα0 N)
        exact sum_chargeStackInterleaving_le_greedy
          hH hastar a (N + 1)
      · apply Finset.sum_le_sum
        intro n hn
        apply mul_le_mul_of_nonneg_left
        · exact sum_chargeStackInterleaving_le_greedy
            hH hastar a (n + 1)
        · rw [pow_succ]
          exact sub_nonneg.2
            (mul_le_of_le_one_right (pow_nonneg hα0 n) hα1)

end BanditAlgorithm

open BanditAlgorithm

/-- Infinite-horizon Hardy--Littlewood inequality (Exercise 35.9 in the
source): provided both discounted interleavings are summable, the greedy
interleaving maximizes their discounted sum. -/
theorem solution
    {k : ℕ} {H : Fin k → ℕ → ℝ} {astar : ℕ → Fin k}
    (hH : ∀ i, Antitone (H i))
    (hastar : IsGreedyChargeStackInterleaving H astar)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (a : ℕ → Fin k)
    (hsuma : Summable
      (fun n ↦ α ^ n * chargeStackInterleaving H a n))
    (hsumg : Summable
      (fun n ↦ α ^ n * chargeStackInterleaving H astar n)) :
    (∑' n : ℕ, α ^ n * chargeStackInterleaving H a n) ≤
      ∑' n : ℕ, α ^ n * chargeStackInterleaving H astar n := by
  exact le_of_tendsto_of_tendsto'
    hsuma.hasSum.tendsto_sum_nat hsumg.hasSum.tendsto_sum_nat
      (fun N ↦ discounted_sum_chargeStackInterleaving_le_greedy
        hH hastar hα0 hα1 a N)
