-- Prove2me | solution 1 for FBMSP.theorem2_computing_segmentation
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:23:23.354268+00:00
-- url     : https://prove2.me/submissions/4034e044-6a95-4ea7-889a-6e8dc05c506a

import Definitions.Def_FBMSP_Model
import Theorems.Thm_FBMSP_dp_correctness
import Theorems.Thm_FBMSP_oracle_operation_bound
import Theorems.Thm_FBMSP_lemma2b_finite_menu_intervals

noncomputable section

open scoped BigOperators
open FBMSP MeasureTheory Set

namespace FBMSP

private theorem exists_monotone_assignment_of_cuts {n k : ℕ} (hk : 1 ≤ k)
    {c : Fin (k + 1) → ℕ} (hc : ValidCuts n k c) :
    ∃ a : Fin n → Fin k, RealizesCuts a c ∧ Monotone a := by
  classical
  cases k with
  | zero => omega
  | succ k =>
    let S (i : Fin n) : Finset (Fin (k + 1)) :=
      Finset.univ.filter (fun j => i.val < c j.succ)
    have hs (i : Fin n) : (S i).Nonempty := by
      refine ⟨Fin.last k, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      change i.val < c (Fin.last (k + 1))
      rw [hc.2.2]
      exact i.isLt
    let a : Fin n → Fin (k + 1) := fun i => (S i).min' (hs i)
    have hupper (i : Fin n) : i.val < c (a i).succ :=
      (Finset.mem_filter.mp (Finset.min'_mem (S i) (hs i))).2
    refine ⟨a, ?_, ?_⟩
    · intro i
      refine ⟨?_, hupper i⟩
      by_cases hzero : a i = 0
      · rw [hzero]
        change c 0 ≤ i.val
        rw [hc.2.1]
        exact Nat.zero_le _
      have hpos : 0 < (a i).val := by
        have hne : (a i).val ≠ 0 := by
          intro heq
          apply hzero
          exact Fin.ext heq
        omega
      let j : Fin (k + 1) := ⟨(a i).val - 1, by have := (a i).isLt; omega⟩
      have hjlt : j < a i := by
        change (a i).val - 1 < (a i).val
        omega
      have hjsucc : j.succ = (a i).castSucc := by
        apply Fin.ext
        change (a i).val - 1 + 1 = (a i).val
        omega
      by_contra h
      have hjmem : j ∈ S i := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hjsucc]
        exact lt_of_not_ge h
      have hmin : a i ≤ j := Finset.min'_le (S i) j hjmem
      exact (not_le_of_gt hjlt) hmin
    · intro i i' hii'
      have hmem : a i' ∈ S i := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_le_of_lt (show i.val ≤ i'.val from hii') (hupper i')
      exact Finset.min'_le (S i) (a i') hmem

private theorem exists_cuts_of_monotone_assignment {n k : ℕ} (a : Fin n → Fin k)
    (ha : Monotone a) :
    ∃ c : Fin (k + 1) → ℕ, ValidCuts n k c ∧ RealizesCuts a c := by
  classical
  let c : Fin (k + 1) → ℕ := fun j =>
    (Finset.univ.filter (fun i : Fin n => (a i).val < j.val)).card
  refine ⟨c, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro j l hjl
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact lt_of_lt_of_le hi (show j.val ≤ l.val from hjl)
  · simp [c]
  · have hfilter : Finset.univ.filter (fun i : Fin n => (a i).val < k) =
        Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i hi
      exact (a i).isLt
    simp only [c, Fin.val_last, hfilter, Finset.card_univ, Fintype.card_fin]
  · intro i
    change (Finset.univ.filter (fun j : Fin n => (a j).val < (a i).val)).card ≤ i.val ∧
      i.val < (Finset.univ.filter (fun j : Fin n => (a j).val < (a i).val + 1)).card
    constructor
    · calc
        _ ≤ (Finset.Iio i).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          apply Finset.mem_Iio.mpr
          by_contra hji
          have hij : i ≤ j := le_of_not_gt hji
          have hm : (a i).val ≤ (a j).val := ha hij
          omega
        _ = i.val := Fin.card_Iio i
    · have hsub : Finset.Iic i ⊆
          Finset.univ.filter (fun j : Fin n => (a j).val < (a i).val + 1) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Nat.lt_succ_of_le (show (a j).val ≤ (a i).val from
          ha (Finset.mem_Iic.mp hj))
      have hcard := Finset.card_le_card hsub
      rw [Fin.card_Iic] at hcard
      omega

private theorem realizesCuts_iff_assignment_eq {n k : ℕ} {a : Fin n → Fin k}
    {c : Fin (k + 1) → ℕ} (hc : ValidCuts n k c) (ha : RealizesCuts a c)
    (i : Fin n) (j : Fin k) :
    a i = j ↔ c j.castSucc ≤ i.val ∧ i.val < c j.succ := by
  constructor
  · intro h
    simpa only [h] using ha i
  · intro hj
    by_contra hne
    obtain hlt | hgt := lt_or_gt_of_ne hne
    · have hidx : (a i).succ ≤ j.castSucc := by
        change (a i).val + 1 ≤ j.val
        exact Nat.succ_le_of_lt hlt
      have hcut := hc.1 hidx
      have hi := ha i
      omega
    · have hidx : j.succ ≤ (a i).castSucc := by
        change j.val + 1 ≤ (a i).val
        exact Nat.succ_le_of_lt hgt
      have hcut := hc.1 hidx
      have hi := ha i
      omega

private theorem finitePolicyRevenue_eq_sum_blockRevenue {n k : ℕ} (η : Measure ℝ)
    (μ w : Fin n → ℝ) {a : Fin n → Fin k} {c : Fin (k + 1) → ℕ}
    (hc : ValidCuts n k c) (ha : RealizesCuts a c) (p : Fin k → ℝ) :
    finitePolicyRevenue η μ w a p =
      ∑ j : Fin k, blockRevenue η μ w (c j.castSucc) (c j.succ) (p j) := by
  classical
  unfold finitePolicyRevenue
  rw [← Finset.sum_fiberwise Finset.univ a
    (fun i => w i * postedRevenue η (μ i) (p (a i)))]
  apply Finset.sum_congr rfl
  intro j hj
  unfold blockRevenue
  have hfilter : Finset.univ.filter (fun i : Fin n => a i = j) =
      Finset.univ.filter (fun i : Fin n => c j.castSucc ≤ i.val ∧ i.val < c j.succ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact realizesCuts_iff_assignment_eq hc ha i j
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro i hi
  have haji := (realizesCuts_iff_assignment_eq hc ha i j).2 (Finset.mem_filter.mp hi).2
  rw [haji]

end FBMSP

private theorem monotone_snoc_cuts {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (b : ℕ) (hb : c (Fin.last r) ≤ b) :
    Monotone (Fin.snoc c b) := by
  intro i j hij
  cases i using Fin.lastCases with
  | last =>
      have hj : j = Fin.last (r + 1) := le_antisymm (Fin.le_last j) hij
      subst j
      exact le_rfl
  | cast i =>
      cases j using Fin.lastCases with
      | last => simpa using le_trans (hc (Fin.le_last i)) hb
      | cast j => simpa using hc hij

private theorem intervalValue_has_cuts {W : ℕ → ℕ → ℝ}
    {k a n : ℕ} {v : ℝ} (hv : IntervalValue W k a n v) :
    ∃ c : Fin (k + 2) → ℕ,
      Monotone c ∧ c 0 = a ∧ c (Fin.last (k + 1)) = a + n ∧
        (∑ j : Fin (k + 1), W (c j.castSucc) (c j.succ)) = v := by
  induction hv with
  | one a n =>
      refine ⟨![a, a + n], ?_, by simp, by simp, by simp⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  | @append k a n i v hi hv ih =>
      obtain ⟨c, hc, hzero, hlast, hsum⟩ := ih
      refine ⟨Fin.snoc c (a + n),
        monotone_snoc_cuts c hc (a + n) (by omega), ?_, ?_, ?_⟩
      · simpa using hzero
      · simp
      · rw [Fin.sum_univ_castSucc]
        simpa only [← Fin.castSucc_succ, Fin.snoc_castSucc,
          Fin.succ_last, Fin.snoc_last, hlast, hsum]

private theorem cuts_have_intervalValue (W : ℕ → ℕ → ℝ)
    (k a n : ℕ) (c : Fin (k + 2) → ℕ) (hc : Monotone c)
    (hzero : c 0 = a) (hlast : c (Fin.last (k + 1)) = a + n) :
    IntervalValue W k a n
      (∑ j : Fin (k + 1), W (c j.castSucc) (c j.succ)) := by
  induction k generalizing n with
  | zero =>
      have hlast' : c 1 = a + n := hlast
      simpa [hzero, hlast'] using IntervalValue.one (W := W) a n
  | succ k ih =>
      let c' : Fin (k + 2) → ℕ := fun j => c j.castSucc
      let i : ℕ := c' (Fin.last (k + 1)) - a
      have hleft : a ≤ c' (Fin.last (k + 1)) := by
        rw [← hzero]
        exact hc (Fin.zero_le _)
      have hright : c' (Fin.last (k + 1)) ≤ a + n := by
        rw [← hlast]
        exact hc (Fin.le_last _)
      have hci : c' (Fin.last (k + 1)) = a + i := by dsimp [i]; omega
      have hin : i ≤ n := by dsimp [i]; omega
      have hc' : Monotone c' := fun x y hxy => hc hxy
      have hz' : c' 0 = a := by simpa [c'] using hzero
      have hv := ih i c' hc' hz' hci
      have hv' := IntervalValue.append (W := W) hin hv
      rw [Fin.sum_univ_castSucc]
      convert hv' using 1 <;>
        simp only [c', ← Fin.castSucc_succ, Fin.succ_last, hlast, ← hci]

private theorem cuts_score_le_dp (W : ℕ → ℕ → ℝ) {n k : ℕ}
    (c : Fin (k + 2) → ℕ) (hc : ValidCuts n (k + 1) c) :
    (∑ j : Fin (k + 1), W (c j.castSucc) (c j.succ)) ≤
      intervalDP W k 0 n := by
  exact (dp_correctness W k 0 n).2 _
    (cuts_have_intervalValue W k 0 n c hc.1 hc.2.1 (by simpa using hc.2.2))

private theorem monotone_policy_le_dp {n k : ℕ} (η : MeasureTheory.Measure ℝ)
    (μ w : Fin n → ℝ) (o : ℕ → ℕ → ℝ) (ho : BlockOracle η μ w o)
    (a : Fin n → Fin (k + 1)) (ha : Monotone a)
    (p : Fin (k + 1) → ℝ) (hp : ∀ j, 0 ≤ p j) :
    finitePolicyRevenue η μ w a p ≤ intervalDP (oracleScore η μ w o) k 0 n := by
  obtain ⟨c, hc, hac⟩ := exists_cuts_of_monotone_assignment a ha
  rw [finitePolicyRevenue_eq_sum_blockRevenue η μ w hc hac p]
  calc
    (∑ j : Fin (k + 1), blockRevenue η μ w (c j.castSucc) (c j.succ) (p j))
        ≤ ∑ j : Fin (k + 1), oracleScore η μ w o (c j.castSucc) (c j.succ) := by
      apply Finset.sum_le_sum
      intro j _
      apply (ho (c j.castSucc) (c j.succ) ?_ ?_).2 (p j) (hp j)
      · exact hc.1 (show j.castSucc ≤ j.succ from Nat.le_succ j.val)
      · calc
          c j.succ ≤ c (Fin.last (k + 1)) := hc.1 (Fin.le_last _)
          _ = n := hc.2.2
    _ ≤ intervalDP (oracleScore η μ w o) k 0 n :=
      cuts_score_le_dp (oracleScore η μ w o) c hc

theorem solution
    {n k : ℕ} (hk : 1 ≤ k) (η : MeasureTheory.Measure ℝ)
    (hη : ValidNoise η) (hMHR : HasMHR η)
    (μ w : Fin n → ℝ) (hMarket : ValidFiniteMarket μ w)
    (o : ℕ → ℕ → ℝ) (ho : BlockOracle η μ w o)
    (charge : ℕ → ℕ → ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hCost : ∀ a b, a < b → b ≤ n → charge a b ≤ m) :
    ∃ (c : Fin (k + 1) → ℕ) (a : Fin n → Fin k),
      ValidCuts n k c ∧ RealizesCuts a c ∧ Monotone a ∧
      finitePolicyRevenue η μ w a
        (fun j => o (c j.castSucc) (c j.succ)) =
          intervalDP (oracleScore η μ w o) (k - 1) 0 n ∧
      (∀ (a' : Fin n → Fin k) (p' : Fin k → ℝ),
        (∀ j, 0 ≤ p' j) →
        finitePolicyRevenue η μ w a' p' ≤
          finitePolicyRevenue η μ w a
            (fun j => o (c j.castSucc) (c j.succ))) ∧
      segmentationWork charge k n ≤ 5 * (n * n) * (k + m) := by
  classical
  cases k with
  | zero => omega
  | succ k =>
      obtain ⟨c, hc, hzero, hlast, hsum⟩ :=
        intervalValue_has_cuts (dp_correctness (oracleScore η μ w o) k 0 n).1
      have hcuts : ValidCuts n (k + 1) c := ⟨hc, hzero, by simpa using hlast⟩
      obtain ⟨a, hac, ha⟩ := exists_monotone_assignment_of_cuts hk hcuts
      have hrev : finitePolicyRevenue η μ w a
          (fun j => o (c j.castSucc) (c j.succ)) =
            intervalDP (oracleScore η μ w o) k 0 n := by
        rw [finitePolicyRevenue_eq_sum_blockRevenue η μ w hcuts hac]
        exact hsum
      refine ⟨c, a, hcuts, hac, ha, hrev, ?_, ?_⟩
      · intro a' p' hp'
        let σ : Equiv.Perm (Fin (k + 1)) := Tuple.sort p'
        let p : Fin (k + 1) → ℝ := p' ∘ σ
        have hpmono : Monotone p := Tuple.monotone_sort p'
        have hpnonneg : ∀ j, 0 ≤ p j := fun j => hp' (σ j)
        obtain ⟨b, hb, _, _, hdom⟩ :=
          lemma2b_finite_menu_intervals η hη hMHR μ w hMarket
            (Nat.succ_pos k) p hpmono hpnonneg
        have hperm : finitePolicyRevenue η μ w a' p' =
            finitePolicyRevenue η μ w (fun i => σ.symm (a' i)) p := by
          simp [finitePolicyRevenue, p]
        calc
          finitePolicyRevenue η μ w a' p' ≤ finitePolicyRevenue η μ w b p := by
            rw [hperm]
            exact hdom _
          _ ≤ intervalDP (oracleScore η μ w o) k 0 n :=
            monotone_policy_le_dp η μ w o ho b hb p hpnonneg
          _ = finitePolicyRevenue η μ w a
              (fun j => o (c j.castSucc) (c j.succ)) := hrev.symm
      · exact (oracle_operation_bound n (k + 1) m hMarket.1 hk charge hCost).2

