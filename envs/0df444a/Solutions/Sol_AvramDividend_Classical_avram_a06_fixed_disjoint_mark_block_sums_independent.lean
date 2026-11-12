-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_fixed_disjoint_mark_block_sums_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:43:06.348742+00:00
-- url     : https://prove2.me/submissions/71a5308d-102d-4ceb-9db1-d8acb18369ca

import Mathlib
import Theorems.Thm_levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
noncomputable section

/-- Independence of sums of disjoint deterministic blocks of independent marks. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (m : Fin (n + 1) → ℕ) (hm : Monotone m)
    (Y : ℕ → Ω → ℝ)
    (hY : ∀ k, Measurable (Y k)) (hIndep : iIndepFun Y P) :
    iIndepFun (fun (i : Fin n) ω =>
      ∑ k ∈ Finset.Ico (m i.castSucc) (m i.succ), Y k ω) P := by
  classical
  let S : Fin n → Finset ℕ :=
    fun i => Finset.Ico (m i.castSucc) (m i.succ)
  have hS : Pairwise (Function.onFun Disjoint
      (fun i : Fin n => (S i : Set ℕ))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro k hik hjk
    have hi := Finset.mem_Ico.mp hik
    have hj := Finset.mem_Ico.mp hjk
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hle : m i.succ ≤ m j.castSucc := hm (by
        apply Fin.le_iff_val_le_val.mpr
        simpa only [Fin.val_succ, Fin.val_castSucc] using
          (Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hij)))
      omega
    · have hle : m j.succ ≤ m i.castSucc := hm (by
        apply Fin.le_iff_val_le_val.mpr
        simpa only [Fin.val_succ, Fin.val_castSucc] using
          (Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hji)))
      omega
  have hBlocks := levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
    hY hIndep hS
  let g : (i : Fin n) → ({k : ℕ // k ∈ S i} → ℝ) → ℝ :=
    fun i z => ∑ k : S i, z k
  have hg : ∀ i, Measurable (g i) := by
    intro i
    dsimp [g]
    fun_prop
  have hComp := hBlocks.comp g hg
  convert hComp using 1
  funext i ω
  simp only [Function.comp_apply, g, S]
  exact (Finset.sum_attach _ _).symm
