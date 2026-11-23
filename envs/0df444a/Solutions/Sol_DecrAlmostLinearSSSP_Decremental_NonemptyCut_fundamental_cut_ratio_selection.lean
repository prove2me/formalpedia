-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.NonemptyCut.fundamental_cut_ratio_selection
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:39:13.616314+00:00
-- url     : https://prove2.me/submissions/2b5cb9f6-b87a-4d97-85e3-9814406a6b54

import Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

open DecrAlmostLinearSSSP.Decremental

/-- A weighted decomposition of a direction into fundamental cuts has a cut whose
ratio is no larger than the ratio of the direction. -/
theorem solution {n k ι : ℕ}
    (g : Physical n k) (w : Fin ι → ℝ) (C : Fin ι → Finset (Fin n))
    (x : Fin n → ℝ) (hu : ∀ e ∈ g.active, 0 ≤ g.u e)
    (hw : ∀ i, 0 ≤ w i)
    (hpos : ∀ i, 0 < w i → 0 < cutCapacity g (C i))
    (hdot : dot g.gamma x = ∑ i, w i * cutDemand g (C i))
    (hnorm : physicalNorm g x = ∑ i, w i * cutCapacity g (C i))
    (hnormpos : 0 < physicalNorm g x) :
    ∃ i, 0 < w i ∧ 0 < cutCapacity g (C i) ∧
      cutDemand g (C i) / cutCapacity g (C i) ≤
        dot g.gamma x / physicalNorm g x := by
  classical
  have hcap : ∀ i, 0 ≤ cutCapacity g (C i) := by
    intro i
    unfold cutCapacity
    apply Finset.sum_nonneg
    intro e he
    split_ifs
    · exact hu e he
    · exact le_rfl
  have hB : 0 < ∑ i, w i * cutCapacity g (C i) := by
    rwa [← hnorm]
  have hex : ∃ i, 0 < w i := by
    by_contra hn
    push_neg at hn
    have hz : ∀ i, w i = 0 := by
      intro i
      exact le_antisymm (hn i) (hw i)
    simp [hz] at hB
  obtain ⟨j, hwj⟩ := hex
  by_contra hn
  push_neg at hn
  have hstrict : ∀ i, 0 < w i →
      dot g.gamma x / physicalNorm g x * (w i * cutCapacity g (C i)) <
        w i * cutDemand g (C i) := by
    intro i hwi
    have hci := hpos i hwi
    have hr := hn i hwi hci
    have hm := mul_lt_mul_of_pos_right hr (mul_pos hwi hci)
    have heq : cutDemand g (C i) / cutCapacity g (C i) *
        (w i * cutCapacity g (C i)) = w i * cutDemand g (C i) := by
      field_simp [ne_of_gt hci]
    rwa [heq] at hm
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin ι)),
      dot g.gamma x / physicalNorm g x * (w i * cutCapacity g (C i)) ≤
        w i * cutDemand g (C i) := by
    intro i hi
    by_cases hwi : 0 < w i
    · exact (hstrict i hwi).le
    · have hwi0 : w i = 0 := le_antisymm (le_of_not_gt hwi) (hw i)
      simp [hwi0]
  have hs : (∑ i, dot g.gamma x / physicalNorm g x *
      (w i * cutCapacity g (C i))) < ∑ i, w i * cutDemand g (C i) := by
    exact Finset.sum_lt_sum hle ⟨j, Finset.mem_univ j, hstrict j hwj⟩
  rw [← Finset.mul_sum, ← hnorm, ← hdot] at hs
  have hcancel : dot g.gamma x / physicalNorm g x * physicalNorm g x =
      dot g.gamma x := div_mul_cancel₀ _ (ne_of_gt hnormpos)
  rw [hcancel] at hs
  exact (lt_irrefl _ hs)
