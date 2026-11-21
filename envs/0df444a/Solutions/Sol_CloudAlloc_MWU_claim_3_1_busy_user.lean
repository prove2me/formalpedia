-- Prove2me | solution 1 for CloudAlloc.MWU.claim_3_1_busy_user
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:09:52.703477+00:00
-- url     : https://prove2.me/submissions/be4416ca-df7c-4ec3-a32c-cf114b30513a

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run
import Definitions.Def_CloudAlloc_MWU_work

namespace Aux_CA_claim31

open CloudAlloc.MWU

theorem mem_trunc {N : ℕ} {ε η : ℝ} {β : Fin N → ℝ} {L h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) : ∀ t, (∑ k, h t k = 1) ∧ ∀ k, ε / N ≤ h t k := by
  intro t
  unfold IsAlg1Run at hrun
  cases t with
  | zero => exact hrun.1
  | succ t => exact (hrun.2 t).1

theorem queue_nonneg {N : ℕ} (h L : ℕ → Fin N → ℝ) : ∀ t i, 0 ≤ queue h L t i := by
  intro t i
  cases t with
  | zero => exact le_refl _
  | succ t => exact le_max_left _ _

theorem queue_succ {N : ℕ} (h L : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) :
    queue h L (t + 1) i = queue h L t i + L t i - work h L t i := by
  show max 0 (L t i + queue h L t i - h t i) = _
  unfold work
  by_cases hc : h t i ≤ L t i + queue h L t i
  · rw [min_eq_left hc, max_eq_right (show (0 : ℝ) ≤ L t i + queue h L t i - h t i by linarith)]
    ring
  · push_neg at hc
    rw [min_eq_right hc.le, max_eq_left (show L t i + queue h L t i - h t i ≤ 0 by linarith)]
    ring

theorem cum_work {N : ℕ} (h L : ℕ → Fin N → ℝ) (i : Fin N) : ∀ k,
    ∑ t ∈ Finset.range k, work h L t i = ∑ t ∈ Finset.range k, L t i - queue h L k i := by
  intro k
  induction k with
  | zero =>
    show (∑ t ∈ Finset.range 0, work h L t i) = ∑ t ∈ Finset.range 0, L t i - 0
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, queue_succ]
    ring

end Aux_CA_claim31

open CloudAlloc.MWU Aux_CA_claim31 in
theorem solution {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ0 : ∀ i, 0 ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h)
    (T sstar : ℕ) :
    let c := ε * η / (4 * (N : ℝ))
    let st := Real.log ((N : ℝ) / ε) / (ε * c)
    let S := ⌊st⌋₊
    IsGreatest {s : ℕ | s ≤ T ∧ ∑ t ∈ Finset.range s, ∑ i, L t i ≤
        ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i} sstar →
      ∀ r : ℕ, sstar < r → r + S < T →
        ∃ i, ∀ r' ∈ Finset.Icc r (r + S), 0 < queue h L r' i := by
  intro c st S hG r hr hrT
  by_contra hno
  push_neg at hno
  choose ri hri hq using hno
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hhpos : ∀ t k, 0 ≤ h t k := fun t k =>
    le_trans (div_pos hε hNpos).le ((mem_trunc hrun t).2 k)
  have hwork : ∀ t k, 0 ≤ work h L t k := by
    intro t k
    unfold work
    exact le_min (hhpos t k) (by linarith [hL t k, queue_nonneg h L t k])
  have hq0 : ∀ i, queue h L (ri i) i = 0 := fun i => le_antisymm (hq i) (queue_nonneg h L _ i)
  have hper : ∀ i, ∑ t ∈ Finset.range r, L t i ≤ ∑ t ∈ Finset.range (r + S), work h L t i := by
    intro i
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hri i)
    have e := cum_work h L i (ri i)
    rw [hq0 i, sub_zero] at e
    calc ∑ t ∈ Finset.range r, L t i ≤ ∑ t ∈ Finset.range (ri i), L t i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h1)
            (fun t _ _ => hL t i)
      _ = ∑ t ∈ Finset.range (ri i), work h L t i := e.symm
      _ ≤ ∑ t ∈ Finset.range (r + S), work h L t i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h2)
            (fun t _ _ => hwork t i)
  have hmem : r ∈ {s : ℕ | s ≤ T ∧ ∑ t ∈ Finset.range s, ∑ i, L t i ≤
      ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i} := by
    rw [Set.mem_setOf_eq]
    refine ⟨by omega, ?_⟩
    calc ∑ t ∈ Finset.range r, ∑ i, L t i = ∑ i, ∑ t ∈ Finset.range r, L t i := Finset.sum_comm
      _ ≤ ∑ i, ∑ t ∈ Finset.range (r + S), work h L t i := Finset.sum_le_sum (fun i _ => hper i)
      _ = ∑ t ∈ Finset.range (r + S), ∑ i, work h L t i := Finset.sum_comm
  have := hG.2 hmem
  omega
