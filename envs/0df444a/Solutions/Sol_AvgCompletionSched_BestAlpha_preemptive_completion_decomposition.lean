-- Prove2me | solution 1 for AvgCompletionSched.BestAlpha.preemptive_completion_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T06:25:57.843841+00:00
-- url     : https://prove2.me/submissions/41b9c4e1-fbcf-4395-a4b7-be102bae8ade

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Model

open AvgCompletionSched.BestAlpha
open MeasureTheory

theorem solution {n : ℕ} {I : Instance n} (P : PreemptiveSchedule I) (i : Fin n) :
    P.CP i = P.idle i + ∑ j, P.frac i j * I.p j := by
  classical
  -- the completion time is a nonnegative real
  have hset : {t : ℝ | I.p i ≤ P.done i t}.Nonempty := by
    obtain ⟨T, hT⟩ := P.bounded i
    refine ⟨max T 1, ?_⟩
    have hsub : {s : ℝ | P.σ s = some i} ⊆ Set.Ico 0 (max T 1) := by
      intro s hs
      exact ⟨P.nonneg s i hs, lt_of_lt_of_le (hT s hs) (le_max_left _ _)⟩
    have heq : {s : ℝ | P.σ s = some i} ∩ Set.Ico 0 (max T 1) = {s : ℝ | P.σ s = some i} :=
      Set.inter_eq_left.mpr hsub
    have hd : P.done i (max T 1) = I.p i := by
      have h2 : P.done i (max T 1)
          = (volume ({s : ℝ | P.σ s = some i} ∩ Set.Ico 0 (max T 1))).toReal := rfl
      rw [h2, heq, P.total i, ENNReal.toReal_ofReal (I.p_pos i).le]
    exact le_of_eq hd.symm
  have hlow : ∀ t ∈ {t : ℝ | I.p i ≤ P.done i t}, 0 ≤ t := by
    intro t ht
    by_contra hneg
    push_neg at hneg
    have hempty : Set.Ico (0:ℝ) t = ∅ := Set.Ico_eq_empty (by linarith)
    have : P.done i t = 0 := by
      simp only [PreemptiveSchedule.done, hempty, Set.inter_empty, measure_empty]
      simp
    have hpi := I.p_pos i
    rw [Set.mem_setOf_eq, this] at ht
    linarith
  have hCnn : 0 ≤ P.CP i := le_csInf hset hlow
  -- the fibres of `σ` partition `[0, C)`
  have hmeas : ∀ o : Option (Fin n), MeasurableSet {s : ℝ | P.σ s = o} := by
    intro o
    cases o with
    | none =>
      have h : {s : ℝ | P.σ s = none} = (⋃ j, {s : ℝ | P.σ s = some j})ᶜ := by
        ext s
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
        constructor
        · intro h j
          rw [h]
          simp
        · intro h
          cases hs : P.σ s with
          | none => rfl
          | some j => exact absurd hs (h j)
      rw [h]
      exact (MeasurableSet.iUnion fun j => P.measurableSet_run j).compl
    | some j => exact P.measurableSet_run j
  have hgm : ∀ o : Option (Fin n),
      MeasurableSet ({s : ℝ | P.σ s = o} ∩ Set.Ico 0 (P.CP i)) :=
    fun o => (hmeas o).inter measurableSet_Ico
  have hgd : Pairwise (Function.onFun Disjoint
      (fun o : Option (Fin n) => {s : ℝ | P.σ s = o} ∩ Set.Ico 0 (P.CP i))) := by
    intro o o' hoo'
    rw [Function.onFun, Set.disjoint_left]
    intro s hs hs'
    exact hoo' (hs.1.symm.trans hs'.1)
  have hgu : (⋃ o : Option (Fin n), {s : ℝ | P.σ s = o} ∩ Set.Ico 0 (P.CP i))
      = Set.Ico 0 (P.CP i) := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨o, -, h⟩
      exact h
    · intro h
      exact ⟨P.σ s, rfl, h⟩
  have hvol : volume (Set.Ico (0:ℝ) (P.CP i))
      = ∑ o : Option (Fin n), volume ({s : ℝ | P.σ s = o} ∩ Set.Ico 0 (P.CP i)) := by
    have h := measure_iUnion (μ := (volume : Measure ℝ)) hgd hgm
    rw [hgu] at h
    rw [h]
    exact tsum_fintype _
  have hfin : ∀ o : Option (Fin n),
      volume ({s : ℝ | P.σ s = o} ∩ Set.Ico 0 (P.CP i)) ≠ ⊤ := by
    intro o
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    exact measure_Ico_lt_top.ne
  -- take real parts
  have hIco : volume (Set.Ico (0:ℝ) (P.CP i)) = ENNReal.ofReal (P.CP i) := by
    rw [Real.volume_Ico, sub_zero]
  have hreal : P.CP i
      = ∑ o : Option (Fin n), (volume ({s : ℝ | P.σ s = o} ∩ Set.Ico 0 (P.CP i))).toReal := by
    have h1 : (volume (Set.Ico (0:ℝ) (P.CP i))).toReal = P.CP i := by
      rw [hIco, ENNReal.toReal_ofReal hCnn]
    have h2 : (volume (Set.Ico (0:ℝ) (P.CP i))).toReal
        = ∑ o : Option (Fin n), (volume ({s : ℝ | P.σ s = o} ∩ Set.Ico 0 (P.CP i))).toReal := by
      rw [hvol]
      exact ENNReal.toReal_sum (fun o _ => hfin o)
    calc P.CP i = (volume (Set.Ico (0:ℝ) (P.CP i))).toReal := h1.symm
      _ = ∑ o : Option (Fin n),
            (volume ({s : ℝ | P.σ s = o} ∩ Set.Ico 0 (P.CP i))).toReal := h2
  rw [hreal, Fintype.sum_option]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PreemptiveSchedule.frac, div_mul_cancel₀ _ (I.p_pos j).ne']
  rfl
