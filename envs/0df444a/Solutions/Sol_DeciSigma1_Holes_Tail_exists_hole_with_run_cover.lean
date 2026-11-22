-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_hole_with_run_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:01.783085+00:00
-- url     : https://prove2.me/submissions/0b9d8514-1775-4c48-abce-4b53f774b9dc

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
public import Theorems.Thm_DeciSigma1_Holes_Tail_RunCovers_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_hasBoundedRunCover_of_covers
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_exists_long_solution
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_period_pos
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_cons_of_agree
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_comparison_of_pumpFactor
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_rayFamily
public import Theorems.Thm_DeciSigma1_Holes_Tail_onset_repeatFactorRay_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_periodicOn_of_rayAgrees
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_eligible
public import Theorems.Thm_DeciSigma1_Holes_Tail_ray_prefix_hole
public import Theorems.Thm_DeciSigma1_Holes_Tail_streamPrefix_repeatFactorRay
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_admitted_target_le_firstRejection
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_eligible_congr
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_congr
public import Theorems.Thm_DeciSigma1_Readers_Table_channel_congr
public import Theorems.Thm_DeciSigma1_Readers_Table_endState_congr
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_channel
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_of_lt_90a7620e9ffe
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k}
    {W : Fin k → List α} (hW : M.IsHole W) :
    ∃ W', M.IsHole W' ∧
      HasScaledRunCover M W' (C.pieceCountBase + 3) (C.periodBound (levelCount k))
          (uncoveredLengthBound C) := by
  classical
  obtain ⟨F⟩ := exists_rayFamily C hW
  have heD : ∀ l, l ≤ F.level → C.periodBound l ≤ C.periodBound (levelCount k) :=
      fun l hl => C.periodBound_mono (hl.trans F.le_top)
  -- the ray lengths: a solution of the ray system above the required lower bounds
  let st : {i // i ∈ F.rays} → S := fun i => M.start i.1
  let J : {i // i ∈ F.rays} → ℕ := fun i => M.firstRejection W i.1
  obtain ⟨L, hsat, hlow⟩ := Arithmetic.DifferenceSystem.exists_long_solution _ F.no_positive_cycle
    (fun i : {i // i ∈ F.rays} => F.endCut i.1 + J i + maxOnset F.ray + 2 * maxPeriod F.ray +
        totalLength W + 1)
  let W' : Fin k → List α := fun i =>
    if h : i ∈ F.rays then streamPrefix (F.ray ⟨i, h⟩).stream (L ⟨i, h⟩) else W i
  have hWr : ∀ i (h : i ∈ F.rays), W' i = streamPrefix (F.ray ⟨i, h⟩).stream (L ⟨i, h⟩) :=
    fun i h => dif_pos h
  have hWf : ∀ i, i ∉ F.rays → W' i = W i := fun i h => dif_neg h
  have hLc : ∀ i (h : i ∈ F.rays), F.endCut i + M.firstRejection W i + totalLength W <
      L ⟨i, h⟩ := by
    intro i h; have := hlow ⟨i, h⟩; simp only [J] at this; omega
  have hlenr : ∀ i (h : i ∈ F.rays), (W' i).length = L ⟨i, h⟩ := by
    intro i h; rw [hWr i h, length_streamPrefix]
  have hstay : ∀ i (h : i ∈ F.rays),
      W' i = pumpFactor (W i) (F.startCut i) (F.endCut i) (L ⟨i, h⟩ - F.startCut i) := by
    intro i h
    have hcl := F.closed i h
    have := hLc i h
    have := hcl.1
    rw [hWr i h, F.ray_eq i h, ← streamPrefix_repeatFactorRay hcl.1 hcl.2.1]
    congr 1; omega
  have hray : ∀ i (h : i ∈ F.rays), M.Eligible W' i ∧ M.Immortal (M.endState W' i) ∧
      M.firstRejection W' i = M.firstRejection W i := by
    intro i h
    have hcl := F.closed i h
    have := hLc i h
    exact pumpFactor_eligible M (hW.1 i) hcl (F.firstRejection_le_startCut i h) (by omega)
        (hstay i h)
  have helig : ∀ i, M.Eligible W' i := fun i => if h : i ∈ F.rays then (hray i h).1
    else (StructuralReader.eligible_congr (hWf i h)).mpr (hW.1 i)
  have hJ : ∀ i, M.firstRejection W' i = M.firstRejection W i := fun i =>
    if h : i ∈ F.rays then (hray i h).2.2 else StructuralReader.firstRejection_congr (hWf i h)
  -- on the rays, admitted targets lie at or before the first rejected cut
  have hK : ∀ (j : {i // i ∈ F.rays}) b p, b ≤ L j →
      M.admitted p (rayState M (st j) (F.ray j) b) = true → b ≤ J j := by
    intro j b p hb hadm
    have hq : rayState M (st j) (F.ray j) b = M.runPrefix W' j.1 b := by
      simp only [rayState, Table.runPrefix, hWr j.1 j.2, take_streamPrefix, min_eq_left hb, st]
    rw [hq] at hadm
    have :=
        StructuralReader.admitted_target_le_firstRejection (helig j.1)
            (by rw [hlenr j.1 j.2]; exact hb) hadm
    rw [hJ] at this
    exact this
  have hchan : ∀ i j, ∀ pq ∈ M.channel W' i j, M.admitted pq.1 pq.2 = false := by
    intro i j pq hpq
    by_cases hi : i ∈ F.rays <;> by_cases hj : j ∈ F.rays
    · -- ray host, ray target
      have key := ray_prefix_hole (M := M) st F.ray J L hK
        (fun j => by have := hlow j; simp only [J] at this ⊢; omega)
        (fun i a b => F.no_self_admission i.1 i.2 a b) hsat ⟨i, hi⟩ ⟨j, hj⟩ pq
      apply key
      simp only [Table.channel] at hpq
      rw [hWr i hi, hWr j hj] at hpq
      exact hpq
    · -- ray host, fixed target: comparisons of the original words
      have hcl := F.closed i hi
      have := hLc i hi
      have hsub := comparison_of_pumpFactor (T := M.toTable) (qt := M.start j) hcl
        (F.mem_targets j hj) (F.free i hi j hj) (L := L ⟨i, hi⟩ - F.startCut i) (by omega)
      simp only [Table.channel] at hpq
      rw [hstay i hi, hWf j hj] at hpq
      exact hW.2 i j pq (hsub hpq)
    · -- fixed host, ray target: admitted targets and length
      by_contra hadm
      rw [Bool.not_eq_false] at hadm
      obtain ⟨a, ha, b, hb, hpre, rfl⟩ := mem_channel.mp hpq
      have hbJ := StructuralReader.admitted_target_le_firstRejection (helig j) hb hadm
      rw [hJ] at hbJ
      have hl := hpre.length_le
      simp only [List.length_drop, hlenr j hj, hWf i hi] at hl
      have := hLc j hj
      have := length_le_totalLength W i
      omega
    · -- fixed / fixed: unchanged
      rw [Table.channel_congr (hWf i hi) (hWf j hj)] at hpq
      exact hW.2 i j pq hpq
  have hhole : M.IsHole W' := ⟨helig, hchan⟩
  have hend : ∀ i, i ∉ F.rays → M.endState W' i = M.endState W i :=
    fun i h => Table.endState_congr (hWf i h)
  refine ⟨W', hhole, ?_⟩
  -- the run cover
  apply hasBoundedRunCover_of_covers M W'
    (T := C.uncoveredBound (levelCount k) + (C.pieceCountBase + 3) * (3 * C.escapeLengthBound
        (levelCount k) + 3))
  intro i himm
  rw [hJ i]
  have hTt : ∀ l, l ≤ F.level → C.uncoveredBound l ≤ C.uncoveredBound (levelCount k) :=
      fun l hl => C.uncoveredBound_mono (hl.trans F.le_top)
  by_cases h : i ∈ F.rays
  · have hcl := F.closed i h
    have hLi := hLc i h
    have hcc := hcl.1
    have hc' := hcl.2.1
    -- the pumped factor `[c, L)`, with the period of the ray
    let sf : PeriodicFactor := ⟨F.startCut i, L ⟨i, h⟩, (F.ray ⟨i, h⟩).period⟩
    have hsf : sf.Valid (W' i) (C.periodBound (levelCount k)) := by
      refine ⟨Ray.period_pos, (F.period_le_bound i h).trans (heD _ le_rfl), (hlenr i h).ge, ?_⟩
      have hag : RayAgrees (F.ray ⟨i, h⟩) (W' i) (L ⟨i, h⟩) :=
        ⟨(hlenr i h).ge, by rw [hWr i h, List.take_of_length_le (by rw [length_streamPrefix])]⟩
      exact (periodicOn_of_rayAgrees hag).mono
        (by rw [F.ray_eq i h]; exact onset_repeatFactorRay_le hcc hc') le_rfl
    -- letters of the edited word below `c'` are original letters
    have hlet : ∀ q < F.endCut i, (W' i)[q]? = (W i)[q]? := by
      intro q hq
      rw [hstay i h]
      exact getElem?_pumpFactor_of_lt hcc hc' (by omega) hq
    rcases F.cover i h with ⟨hc'eq, hcov⟩ | hcov
    · -- terminal ray: its cover of `[J, |w|)` and the pumped factor
      refine (((hcov.mono le_rfl (heD _ (by omega)) le_rfl).cons_of_agree hsf
        (show F.startCut i ≤ _ by omega) (hlenr i h).symm
        (by rw [hlenr i h]; omega) fun q hq => hlet q (by omega)).mono (by omega) le_rfl ?_)
      exact (hTt _ (by omega)).trans (Nat.le_add_right _ _)
    · -- other ray: its cover of `[J, c)` and the pumped factor
      have hlc : ((W i).take (F.startCut i)).length = F.startCut i := by simp; omega
      refine (((hcov.mono le_rfl (heD _ le_rfl) le_rfl).cons_of_agree hsf
        hlc.ge (hlenr i h).symm
        (by rw [hlc, hlenr i h]; omega) fun q hq => ?_).mono (by omega) le_rfl ?_)
      · rw [hlc] at hq
        rw [hlet q (by omega), List.getElem?_take_of_lt hq]
      · have := Nat.mul_le_mul_left (C.pieceCountBase + 3) (Nat.add_le_add_right
          (Nat.mul_le_mul_left 3 (C.escapeLengthBound_mono F.le_top)) 3)
        omega
  · -- fixed immortal word: its cover at level `l - 2`
    rcases F.fixed i h with hm | hKp
    · exact absurd (by rwa [← hend i h]) hm
    rw [hWf i h]
    exact hKp.1.mono (by omega) (heD _ (by omega)) ((hTt _ (by omega)).trans (Nat.le_add_right _ _))
end DeciSigma1.Holes.Tail
