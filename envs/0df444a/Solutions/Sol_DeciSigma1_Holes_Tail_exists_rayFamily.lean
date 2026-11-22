-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_rayFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:07:53.202189+00:00
-- url     : https://prove2.me/submissions/a96e1e47-e22c-488a-a94f-615412010f78

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_greedy_choice
public import Theorems.Thm_DeciSigma1_Holes_Tail_mkRay_eq
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_ClosedAt_nodeClosedAt
public import Theorems.Thm_DeciSigma1_Holes_Tail_NoSuffixOccurrenceEndsBetween_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_PeriodicCover_mono
public import Theorems.Thm_DeciSigma1_Holes_Tail_compatible_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_compatible_rayCandidate
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_stable_level
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_terminal_ray
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_le_of_mem_suffixDictionary
public import Theorems.Thm_DeciSigma1_Holes_Tail_levelCoverProperty_chainBound
public import Theorems.Thm_DeciSigma1_Holes_Tail_levelCoverProperty_chainBoundFrom
public import Theorems.Thm_DeciSigma1_Holes_Tail_nil_mem_suffixDictionary
public import Theorems.Thm_DeciSigma1_Holes_Tail_onset_repeatFactorRay_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_period_repeatFactorRay_le
public import Theorems.Thm_DeciSigma1_Holes_Tail_rayCandidate_no_selfAdmission
public import Theorems.Thm_DeciSigma1_Holes_Tail_rays_no_positiveCycle
public import Theorems.Thm_DeciSigma1_Holes_Tail_repeatFactorRay_agrees
public import Theorems.Thm_DeciSigma1_Holes_Tail_repeatFactorRay_periodicFrom
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_terminalRay_admission_edge
public import Theorems.Thm_DeciSigma1_Holes_Tail_terminalRay_no_selfAdmission
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_ChainBoundFrom_mono
public import Theorems.Thm_DeciSigma1_Words_ChainBound_chainBoundFrom
public import Theorems.Thm_DeciSigma1_Words_ChainBound_mono
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_PeriodicOn_mono
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_Ray_period_le_of_periodicFrom
public import Theorems.Thm_DeciSigma1_Words_chainBound_mortal
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
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
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k} {W : Fin k → List α} (hW : M.IsHole W) : Nonempty
        (RayFamily C M W) := by
  classical
  obtain ⟨l, hl2, hlt, hst⟩ := exists_stable_level C M W hW.1
  -- the coordinates continued by rays: immortal, without the level cover property at `l - 2`
  let IsRay : Fin k → Prop := fun i =>
    M.Immortal (M.endState W i) ∧ ¬ LevelCoverProperty C (l - 2) M W i
  have hfixed : ∀ j, ¬ IsRay j →
      ¬ M.Immortal (M.endState W j) ∨ LevelCoverProperty C (l - 2) M W j := fun j hj => by
    by_cases h : M.Immortal (M.endState W j)
    · exact .inr (by_contra fun h' => hj ⟨h, h'⟩)
    · exact .inl h
  -- without letters every coordinate is mortal, and the family has no rays
  by_cases hα : IsEmpty α
  · have hmort : ∀ j, ¬ M.Immortal (M.endState W j) := fun j h => by
      obtain ⟨u, hu, -⟩ := h 1
      exact hα.false (u.head (List.ne_nil_of_length_pos (by omega)))
    exact ⟨{
      level := l, le_top := hlt, rays := ∅, windowLength := 0, startCut := 0,
      endCut := 0, ray := fun i => absurd i.2 (Finset.notMem_empty _), targets := List.ofFn W,
      fixed := fun j _ => .inl (hmort j), mem_targets := fun j _ => List.mem_ofFn.mpr ⟨j, rfl⟩,
      no_positive_cycle := by rintro ⟨i, -⟩; exact absurd i.2 (Finset.notMem_empty _),
      closed := by simp, ray_eq := by simp,
      firstRejection_le_startCut := by simp, free := by simp, period_le_bound := by simp,
      cover := by simp, no_self_admission := by simp }⟩
  obtain ⟨a0⟩ := not_isEmpty_iff.mp hα
  let mk : Fin k → FactorCuts → Ray α := fun i f =>
    mkRay ⟨[], [a0], List.cons_ne_nil _ _⟩ (W i) f.startCut f.endCut
  have hmk : ∀ i f (h : f.startCut < f.endCut ∧ f.endCut ≤ (W i).length),
      mk i f = repeatFactorRay (W i) f.startCut f.endCut h.1 h.2 :=
    fun i f h => mkRay_eq h
  -- the rays chosen earlier must agree with their words (`exists_compatible_rayCandidate`);
  -- this holds for the ray of a closed factor after the first rejected cut
  let Adm : Fin k → FactorCuts → Prop := fun u f =>
    RayAgrees (mk u f) (W u) f.endCut ∧ (mk u f).onset ≤ f.endCut ∧
      M.firstRejection W u ≤ f.endCut ∧
      ((mk u f).onset ≤ M.firstRejection W u → (mk u f).period ≤ C.periodBound (l - 1))
  have hadm : ∀ u f (h : f.startCut < f.endCut ∧ f.endCut ≤ (W u).length),
      M.firstRejection W u ≤ f.startCut →
      ((mk u f).onset ≤ M.firstRejection W u → (mk u f).period ≤ C.periodBound (l - 1)) →
      Adm u f := by
    intro u f h hJ hper
    refine ⟨?_, ?_, by have := h.1; omega, hper⟩ <;> rw [hmk u f h]
    · exact repeatFactorRay_agrees _ _
    · have := onset_repeatFactorRay_le h.1 h.2; have := h.1; omega
  -- terminal rays (coordinates with a cover at level `l - 1`) and the other rays
  let Tset := Finset.univ.filter fun i => IsRay i ∧ CoordinateCover C (l - 1) M W i
  let Mset := Finset.univ.filter fun i => IsRay i ∧ ¬ CoordinateCover C (l - 1) M W i
  have hdisj : Disjoint Tset Mset := Finset.disjoint_filter.mpr fun _ _ h h' => h'.2 h.2
  have hmem : ∀ i, i ∈ Tset ∪ Mset ↔ IsRay i := fun i => by
    by_cases h : CoordinateCover C (l - 1) M W i <;> simp [Tset, Mset, h]
  -- the fixed words, as targets; all their chains have at most `fixedChainBudget l` steps
  let ts : List (List α) := ((Finset.univ.filter fun j => ¬ IsRay j).toList).map W
  have hts : ts.length ≤ k := by
    simpa [ts] using (Finset.card_filter_le Finset.univ _).trans_eq (Finset.card_fin k)
  have hfixCB : ∀ j, ¬ IsRay j → ChainBound (W j) (C.fixedChainBudget l) := by
    intro j hj
    rcases hfixed j hj with hm | hK
    · exact (chainBound_mortal (hW.1 j) hm).mono
        (by have := C.stateCount_le_fixedChainBudget l; omega)
    · have hSl := C.fixedChainBudget_ge_chainLength (l - 2)
      rw [show l - 2 + 2 = l by omega] at hSl
      exact (levelCoverProperty_chainBound C (hW.1 j) hK).mono hSl
  -- from the initial window of the level on, their chains have at most `Q + N` steps
  have hS : ∀ t ∈ ts, ChainBoundFrom t (C.startWindow l) (C.pieceCountBase + Fintype.card S) := by
    intro t ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    rcases hfixed j (by simpa using hj) with hm | hK
    · exact ((chainBound_mortal (hW.1 j) hm).chainBoundFrom _).mono le_rfl (by omega)
    · have hb := C.chainWindow_le_startWindow (l - 2)
      rw [show l - 2 + 2 = l by omega] at hb
      exact levelCoverProperty_chainBoundFrom C (hW.1 j) hK hb
  -- the terminal ray of each coordinate of `Tset`, from `exists_terminal_ray` at level `l - 1`
  have hterm : ∀ i, ∃ f : FactorCuts, i ∈ Tset →
      ClosedAt M.toTable (M.start i) (W i) f.windowLength f.startCut f.endCut ∧
      f.endCut = (W i).length ∧ M.firstRejection W i ≤ f.startCut ∧
      (mk i f).period ≤ C.periodBound (l - 1) ∧ ∀ t, ChainBound t (C.fixedChainBudget l) →
        NoSuffixOccurrenceEndsBetween (W i) t f.windowLength f.startCut f.endCut := by
    intro i
    by_cases hi : i ∈ Tset
    · obtain ⟨hray, hcov⟩ := (Finset.mem_filter.mp hi).2
      have hlong : C.terminalLengthBound (l - 1) ≤
          longestPeriodicSuffixLength (C.periodBound (l - 1)) (W i) := by
        by_contra h; exact hray.2 ((hst i).2.mpr ⟨hcov, by omega⟩)
      obtain ⟨B, c, p, hcl, hJc, hp, hpl, hlen, hper, hfree⟩ :=
        exists_terminal_ray C (hW.1 i) hlong
      rw [show l - 1 + 1 = l by omega] at hfree
      refine ⟨⟨B, c, (W i).length⟩, fun _ => ⟨hcl, rfl, hJc, ?_, hfree⟩⟩
      rw [hmk i _ ⟨hcl.2.1, hcl.2.2.1⟩]
      exact (Ray.period_le_of_periodicFrom hp
        (repeatFactorRay_periodicFrom hcl hp (Dvd.intro _ hlen.symm) hper)).trans hpl
    · exact ⟨⟨0, 0, 0⟩, fun h => absurd h hi⟩
  choose Ω₀ hΩ₀ using hterm
  -- the other rays, one coordinate at a time, each a good candidate
  let Good : Fin k → FactorCuts → Prop := fun v f =>
    NodeClosedAt M.toTable (M.start v) (suffixDictionary ts f.windowLength) (W v) f.startCut
      f.endCut ∧
      M.firstRejection W v ≤ f.startCut ∧ f.endCut - f.startCut ≤ C.periodBound l ∧
      (∀ t ∈ ts, NoSuffixOccurrenceEndsBetween (W v) t f.windowLength f.startCut f.endCut) ∧
      M.firstRejection W v < (mk v f).onset ∧
      PeriodicCover ((W v).take f.startCut) (M.firstRejection W v) (C.pieceCountBase + 2)
        (C.periodBound l) ((C.pieceCountBase + 3) * (3 * C.escapeLengthBound l + 3))
  obtain ⟨Ω, hΩT, hΩM, hΩc⟩ := exists_greedy_choice hdisj Ω₀ Adm Good
    (fun v f u g => NoForbiddenRayOverlap (mk v f) (mk u g) (M.firstRejection W v)
      (M.firstRejection W u))
    (fun u hu => let h := hΩ₀ u hu; hadm u _ ⟨h.1.2.1, h.1.2.2.1⟩ h.2.2.1 fun _ => h.2.2.2.1)
    (fun v _ f hf => hadm v f ⟨hf.1.1, hf.1.2.1⟩ hf.2.1 fun h =>
      absurd h (not_le.mpr hf.2.2.2.2.1))
    (fun _ _ _ _ _ _ hf hg h => compatible_symm hf.2.2.2.2.1 hg.2.2.2.2.1 h)
    (fun v hv U Ω' hvU hU => by
      obtain ⟨x, -, hx2, hx3, hx4, hx5, hx6, hx7⟩ := exists_compatible_rayCandidate C hW
        (by omega : 1 ≤ l) (fun h => (Finset.mem_filter.mp hv).2.2 ((hst v).1.mpr h)) ts hts hS
        U hvU (fun u => mk u (Ω' u)) (fun u => (Ω' u).endCut) hU
      have hx : mk v ⟨x.windowLength, x.startCut, x.endCut⟩ = x.ray :=
        hmk v _ ⟨x.closed.1, x.closed.2.1⟩
      refine ⟨⟨x.windowLength, x.startCut, x.endCut⟩, ⟨x.closed, hx2, hx3, hx4, ?_, hx6⟩,
        fun u hu => ?_⟩
      · rw [hx]; exact hx5
      · show NoForbiddenRayOverlap (mk v _) _ _ _
        rw [hx]; exact hx7 u hu)
  -- the family
  have hclosed : ∀ i ∈ Tset ∪ Mset,
      NodeClosedAt M.toTable (M.start i) (suffixDictionary ts (Ω i).windowLength) (W i)
        (Ω i).startCut (Ω i).endCut := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]
      exact (hΩ₀ i h).1.nodeClosedAt nil_mem_suffixDictionary
        fun _ hr => length_le_of_mem_suffixDictionary hr
    · exact (hΩM i h).1
  have hagT : ∀ i ∈ Tset, RayAgrees (mk i (Ω i)) (W i) (W i).length := fun i h => by
    rw [hΩT i h, ← (hΩ₀ i h).2.1]
    exact (hadm i _ ⟨(hΩ₀ i h).1.2.1, (hΩ₀ i h).1.2.2.1⟩ (hΩ₀ i h).2.2.1
      fun _ => (hΩ₀ i h).2.2.2.1).1
  refine ⟨{
    level := l, le_top := hlt, rays := Tset ∪ Mset,
    windowLength := fun i => (Ω i).windowLength, startCut := fun i => (Ω i).startCut,
    endCut := fun i => (Ω i).endCut, ray := fun i => mk i.1 (Ω i.1), targets := ts,
    fixed := fun j hj => hfixed j fun h => hj ((hmem j).mpr h),
    mem_targets := fun j hj => List.mem_map.mpr ⟨j, by
      simpa using fun h => hj ((hmem j).mpr h), rfl⟩, closed := hclosed,
    ray_eq := fun i hi => hmk i _ ⟨(hclosed i hi).1, (hclosed i hi).2.1⟩,
    firstRejection_le_startCut := fun i hi => ?_, free := fun i hi j hj => ?_,
    period_le_bound := fun i hi => ?_, cover := fun i hi => ?_,
    no_self_admission := fun i hi => ?_, no_positive_cycle := ?_ }⟩
  · rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]; exact (hΩ₀ i h).2.2.1
    · exact (hΩM i h).2.1
  · have hj' : ¬ IsRay j := fun h => hj ((hmem j).mpr h)
    rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]; exact (hΩ₀ i h).2.2.2.2 (W j) (hfixCB j hj')
    · exact (hΩM i h).2.2.2.1 (W j) (List.mem_map.mpr ⟨j, by simpa using hj', rfl⟩)
  · rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]; exact (hΩ₀ i h).2.2.2.1.trans (C.periodBound_mono (by omega))
    · rw [hmk i _ ⟨(hΩM i h).1.1, (hΩM i h).1.2.1⟩]
      exact (period_repeatFactorRay_le _ _).trans (hΩM i h).2.2.1
  · rcases Finset.mem_union.mp hi with h | h
    · rw [hΩT i h]; exact .inl ⟨(hΩ₀ i h).2.1, (Finset.mem_filter.mp h).2.2⟩
    · exact .inr (hΩM i h).2.2.2.2.2
  · rcases Finset.mem_union.mp hi with h | h
    · exact terminalRay_no_selfAdmission hW (hagT i h)
    · have hg := hΩM i h
      exact rayCandidate_no_selfAdmission hW
        (hadm i _ ⟨hg.1.1, hg.1.2.1⟩ hg.2.1 fun h => absurd h (not_le.mpr hg.2.2.2.2.1)).1
        (by have := hg.1.1; omega) hg.2.2.2.2.1
  · apply rays_no_positiveCycle M _ _ _ (fun i => ((W i.1).length : ℤ)) (fun i => i.1 ∈ Mset)
    · exact fun v hv => ⟨(hΩM v.1 hv).2.2.2.2.1,
        fun u huv => hΩc v.1 hv u.1 u.2 fun h => huv (Subtype.ext h)⟩
    · intro i j hi hj _ a b hb hadm heq
      exact terminalRay_admission_edge hW (hagT i.1 ((Finset.mem_union.mp i.2).resolve_right hi))
        (hagT j.1 ((Finset.mem_union.mp j.2).resolve_right hj)) hb hadm heq
end DeciSigma1.Holes.Tail
