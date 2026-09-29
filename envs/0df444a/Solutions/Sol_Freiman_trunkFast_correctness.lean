-- Prove2me | solution 1 for Freiman.trunkFast_correctness
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:08:45.800658+00:00
-- url     : https://prove2.me/submissions/70bf7be7-e7d7-44b1-a105-6913bcd5ee34

import Definitions.Def_Freiman_trunkFast
open Freiman Freiman.TrunkFast
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem foldl_append_getElem? {α : Type} :
    ∀ (arrs : List (Array α)) (init : Array α) (i : ℕ),
      (arrs.foldl (·++·) init)[i]? =
        if i < init.size then init[i]? else chainGet? arrs (i - init.size)
  | [], init, i => by
      by_cases h : i < init.size
      · simp [h]
      · simp [h, chainGet?]
  | A::As, init, i => by
      rw [List.foldl_cons, foldl_append_getElem? As (init++A) i, Array.size_append]
      by_cases h1 : i < init.size
      · rw [if_pos h1, if_pos (by omega : i < init.size + A.size),
          Array.getElem?_append_left h1]
      · rw [if_neg h1]
        rw [show chainGet? (A::As) (i-init.size) =
              if i - init.size < A.size then A[i-init.size]? else chainGet? As (i - init.size - A.size)
            from rfl]
        by_cases h2 : i < init.size + A.size
        · rw [if_pos h2, Array.getElem?_append_right (by omega),
            if_pos (by omega : i - init.size < A.size)]
        · rw [if_neg h2, if_neg (show ¬ i - init.size < A.size by omega),
            show i - (init.size + A.size) = i - init.size - A.size by omega]

private theorem foldl_append_size {α : Type} :
    ∀ (arrs : List (Array α)) (init : Array α),
      (arrs.foldl (·++·) init).size = arrs.foldl (fun n A => n + A.size) init.size
  | [], init => rfl
  | A::As, init => by
      rw [List.foldl_cons, foldl_append_size As (init++A), Array.size_append, List.foldl_cons]

private theorem trunkDataWitnesses_eq_foldl :
    trunkDataWitnesses = List.foldl (·++·) trunkWitnessData01
      [trunkWitnessData02,trunkWitnessData03,trunkWitnessData04,trunkWitnessData05,trunkWitnessData06,
       trunkWitnessData07,trunkWitnessData08,trunkWitnessData09,trunkWitnessData10,trunkWitnessData11,
       trunkWitnessData12,trunkWitnessData13,trunkWitnessData14,trunkWitnessData15,trunkWitnessData16,
       trunkWitnessData17,trunkWitnessData18,trunkWitnessData19,trunkWitnessData20,trunkWitnessData21,
       trunkWitnessData22,trunkWitnessData23,trunkWitnessData24,trunkWitnessData25,trunkWitnessData26,
       trunkWitnessData27,trunkWitnessData28,trunkWitnessData29,trunkWitnessData30,trunkWitnessData31,
       trunkWitnessData32,trunkWitnessData33,trunkWitnessData34,trunkWitnessData35] := rfl

private theorem trunkWitnesses_size : trunkCatalog.witnesses.size = 8656 := by
  rw [show trunkCatalog.witnesses = trunkDataWitnesses from rfl,
    trunkDataWitnesses_eq_foldl, foldl_append_size]
  decide +kernel

private theorem witness_eq? (n : ℕ) : trunkDataWitnesses[n-1]? = fastWitness? n := by
  rw [trunkDataWitnesses_eq_foldl, foldl_append_getElem?]; rfl

private theorem witness_eq (n : ℕ) : trunkWitness trunkCatalog n = fastWitness n := by
  unfold trunkWitness fastWitness
  rw [show trunkCatalog.witnesses = trunkDataWitnesses from rfl, witness_eq?]

private theorem trunkDataBounds_eq_foldl :
    trunkDataBounds = List.foldl (·++·) trunkBoundData01
      [trunkBoundData02,trunkBoundData03,trunkBoundData04] := rfl

private theorem bound_eq? (n : ℕ) : trunkDataBounds[n-1]? = fastBound? n := by
  rw [trunkDataBounds_eq_foldl, foldl_append_getElem?]; rfl

private theorem bound_eq (n : ℕ) : trunkBound trunkCatalog n = fastBound n := by
  unfold trunkBound fastBound
  rw [show trunkCatalog.bounds = trunkDataBounds from rfl, bound_eq?]

/-! ## Mirror predicates: same shape as trunkLeafBound/trunkTreeBound, but
built directly from fastWitness/fastBound/literal sizes, hence PLAINLY
decidable (no rewriting needed at decide-time). Soundness (Fast -> real) is
proved ONCE, ordinarily (not inside a reusable Decidable instance), so
`decide +kernel` on the Fast predicate never has to reduce the
witness_eq/bound_eq/foldl-induction proofs. -/

private theorem trunkUseBoundsFast_iff (w : TrunkWitness) (l u : CertBound) :
    trunkUseBoundsFast w l u ↔ trunkUseBounds trunkCatalog w l u := by
  unfold trunkUseBoundsFast trunkUseBounds
  rw [bound_eq, bound_eq]

private theorem trunkLeafBoundFast_iff (R : CertRectangle) (bs : List CertBound) (id : ℕ) (sign : ℤ) :
    trunkLeafBoundFast R bs id sign ↔ trunkLeafBound trunkCatalog R bs id sign := by
  unfold trunkLeafBoundFast trunkLeafBound
  rw [← witness_eq, ← trunkWitnesses_size]
  constructor
  · rintro ⟨h1,h2,h3,h4,l,hl,u,hu,h5⟩
    exact ⟨h1,h2,h3,h4,l,hl,u,hu,(trunkUseBoundsFast_iff _ l u).1 h5⟩
  · rintro ⟨h1,h2,h3,h4,l,hl,u,hu,h5⟩
    exact ⟨h1,h2,h3,h4,l,hl,u,hu,(trunkUseBoundsFast_iff _ l u).2 h5⟩

private theorem trunkTreeBoundFast_iff (R : CertRectangle) (bs : List CertBound) :
    ∀ t, trunkTreeBoundFast R bs t ↔ trunkTreeBound trunkCatalog R bs t
  | .pair id => trunkLeafBoundFast_iff R bs id 0
  | .split axis left right => by
      unfold trunkTreeBoundFast trunkTreeBound
      rw [trunkTreeBoundFast_iff (trunkRectangleHalf R axis false) bs left,
          trunkTreeBoundFast_iff (trunkRectangleHalf R axis true) bs right]
  | .diagonal negative positive => by
      unfold trunkTreeBoundFast trunkTreeBound
      rw [trunkLeafBoundFast_iff R bs negative (-1), trunkLeafBoundFast_iff R bs positive 1]
  | .boundary => by unfold trunkTreeBoundFast trunkTreeBound; rfl

private theorem trunk_fold_dedup_eq_self :
    ∀ (L acc : List (List CertBound)),
      (∀ y ∈ acc, ∀ x ∈ L, y.toFinset ≠ x.toFinset) →
      L.Pairwise (fun x y => x.toFinset ≠ y.toFinset) →
      L.foldl (fun acc bs => if acc.any (fun cs => decide (cs.toFinset = bs.toFinset))
        then acc else acc ++ [bs]) acc = acc ++ L := by
  intro L
  induction L with
  | nil => intro acc _ _; simp
  | cons x xs ih =>
    intro acc hacc hpair
    simp only [List.foldl_cons]
    rw [List.pairwise_cons] at hpair
    have hx : ¬ acc.any (fun cs => decide (cs.toFinset = x.toFinset)) = true := by
      simp only [List.any_eq_true, decide_eq_true_eq]
      rintro ⟨y, hy, hpy⟩
      exact hacc y hy x (List.mem_cons_self ..) hpy
    rw [if_neg hx]
    have hacc' : ∀ y ∈ acc ++ [x], ∀ z ∈ xs, y.toFinset ≠ z.toFinset := by
      intro y hy z hz
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | hy
      · exact hacc y hy z (List.mem_cons_of_mem _ hz)
      · subst hy; exact hpair.1 z hz
    rw [ih (acc ++ [x]) hacc' hpair.2, List.append_assoc]
    simp

private theorem trunkParents_eq_raw (C : LowerHistoryContext)
    (hpf : (trunkRawParents C).Pairwise (fun cs bs => cs.toFinset ≠ bs.toFinset)) :
    trunkParents C = trunkRawParents C := by
  show (trunkRawParents C).foldl (fun acc bs => if acc.any (fun cs => decide (cs.toFinset = bs.toFinset))
    then acc else acc ++ [bs]) [] = trunkRawParents C
  have hfold := trunk_fold_dedup_eq_self (trunkRawParents C) [] (by simp) hpf
  simpa using hfold

private theorem trunkResidualFast_eq (S : TrunkState)
    (hPar : trunkParents S.context = trunkRawParents S.context)
    (plan parent goal : ℕ) (branch : ℤ) :
    trunkResidualFast S plan parent goal branch = trunkResidual S plan parent goal branch := by
  unfold trunkResidualFast trunkResidual trunkBaseConditions
  rw [hPar]
  rfl

private theorem trunkGroupValidFast_imp (k : Fin 16)
    (hPar : trunkParents (trunkCatalog.states k).context = trunkRawParents (trunkCatalog.states k).context)
    (g : TrunkGroup) (h : trunkGroupValidFast k g) : trunkGroupValid trunkCatalog k g := by
  unfold trunkGroupValidFast at h
  unfold trunkGroupValid
  dsimp only
  rw [hPar]
  obtain ⟨h1,h2,h3,h4⟩ := h
  refine ⟨h1,h2,h3,?_⟩
  intro bt hbt
  obtain ⟨ha,hb,hc⟩ := h4 bt hbt
  refine ⟨ha,hb,?_⟩
  intro p hp
  rw [← trunkResidualFast_eq _ hPar]
  exact (trunkTreeBoundFast_iff _ _ _).1 (hc p hp)

theorem solution :
    (∀ C : LowerHistoryContext,
      (trunkRawParents C).Pairwise (fun cs bs => cs.toFinset ≠ bs.toFinset) →
      trunkParents C = trunkRawParents C) ∧
    (∀ k : Fin 16,
      trunkParents (trunkCatalog.states k).context = trunkRawParents (trunkCatalog.states k).context →
      ∀ g : TrunkGroup, trunkGroupValidFast k g → trunkGroupValid trunkCatalog k g) := by
  exact ⟨trunkParents_eq_raw, trunkGroupValidFast_imp⟩

#print axioms solution
