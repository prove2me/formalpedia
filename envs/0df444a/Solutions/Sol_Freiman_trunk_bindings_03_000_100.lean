-- Prove2me | solution 1 for Freiman.trunk_bindings_03_000_100
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:01:31.762629+00:00
-- url     : https://prove2.me/submissions/aa834dff-0aff-4626-9a55-700c7a2cc689

-- Adapted from the public kernel-checked optimization helpers in Marac submission
-- https://prove2.me/submissions/93a6c511-3ed0-48c3-bbd0-ecae49532be4
-- The finite decision below checks the distinct state and row range of this target.
import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases

open Freiman

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! ## Fast array-chain lookup (avoids forcing the kernel to physically
concatenate all 35 witness-data arrays / 4 bound-data arrays on every
reference), via a generic `chainGet?` proved equal to folded `++` once,
symbolically (no data-specific `decide`). -/
def chainGet? {α : Type} : List (Array α) → ℕ → Option α
  | [], _ => none
  | A::As, j => if j < A.size then A[j]? else chainGet? As (j - A.size)

theorem foldl_append_getElem? {α : Type} :
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

theorem foldl_append_size {α : Type} :
    ∀ (arrs : List (Array α)) (init : Array α),
      (arrs.foldl (·++·) init).size = arrs.foldl (fun n A => n + A.size) init.size
  | [], init => rfl
  | A::As, init => by
      rw [List.foldl_cons, foldl_append_size As (init++A), Array.size_append, List.foldl_cons]

theorem trunkDataWitnesses_eq_foldl :
    trunkDataWitnesses = List.foldl (·++·) trunkWitnessData01
      [trunkWitnessData02,trunkWitnessData03,trunkWitnessData04,trunkWitnessData05,trunkWitnessData06,
       trunkWitnessData07,trunkWitnessData08,trunkWitnessData09,trunkWitnessData10,trunkWitnessData11,
       trunkWitnessData12,trunkWitnessData13,trunkWitnessData14,trunkWitnessData15,trunkWitnessData16,
       trunkWitnessData17,trunkWitnessData18,trunkWitnessData19,trunkWitnessData20,trunkWitnessData21,
       trunkWitnessData22,trunkWitnessData23,trunkWitnessData24,trunkWitnessData25,trunkWitnessData26,
       trunkWitnessData27,trunkWitnessData28,trunkWitnessData29,trunkWitnessData30,trunkWitnessData31,
       trunkWitnessData32,trunkWitnessData33,trunkWitnessData34,trunkWitnessData35] := rfl

def fastWitness? (n : ℕ) : Option TrunkWitness :=
  if n-1 < trunkWitnessData01.size then trunkWitnessData01[n-1]?
  else chainGet? [trunkWitnessData02,trunkWitnessData03,trunkWitnessData04,trunkWitnessData05,trunkWitnessData06,
       trunkWitnessData07,trunkWitnessData08,trunkWitnessData09,trunkWitnessData10,trunkWitnessData11,
       trunkWitnessData12,trunkWitnessData13,trunkWitnessData14,trunkWitnessData15,trunkWitnessData16,
       trunkWitnessData17,trunkWitnessData18,trunkWitnessData19,trunkWitnessData20,trunkWitnessData21,
       trunkWitnessData22,trunkWitnessData23,trunkWitnessData24,trunkWitnessData25,trunkWitnessData26,
       trunkWitnessData27,trunkWitnessData28,trunkWitnessData29,trunkWitnessData30,trunkWitnessData31,
       trunkWitnessData32,trunkWitnessData33,trunkWitnessData34,trunkWitnessData35] (n-1-trunkWitnessData01.size)
def fastWitness (n : ℕ) : TrunkWitness := (fastWitness? n).getD ⟨0,0,⟨0,1,0,1⟩,0,0⟩

theorem trunkWitnesses_size : trunkCatalog.witnesses.size = 8656 := by
  rw [show trunkCatalog.witnesses = trunkDataWitnesses from rfl,
    trunkDataWitnesses_eq_foldl, foldl_append_size]
  decide +kernel

theorem witness_eq? (n : ℕ) : trunkDataWitnesses[n-1]? = fastWitness? n := by
  rw [trunkDataWitnesses_eq_foldl, foldl_append_getElem?]; rfl
theorem witness_eq (n : ℕ) : trunkWitness trunkCatalog n = fastWitness n := by
  unfold trunkWitness fastWitness
  rw [show trunkCatalog.witnesses = trunkDataWitnesses from rfl, witness_eq?]

theorem trunkDataBounds_eq_foldl :
    trunkDataBounds = List.foldl (·++·) trunkBoundData01
      [trunkBoundData02,trunkBoundData03,trunkBoundData04] := rfl
def fastBound? (n : ℕ) : Option CertBound :=
  if n-1 < trunkBoundData01.size then trunkBoundData01[n-1]?
  else chainGet? [trunkBoundData02,trunkBoundData03,trunkBoundData04] (n-1-trunkBoundData01.size)
def fastBound (n : ℕ) : CertBound := (fastBound? n).getD lowerHistoryZero
theorem bound_eq? (n : ℕ) : trunkDataBounds[n-1]? = fastBound? n := by
  rw [trunkDataBounds_eq_foldl, foldl_append_getElem?]; rfl
theorem bound_eq (n : ℕ) : trunkBound trunkCatalog n = fastBound n := by
  unfold trunkBound fastBound
  rw [show trunkCatalog.bounds = trunkDataBounds from rfl, bound_eq?]

/-! ## Mirror predicates: same shape as trunkLeafBound/trunkTreeBound, but
built directly from fastWitness/fastBound/literal sizes, hence PLAINLY
decidable (no rewriting needed at decide-time). Soundness (Fast -> real) is
proved ONCE, ordinarily (not inside a reusable Decidable instance), so
`decide +kernel` on the Fast predicate never has to reduce the
witness_eq/bound_eq/foldl-induction proofs. -/
def trunkUseBoundsFast (w : TrunkWitness) (l u : CertBound) : Prop :=
  l.lower = true ∧ u.lower = false ∧
  l.threshold = (fastBound w.lowerId).threshold ∧
  u.threshold = (fastBound w.upperId).threshold ∧
  ((w.diagonal = 0 ∧ 0 < w.margin) ∨ l.strict = true ∨ u.strict = true)

def trunkLeafBoundFast (R : CertRectangle) (bs : List CertBound) (id : ℕ) (sign : ℤ) : Prop :=
  0 < id ∧ id ≤ 8656 ∧
  (fastWitness id).diagonal = sign ∧
  section14RectangleContains (fastWitness id).rectangle R ∧
  ∃ l ∈ bs, ∃ u ∈ bs, trunkUseBoundsFast (fastWitness id) l u

theorem trunkUseBoundsFast_iff (w : TrunkWitness) (l u : CertBound) :
    trunkUseBoundsFast w l u ↔ trunkUseBounds trunkCatalog w l u := by
  unfold trunkUseBoundsFast trunkUseBounds
  rw [bound_eq, bound_eq]

theorem trunkLeafBoundFast_iff (R : CertRectangle) (bs : List CertBound) (id : ℕ) (sign : ℤ) :
    trunkLeafBoundFast R bs id sign ↔ trunkLeafBound trunkCatalog R bs id sign := by
  unfold trunkLeafBoundFast trunkLeafBound
  rw [← witness_eq, ← trunkWitnesses_size]
  constructor
  · rintro ⟨h1,h2,h3,h4,l,hl,u,hu,h5⟩
    exact ⟨h1,h2,h3,h4,l,hl,u,hu,(trunkUseBoundsFast_iff _ l u).1 h5⟩
  · rintro ⟨h1,h2,h3,h4,l,hl,u,hu,h5⟩
    exact ⟨h1,h2,h3,h4,l,hl,u,hu,(trunkUseBoundsFast_iff _ l u).2 h5⟩

def trunkTreeBoundFast (R : CertRectangle) (bs : List CertBound) : TrunkTree → Prop
  | .pair id => trunkLeafBoundFast R bs id 0
  | .split axis left right =>
    trunkTreeBoundFast (trunkRectangleHalf R axis false) bs left ∧
    trunkTreeBoundFast (trunkRectangleHalf R axis true) bs right
  | .diagonal negative positive => trunkLeafBoundFast R bs negative (-1) ∧ trunkLeafBoundFast R bs positive 1
  | .boundary => trunkBoundaryBound R bs

theorem trunkTreeBoundFast_iff (R : CertRectangle) (bs : List CertBound) :
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

instance decTrunkTreeBoundFast (R : CertRectangle) (bs : List CertBound) :
    ∀ t : TrunkTree, Decidable (trunkTreeBoundFast R bs t)
  | .pair id => by unfold trunkTreeBoundFast trunkLeafBoundFast trunkUseBoundsFast section14RectangleContains; infer_instance
  | .split axis left right => by
      unfold trunkTreeBoundFast
      have := decTrunkTreeBoundFast (trunkRectangleHalf R axis false) bs left
      have := decTrunkTreeBoundFast (trunkRectangleHalf R axis true) bs right
      infer_instance
  | .diagonal negative positive => by
      unfold trunkTreeBoundFast trunkLeafBoundFast trunkUseBoundsFast section14RectangleContains
      infer_instance
  | .boundary => by unfold trunkTreeBoundFast trunkBoundaryBound certThresholdDataValid; infer_instance

def trunkRawParents (C : LowerHistoryContext) : List (List CertBound) :=
  let a := trunkBranches C ⟨([2],[]),true,([1],[]),false,false,[]⟩
  let b := trunkBranches C ⟨([1],[]),true,([2],[]),false,false,[]⟩
  a.flatMap fun (ca,ga) => b.filterMap fun (cb,gb) =>
    let base := ca++cb++[lowerHistoryHN,lowerHistoryZero]
    match ga,gb with
    | .impossible,_ | _,.impossible => none
    | .automatic,.automatic => some base
    | .bound g,.automatic | .automatic,.bound g => some (g::base)
    | .bound g,.bound h => some (g::h::base)

theorem trunk_fold_dedup_eq_self :
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

theorem trunkParents_eq_raw (C : LowerHistoryContext)
    (hpf : (trunkRawParents C).Pairwise (fun cs bs => cs.toFinset ≠ bs.toFinset)) :
    trunkParents C = trunkRawParents C := by
  show (trunkRawParents C).foldl (fun acc bs => if acc.any (fun cs => decide (cs.toFinset = bs.toFinset))
    then acc else acc ++ [bs]) [] = trunkRawParents C
  have hfold := trunk_fold_dedup_eq_self (trunkRawParents C) [] (by simp) hpf
  simpa using hfold

theorem hParEq3 : trunkParents (trunkCatalog.states 3).context = trunkRawParents (trunkCatalog.states 3).context :=
  trunkParents_eq_raw _ (by decide +kernel)

def trunkResidualFast3 (S : TrunkState) (plan parent goal : ℕ) (branch : ℤ) : List CertBound :=
  let b := trunkBranch S plan goal branch
  (trunkPlanAt S plan).cuts ++ (trunkRawParents S.context)[parent]?.getD [] ++ b.1 ++
    match b.2 with | .bound a => [lowerHistoryComplement a] | _ => []

theorem trunkResidualFast_eq3 (plan parent goal : ℕ) (branch : ℤ) :
    trunkResidualFast3 (trunkCatalog.states 3) plan parent goal branch =
      trunkResidual (trunkCatalog.states 3) plan parent goal branch := by
  unfold trunkResidualFast3 trunkResidual trunkBaseConditions
  rw [hParEq3]
  rfl

def trunkGroupValidFast3 (g : TrunkGroup) : Prop :=
  let S := trunkCatalog.states 3
  g.plan < (trunkSourcePlans S.context).length ∧ g.goal ≤ (trunkSpecs (trunkPlanAt S g.plan)).length ∧
  (∀ p ∈ g.parents, p < (trunkRawParents S.context).length) ∧
  ∀ bt ∈ g.branches,
    ((g.goal = 0 ∧ bt.1 = -1) ∨ (0 < g.goal ∧ 0 ≤ bt.1 ∧ bt.1.toNat < (trunkGoalBranches S g.plan g.goal).length)) ∧
    (trunkBranch S g.plan g.goal bt.1).2 ≠ LowerHistoryComparison.automatic ∧
    ∀ p ∈ g.parents, trunkTreeBoundFast S.rectangle (trunkResidualFast3 S g.plan p g.goal bt.1) bt.2

theorem trunkGroupValidFast3_imp (g : TrunkGroup) (h : trunkGroupValidFast3 g) :
    trunkGroupValid trunkCatalog 3 g := by
  unfold trunkGroupValidFast3 at h
  unfold trunkGroupValid
  dsimp only
  rw [hParEq3]
  obtain ⟨h1,h2,h3,h4⟩ := h
  refine ⟨h1,h2,h3,?_⟩
  intro bt hbt
  obtain ⟨ha,hb,hc⟩ := h4 bt hbt
  refine ⟨ha,hb,?_⟩
  intro p hp
  rw [← trunkResidualFast_eq3]
  exact (trunkTreeBoundFast_iff _ _ _).1 (hc p hp)


theorem batch_chunk_0 : ∀ j ∈ List.range 20, trunkGroupValidFast3 (trunkStateData03Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast3 trunkResidualFast3
  decide +kernel

theorem batch_chunk_20 : ∀ j ∈ List.range' 20 20, trunkGroupValidFast3 (trunkStateData03Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast3 trunkResidualFast3
  decide +kernel

theorem batch_chunk_40 : ∀ j ∈ List.range' 40 20, trunkGroupValidFast3 (trunkStateData03Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast3 trunkResidualFast3
  decide +kernel

theorem batch_chunk_60 : ∀ j ∈ List.range' 60 20, trunkGroupValidFast3 (trunkStateData03Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast3 trunkResidualFast3
  decide +kernel

theorem batch_chunk_80 : ∀ j ∈ List.range' 80 20, trunkGroupValidFast3 (trunkStateData03Part01.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast3 trunkResidualFast3
  decide +kernel

theorem batch_key (j : ℕ) (hj : j < 100) : trunkGroupValidFast3 (trunkStateData03Part01.getD j ⟨0,[],0,[]⟩) := by
  rcases lt_or_ge j 20 with h0 | h0
  · exact batch_chunk_0 j (List.mem_range.2 (by omega))
  rcases lt_or_ge j 40 with h1 | h1
  · exact batch_chunk_20 j (List.mem_range'.2 ⟨j - 20, by omega, by omega⟩)
  rcases lt_or_ge j 60 with h2 | h2
  · exact batch_chunk_40 j (List.mem_range'.2 ⟨j - 40, by omega, by omega⟩)
  rcases lt_or_ge j 80 with h3 | h3
  · exact batch_chunk_60 j (List.mem_range'.2 ⟨j - 60, by omega, by omega⟩)
  · exact batch_chunk_80 j (List.mem_range'.2 ⟨j - 80, by omega, by omega⟩)

theorem part_length_1 : trunkStateData03Part01.length = 100 := by decide +kernel

theorem part_length_2 : trunkStateData03Part02.length = 100 := by decide +kernel

theorem solution : trunkBindingBatch 3 0 100 := by
  intro i hlo hhi g hg
  change (trunkStateData03Part01 ++ trunkStateData03Part02 ++ trunkStateData03Part03)[i]? = some g at hg
  rw [List.getElem?_append_left (show i < (trunkStateData03Part01 ++ trunkStateData03Part02).length by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  rw [List.getElem?_append_left (show i < (trunkStateData03Part01).length by simp only [List.length_append, part_length_1, part_length_2, Nat.reduceAdd]; omega)] at hg
  have hgi := batch_key (i - 0) (by omega)
  have hgv : trunkStateData03Part01.getD (i - 0) ⟨0,[],0,[]⟩ = g := by
    simp only [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact trunkGroupValidFast3_imp g hgi
