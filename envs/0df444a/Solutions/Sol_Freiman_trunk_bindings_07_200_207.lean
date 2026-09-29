-- Prove2me | solution 1 for Freiman.trunk_bindings_07_200_207
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:13:50.147734+00:00
-- url     : https://prove2.me/submissions/cb6dafe6-4140-4761-87c6-431ad7a7f7d7

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

theorem hParEq07 : trunkParents (trunkCatalog.states 7).context = trunkRawParents (trunkCatalog.states 7).context :=
  trunkParents_eq_raw _ (by decide +kernel)

def trunkResidualFast07 (S : TrunkState) (plan parent goal : ℕ) (branch : ℤ) : List CertBound :=
  let b := trunkBranch S plan goal branch
  (trunkPlanAt S plan).cuts ++ (trunkRawParents S.context)[parent]?.getD [] ++ b.1 ++
    match b.2 with | .bound a => [lowerHistoryComplement a] | _ => []

theorem trunkResidualFast_eq07 (plan parent goal : ℕ) (branch : ℤ) :
    trunkResidualFast07 (trunkCatalog.states 7) plan parent goal branch =
      trunkResidual (trunkCatalog.states 7) plan parent goal branch := by
  unfold trunkResidualFast07 trunkResidual trunkBaseConditions
  rw [hParEq07]
  rfl

def trunkGroupValidFast07 (g : TrunkGroup) : Prop :=
  let S := trunkCatalog.states 7
  g.plan < (trunkSourcePlans S.context).length ∧ g.goal ≤ (trunkSpecs (trunkPlanAt S g.plan)).length ∧
  (∀ p ∈ g.parents, p < (trunkRawParents S.context).length) ∧
  ∀ bt ∈ g.branches,
    ((g.goal = 0 ∧ bt.1 = -1) ∨ (0 < g.goal ∧ 0 ≤ bt.1 ∧ bt.1.toNat < (trunkGoalBranches S g.plan g.goal).length)) ∧
    (trunkBranch S g.plan g.goal bt.1).2 ≠ LowerHistoryComparison.automatic ∧
    ∀ p ∈ g.parents, trunkTreeBoundFast S.rectangle (trunkResidualFast07 S g.plan p g.goal bt.1) bt.2

theorem trunkGroupValidFast07_imp (g : TrunkGroup) (h : trunkGroupValidFast07 g) :
    trunkGroupValid trunkCatalog 7 g := by
  unfold trunkGroupValidFast07 at h
  unfold trunkGroupValid
  dsimp only
  rw [hParEq07]
  obtain ⟨h1,h2,h3,h4⟩ := h
  refine ⟨h1,h2,h3,?_⟩
  intro bt hbt
  obtain ⟨ha,hb,hc⟩ := h4 bt hbt
  refine ⟨ha,hb,?_⟩
  intro p hp
  rw [← trunkResidualFast_eq07]
  exact (trunkTreeBoundFast_iff _ _ _).1 (hc p hp)

theorem key_07_200_207_c0 : ∀ j ∈ List.range 7, trunkGroupValidFast07 (trunkStateData07Part03.getD j ⟨0,[],0,[]⟩) := by
  unfold trunkGroupValidFast07 trunkResidualFast07
  decide +kernel

theorem key_07_200_207 (j : ℕ) (hj : j < 7) : trunkGroupValidFast07 (trunkStateData07Part03.getD j ⟨0,[],0,[]⟩) := by
  exact key_07_200_207_c0 j (List.mem_range.2 hj)

theorem hlen_07_200_207 : trunkStateData07Part03.length = 7 := by decide +kernel

theorem hlenPrev_07_200_207 : (trunkStateData07Part01++trunkStateData07Part02).length = 200 := by decide +kernel

theorem solution : trunkBindingBatch 7 200 207 := by
  intro i hlo hhi g hg
  rw [show (trunkCatalog.states 7).groups = trunkStateData07Part01++trunkStateData07Part02++trunkStateData07Part03 from rfl,
      List.getElem?_append_right (show 200 ≤ i by omega)] at hg
  rw [hlenPrev_07_200_207] at hg
  have hgi := key_07_200_207 (i - 200) (by omega)
  have hgv : trunkStateData07Part03.getD (i - 200) ⟨0,[],0,[]⟩ = g := by
    rw [List.getD_eq_getElem?_getD, hg]; rfl
  rw [hgv] at hgi
  exact trunkGroupValidFast07_imp g hgi
