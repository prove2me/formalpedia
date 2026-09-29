-- Prove2me | solution 1 for Freiman.middle_cert_family_equal_II_a_valid
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T12:43:36.000558+00:00
-- url     : https://prove2.me/submissions/24a020b7-07f4-485b-a9df-d5f76893dddc

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## Fast (balanced-split) list lookup, provably equal to `l[i]?` -/

def fam5Get? {α : Type} : ℕ → List α → ℕ → Option α
  | 0, l, i => l[i]?
  | d+1, l, i =>
    if i < l.length / 2 then fam5Get? d (l.take (l.length / 2)) i
    else fam5Get? d (l.drop (l.length / 2)) (i - l.length / 2)

theorem fam5Get?_eq {α : Type} : ∀ (d : ℕ) (l : List α) (i : ℕ), fam5Get? d l i = l[i]?
  | 0, l, i => rfl
  | d+1, l, i => by
    unfold fam5Get?
    split
    · rw [fam5Get?_eq d, List.getElem?_take_of_lt (by assumption)]
    · rw [fam5Get?_eq d, List.getElem?_drop, Nat.add_sub_cancel' (Nat.le_of_not_lt (by assumption))]

/-! ## Mirrored catalog accessors -/

def fam5Threshold (C : MiddleCertCatalog) (i : ℕ) : CertThreshold :=
  (fam5Get? 5 C.thresholds (i-1)).getD ⟨certDiagonalZero,certDiagonalZero,certDiagonalZero,certDiagonalZero,certDiagonalZero⟩
theorem fam5Threshold_eq : fam5Threshold = middleCertThreshold := by
  funext C i; simp only [fam5Threshold, middleCertThreshold, fam5Get?_eq]

def fam5Tail (C : MiddleCertCatalog) (i : ℕ) : CertField := (fam5Get? 2 C.tails (i-1)).getD certDiagonalZero
theorem fam5Tail_eq : fam5Tail = middleCertTail := by
  funext C i; simp only [fam5Tail, middleCertTail, fam5Get?_eq]

def fam5Endpoint (C : MiddleCertCatalog) (i : ℕ) : MiddleCertEndpoint :=
  (fam5Get? 3 C.endpoints (i-1)).getD ⟨([],[]),false,false,[]⟩
theorem fam5Endpoint_eq : fam5Endpoint = middleCertEndpoint := by
  funext C i; simp only [fam5Endpoint, middleCertEndpoint, fam5Get?_eq]

def fam5Goal (C : MiddleCertCatalog) (i : ℕ) : MiddleCertGoal :=
  (fam5Get? 3 C.goals (i-1)).getD ⟨0,.uniform,0,0,[],[]⟩
theorem fam5Goal_eq : fam5Goal = middleCertGoal := by
  funext C i; simp only [fam5Goal, middleCertGoal, fam5Get?_eq]

def fam5Witness (C : MiddleCertCatalog) (i : ℕ) : MiddleCertWitness :=
  (fam5Get? 7 C.witnesses (i-1)).getD ⟨0,0,0,[],0⟩
theorem fam5Witness_eq : fam5Witness = middleCertWitness := by
  funext C i; simp only [fam5Witness, middleCertWitness, fam5Get?_eq]

def fam5Proof (C : MiddleCertCatalog) (i : ℕ) : MiddleCertProof :=
  (fam5Get? 6 C.proofs (i-1)).getD (.pair ⟨⟨true,false,0⟩,⟨false,false,0⟩,0⟩)
theorem fam5Proof_eq : fam5Proof = middleCertProof := by
  funext C i; simp only [fam5Proof, middleCertProof, fam5Get?_eq]

def fam5Bound (C : MiddleCertCatalog) (b : MiddleCertBoundRef) : CertBound :=
  ⟨b.lower,b.strict,fam5Threshold C b.threshold⟩
theorem fam5Bound_eq : fam5Bound = middleCertBound := by
  funext C b; simp only [fam5Bound, middleCertBound, fam5Threshold_eq]

/-! ## Branches, keeping bound references instead of bounds -/

def fam5Cases (C : MiddleCertCatalog) (e : MiddleCertEndpoint) :
    List ((CertField × CertField) × List MiddleCertBoundRef) :=
  e.alternatives.map fun a => ((fam5Tail C a.x,fam5Tail C a.y),a.conditions)

def fam5Branches (C : MiddleCertCatalog) (g : MiddleCertGoal) :
    List (List MiddleCertBoundRef × LowerHistoryComparison) :=
  (fam5Cases C (fam5Endpoint C g.first)).flatMap fun (x,cx) =>
    (fam5Cases C (fam5Endpoint C g.second)).map fun (y,cy) =>
      (cx++cy,middleCertGreater (middleCertParity g.family) x y)

theorem fam5ActualCases_eq (C : MiddleCertCatalog) (e : MiddleCertEndpoint) :
    middleCertActualCases C e = (fam5Cases C e).map fun v => (v.1, middleCertBounds C v.2) := by
  simp only [middleCertActualCases, fam5Cases, List.map_map, Function.comp_def, fam5Tail_eq]

theorem fam5Branches_eq (C : MiddleCertCatalog) (g : MiddleCertGoal) :
    middleCertGoalBranches C g = (fam5Branches C g).map fun v => (middleCertBounds C v.1, v.2) := by
  simp only [middleCertGoalBranches, fam5Branches, fam5ActualCases_eq, fam5Endpoint_eq, List.flatMap_map,
    List.map_flatMap, List.map_map, Function.comp_def, middleCertBounds, List.map_append]

def fam5Branch (br : List (List MiddleCertBoundRef × LowerHistoryComparison)) (i : ℕ) :
    List MiddleCertBoundRef × LowerHistoryComparison := (fam5Get? 3 br i).getD ([],.impossible)

theorem fam5Branch_eq (C : MiddleCertCatalog) (g : MiddleCertGoal) (i : ℕ) :
    middleCertBranch C g i =
      (middleCertBounds C (fam5Branch (fam5Branches C g) i).1, (fam5Branch (fam5Branches C g) i).2) := by
  unfold middleCertBranch fam5Branch
  rw [fam5Branches_eq, List.getElem?_map, fam5Get?_eq]
  cases (fam5Branches C g)[i]? <;> rfl

theorem fam5Branches_length (C : MiddleCertCatalog) (g : MiddleCertGoal) :
    (middleCertGoalBranches C g).length = (fam5Branches C g).length := by
  rw [fam5Branches_eq, List.length_map]

/-! ## Proof validity -/

def fam5PairValid (C : MiddleCertCatalog) (p : MiddleCertPair) (direction : ℤ) : Prop :=
  0 < p.witness ∧ p.witness ≤ C.witnesses.length ∧
  p.lowerBound.lower = true ∧ p.upperBound.lower = false ∧
  p.lowerBound.threshold = (fam5Witness C p.witness).first ∧
  p.upperBound.threshold = (fam5Witness C p.witness).second ∧
  (fam5Witness C p.witness).direction = direction ∧
  (if direction = 0 then 0 < (fam5Witness C p.witness).lowerNumerator ∨
    p.lowerBound.strict = true ∨ p.upperBound.strict = true
   else p.lowerBound.strict = true ∨ p.upperBound.strict = true)
theorem fam5PairValid_eq : fam5PairValid = middleCertPairValid := by
  funext C p d; simp only [fam5PairValid, middleCertPairValid, fam5Witness_eq]

def fam5ProofValid (C : MiddleCertCatalog) : MiddleCertProof → Prop
  | .pair p => fam5PairValid C p 0
  | .diagonal a b => fam5PairValid C a 1 ∧ fam5PairValid C b (-1)
theorem fam5ProofValid_eq : fam5ProofValid = middleCertProofValid := by
  funext C p; cases p <;> simp only [fam5ProofValid, middleCertProofValid, fam5PairValid_eq]

instance fam5PairValid.dec (C : MiddleCertCatalog) (p : MiddleCertPair) (d : ℤ) : Decidable (fam5PairValid C p d) := by
  unfold fam5PairValid; infer_instance
instance fam5ProofValid.dec (C : MiddleCertCatalog) (p : MiddleCertProof) : Decidable (fam5ProofValid C p) := by
  cases p <;> unfold fam5ProofValid <;> infer_instance

/-! ## Record validity (explicit goal & branch table, reference-based membership) -/

def fam5TailEq (C : MiddleCertCatalog) (b : MiddleCertBoundRef) : LowerHistoryComparison → Prop
  | .bound c => fam5Bound C b = lowerHistoryComplement c
  | _ => False
instance fam5TailEq.dec (C : MiddleCertCatalog) (b : MiddleCertBoundRef) (v : LowerHistoryComparison) :
    Decidable (fam5TailEq C b v) := by
  cases v <;> unfold fam5TailEq <;> infer_instance

def fam5Parents (C : MiddleCertCatalog) (g : MiddleCertGoal) (parent : ℤ) : List MiddleCertBoundRef :=
  (fam5Get? 4 (C.parents (middleCertParity g.family)) parent.toNat).getD []

def fam5In (C : MiddleCertCatalog) (g : MiddleCertGoal) (v : List MiddleCertBoundRef × LowerHistoryComparison)
    (r : MiddleCertRecord) (b : MiddleCertBoundRef) : Prop :=
  b ∈ g.hypotheses ++ v.1 ∨ fam5TailEq C b v.2 ∨
  ∀ parent ∈ r.parents, ¬ parent < 0 ∧ b ∈ fam5Parents C g parent
instance fam5In.dec (C : MiddleCertCatalog) (g : MiddleCertGoal) (v : List MiddleCertBoundRef × LowerHistoryComparison)
    (r : MiddleCertRecord) (b : MiddleCertBoundRef) : Decidable (fam5In C g v r b) := by
  unfold fam5In; infer_instance

def fam5RecValid (C : MiddleCertCatalog) (g : MiddleCertGoal)
    (br : List (List MiddleCertBoundRef × LowerHistoryComparison)) (r : MiddleCertRecord) : Prop :=
  0 < r.goal ∧ r.goal ≤ C.goals.length ∧ 0 < r.proof ∧ r.proof ≤ C.proofs.length ∧
  r.branch < br.length ∧
  (fam5Branch br r.branch).2 ≠ .automatic ∧
  fam5ProofValid C (fam5Proof C r.proof) ∧
  (∀ parent ∈ r.parents, parent = -1 ∨ (0 ≤ parent ∧ parent.toNat < (C.parents (middleCertParity g.family)).length)) ∧
  ∀ p ∈ middleCertProofPairs (fam5Proof C r.proof),
    fam5In C g (fam5Branch br r.branch) r p.lowerBound ∧ fam5In C g (fam5Branch br r.branch) r p.upperBound
instance fam5RecValid.dec (C : MiddleCertCatalog) (g : MiddleCertGoal)
    (br : List (List MiddleCertBoundRef × LowerHistoryComparison)) (r : MiddleCertRecord) :
    Decidable (fam5RecValid C g br r) := by
  unfold fam5RecValid; infer_instance

theorem fam5In_mem (C : MiddleCertCatalog) (r : MiddleCertRecord) (b : MiddleCertBoundRef) (parent : ℤ)
    (hp : parent ∈ r.parents)
    (h : fam5In C (middleCertGoal C r.goal) (fam5Branch (fam5Branches C (middleCertGoal C r.goal)) r.branch) r b) :
    middleCertBound C b ∈ middleCertRecordConditions C r parent := by
  unfold middleCertRecordConditions
  dsimp only
  rw [fam5Branch_eq]
  simp only [List.mem_append]
  rcases h with h | h | h
  · simp only [List.mem_append] at h
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl (List.mem_map_of_mem h)))
    · exact Or.inl (Or.inl (Or.inr (List.mem_map_of_mem h)))
  · right
    revert h
    cases (fam5Branch (fam5Branches C (middleCertGoal C r.goal)) r.branch).2 with
    | automatic => intro h; exact h.elim
    | impossible => intro h; exact h.elim
    | bound c => intro h; rw [← fam5Bound_eq, h]; exact List.mem_singleton_self _
  · obtain ⟨hneg, hb⟩ := h parent hp
    left; right
    rw [if_neg hneg]
    unfold fam5Parents at hb
    rw [fam5Get?_eq] at hb
    exact List.mem_map_of_mem hb

theorem fam5RecValid_imp (C : MiddleCertCatalog) (r : MiddleCertRecord)
    (h : fam5RecValid C (middleCertGoal C r.goal) (fam5Branches C (middleCertGoal C r.goal)) r) :
    middleCertRecordValid C r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
  · rw [fam5Branches_length]; exact h5
  · rw [fam5Branch_eq]; exact h6
  · rw [← fam5ProofValid_eq, ← fam5Proof_eq]; exact h7
  · intro parent hp
    refine ⟨h8 parent hp, ?_⟩
    intro p hp'
    rw [← fam5Proof_eq] at hp'
    obtain ⟨hl, hu⟩ := h9 p hp'
    exact ⟨fam5In_mem C r p.lowerBound parent hp hl, fam5In_mem C r p.upperBound parent hp hu⟩

/-! ## Bitmask coverage lemmas -/

theorem fam5_foldl_testBit {α : Type} (P : α → Bool) (f : α → ℕ) (k : ℕ) :
    ∀ (L : List α) (acc : ℕ),
      (L.foldl (fun m x => if P x then m ||| f x else m) acc).testBit k = true →
      acc.testBit k = true ∨ ∃ x ∈ L, P x = true ∧ (f x).testBit k = true
  | [], acc, h => Or.inl h
  | x :: L, acc, h => by
    simp only [List.foldl_cons] at h
    rcases fam5_foldl_testBit P f k L _ h with h | ⟨y, hy, hPy, hfy⟩
    · by_cases hP : P x = true
      · rw [if_pos hP, Nat.testBit_or, Bool.or_eq_true] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_self .., hP, h⟩
      · rw [if_neg hP] at h
        exact Or.inl h
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hPy, hfy⟩

theorem fam5_testBit_one_shift (n k : ℕ) (h : (1 <<< n).testBit k = true) : k = n := by
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff, Nat.testBit_one_eq_true_iff_self_eq_zero] at h
  omega

def fam5ParMask (ps : List ℤ) : ℕ :=
  ps.foldl (fun m (p : ℤ) => if decide (0 ≤ p) then m ||| (1 <<< p.toNat) else m) 0
theorem fam5ParMask_mem (ps : List ℤ) (k : ℕ) (h : (fam5ParMask ps).testBit k = true) : (k:ℤ) ∈ ps := by
  unfold fam5ParMask at h
  rcases fam5_foldl_testBit (fun p : ℤ => decide (0 ≤ p)) (fun p : ℤ => 1 <<< p.toNat) k ps 0 h with h | ⟨p, hp, hP, hf⟩
  · rw [Nat.zero_testBit] at h; exact absurd h Bool.false_ne_true
  · have hk := fam5_testBit_one_shift _ _ hf
    rw [decide_eq_true_iff] at hP
    have : (k:ℤ) = p := by rw [hk, Int.toNat_of_nonneg hP]
    rw [this]; exact hp

def fam5CovMask (L : List MiddleCertRecord) : ℕ :=
  L.foldl (fun m r => if decide ((-1:ℤ) ∈ r.parents) then m ||| (1 <<< r.branch) else m) 0
theorem fam5CovMask_mem (L : List MiddleCertRecord) (j : ℕ) (h : (fam5CovMask L).testBit j = true) :
    ∃ r ∈ L, r.branch = j ∧ (-1:ℤ) ∈ r.parents := by
  rcases fam5_foldl_testBit _ _ j L 0 h with h | ⟨r, hr, hP, hf⟩
  · rw [Nat.zero_testBit] at h; exact absurd h Bool.false_ne_true
  · exact ⟨r, hr, (fam5_testBit_one_shift _ _ hf).symm, decide_eq_true_iff.1 hP⟩

def fam5BranchMask (L : List MiddleCertRecord) (j : ℕ) : ℕ :=
  L.foldl (fun m r => if decide (r.branch = j) then m ||| fam5ParMask r.parents else m) 0
theorem fam5BranchMask_mem (L : List MiddleCertRecord) (j k : ℕ) (h : (fam5BranchMask L j).testBit k = true) :
    ∃ r ∈ L, r.branch = j ∧ (k:ℤ) ∈ r.parents := by
  rcases fam5_foldl_testBit _ _ k L 0 h with h | ⟨r, hr, hP, hf⟩
  · rw [Nat.zero_testBit] at h; exact absurd h Bool.false_ne_true
  · exact ⟨r, hr, decide_eq_true_iff.1 hP, fam5ParMask_mem _ _ hf⟩

/-- branches having at least one record with real parents (used only as a pruning guard) -/
def fam5HasParMask (L : List MiddleCertRecord) : ℕ :=
  L.foldl (fun m r => if decide (¬ (-1:ℤ) ∈ r.parents) then m ||| (1 <<< r.branch) else m) 0

/-! ## Local decidability instances for the original predicates (spec matching) -/
local instance (C : MiddleCertCatalog) (g : MiddleCertGoal) (sp : MiddleCertSpec) :
    Decidable (middleCertGoalMatches C g sp) := by
  unfold middleCertGoalMatches
  infer_instance


theorem solution : middleCertFamilyValid middleCertData 5 := by
  unfold middleCertFamilyValid
  refine ⟨?_, ?_, ?_⟩
  · -- spec matching
    decide +kernel
  · -- record validity
    have hR0 : ∀ r ∈ middleCertRecords0, r.goal < 83 := by decide +kernel
    have hR1 : ∀ r ∈ middleCertRecords1, r.goal < 83 := by decide +kernel
    have hR4 : ∀ r ∈ middleCertRecords4, 97 < r.goal := by decide +kernel
    have hG : ∀ g, (middleCertGoal middleCertData g).family = 5 → g ∈ [83,84,85,86,87,88,89,90,91,92,93,94,95,96,97] := by
      intro g hg
      by_cases hlt : g < 152
      · have key : ∀ g ∈ List.range 152, (fam5Goal middleCertData g).family = 5 → g ∈ [83,84,85,86,87,88,89,90,91,92,93,94,95,96,97] := by
          decide +kernel
        exact key g (List.mem_range.2 hlt) (by rw [fam5Goal_eq]; exact hg)
      · exfalso
        have hlen : middleCertData.goals.length = 151 := by decide +kernel
        unfold middleCertGoal at hg
        rw [List.getElem?_eq_none (by omega)] at hg
        exact absurd hg (by decide)
    have hV2 : ∀ g ∈ [83,84,85,86,87,88,89,90,91,92,93,94,95,96,97], ∀ r ∈ middleCertRecords2.filter (fun r => decide (r.goal = g)),
        fam5RecValid middleCertData (fam5Goal middleCertData g) (fam5Branches middleCertData (fam5Goal middleCertData g)) r := by
      decide +kernel
    have hV3 : ∀ g ∈ [83,84,85,86,87,88,89,90,91,92,93,94,95,96,97], ∀ r ∈ middleCertRecords3.filter (fun r => decide (r.goal = g)),
        fam5RecValid middleCertData (fam5Goal middleCertData g) (fam5Branches middleCertData (fam5Goal middleCertData g)) r := by
      decide +kernel
    have hGr : ∀ g ∈ [83,84,85,86,87,88,89,90,91,92,93,94,95,96,97], 83 ≤ g ∧ g ≤ 97 := by decide
    intro r hr hf
    have hg := hG r.goal hf
    have hgr := hGr r.goal hg
    change r ∈ middleCertRecords at hr
    unfold middleCertRecords at hr
    simp only [List.mem_append] at hr
    rcases hr with (((hr | hr) | hr) | hr) | hr
    · have := hR0 r hr; omega
    · have := hR1 r hr; omega
    · have := hV2 r.goal hg r (List.mem_filter.2 ⟨hr, decide_eq_true rfl⟩)
      rw [fam5Goal_eq] at this
      exact fam5RecValid_imp middleCertData r this
    · have := hV3 r.goal hg r (List.mem_filter.2 ⟨hr, decide_eq_true rfl⟩)
      rw [fam5Goal_eq] at this
      exact fam5RecValid_imp middleCertData r this
    · have := hR4 r hr; omega
  · -- branch coverage
    have key3 : ∀ i ∈ List.range middleCertData.goals.length, (fam5Goal middleCertData (i+1)).family = 5 →
        ∀ j ∈ List.range (fam5Branches middleCertData (fam5Goal middleCertData (i+1))).length,
          (fam5CovMask (middleCertRecords2.filter (fun r => decide (r.goal = i+1)) ++ middleCertRecords3.filter (fun r => decide (r.goal = i+1)))).testBit j = true ∨
          ((fam5HasParMask (middleCertRecords2.filter (fun r => decide (r.goal = i+1)) ++ middleCertRecords3.filter (fun r => decide (r.goal = i+1)))).testBit j = true ∧
            ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length, (fam5BranchMask (middleCertRecords2.filter (fun r => decide (r.goal = i+1)) ++ middleCertRecords3.filter (fun r => decide (r.goal = i+1))) j).testBit k = true) ∨
          (fam5Branch (fam5Branches middleCertData (fam5Goal middleCertData (i+1))) j).2 = .automatic := by
      decide +kernel
    have hsub : ∀ i r, r ∈ (middleCertRecords2.filter (fun r => decide (r.goal = i+1)) ++ middleCertRecords3.filter (fun r => decide (r.goal = i+1))) → r ∈ middleCertData.records ∧ r.goal = i+1 := by
      intro i r hr
      simp only [List.mem_append, List.mem_filter, decide_eq_true_iff] at hr
      refine ⟨?_, by rcases hr with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h⟩
      show r ∈ middleCertRecords
      unfold middleCertRecords
      simp only [List.mem_append]
      rcases hr with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
    intro i hi hf j hj
    rw [← fam5Goal_eq] at hf
    have hj' : j ∈ List.range (fam5Branches middleCertData (fam5Goal middleCertData (i+1))).length := by
      rw [fam5Goal_eq, ← fam5Branches_length]; exact hj
    rcases key3 i hi hf j hj' with h | ⟨_, h⟩ | h
    · right; left
      obtain ⟨r, hr, hb, hp⟩ := fam5CovMask_mem _ _ h
      obtain ⟨hmem, hgoal⟩ := hsub i r hr
      exact ⟨r, hmem, hgoal, hb, hp⟩
    · right; right
      refine ⟨by norm_num, fun k hk => ?_⟩
      obtain ⟨r, hr, hb, hp⟩ := fam5BranchMask_mem _ _ _ (h k hk)
      obtain ⟨hmem, hgoal⟩ := hsub i r hr
      exact ⟨r, hmem, hgoal, hb, hp⟩
    · left
      rw [fam5Branch_eq, fam5Goal_eq] at *
      exact h
