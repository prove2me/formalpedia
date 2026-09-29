-- Prove2me | solution 1 for CubicP3Partition.R03SP01TwoFactorTwoCycleP3FactorOfCover
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:31:17.622053+00:00
-- url     : https://prove2.me/submissions/699d9180-8a27-428f-9026-4e1132c65343

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition
open SimpleGraph
universe u
set_option maxHeartbeats 1000000

/-- Candidate assembly lemma: three local ordered paths in each residual block,
    plus a two-edge exceptional block, give a canonical P3 factor. -/
theorem R03SP01ThreePieceCrossAssembly
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : (Fin (kA * 3) ⊕ Fin 1) ≃ A)
    (eB : (Fin (kB * 3) ⊕ Fin 2) ≃ B)
    (edgeA : ∀ b : Fin kA,
      G.Adj (Sum.inl (eA (Sum.inl (finProdFinEquiv (b, 0)))))
        (Sum.inl (eA (Sum.inl (finProdFinEquiv (b, 1))))) ∧
      G.Adj (Sum.inl (eA (Sum.inl (finProdFinEquiv (b, 1)))))
        (Sum.inl (eA (Sum.inl (finProdFinEquiv (b, 2))))))
    (edgeB : ∀ b : Fin kB,
      G.Adj (Sum.inr (eB (Sum.inl (finProdFinEquiv (b, 0)))))
        (Sum.inr (eB (Sum.inl (finProdFinEquiv (b, 1))))) ∧
      G.Adj (Sum.inr (eB (Sum.inl (finProdFinEquiv (b, 1)))))
        (Sum.inr (eB (Sum.inl (finProdFinEquiv (b, 2))))))
    (cross01 : G.Adj (Sum.inl (eA (Sum.inr 0)))
      (Sum.inr (eB (Sum.inr 0))))
    (cross12 : G.Adj (Sum.inr (eB (Sum.inr 0)))
      (Sum.inr (eB (Sum.inr 1)))) :
    Nonempty (P3Factor G) := by
  let crossPlace : Fin 3 → A ⊕ B := fun j =>
    if j = 0 then Sum.inl (eA (Sum.inr 0))
    else if j = 1 then Sum.inr (eB (Sum.inr 0))
    else Sum.inr (eB (Sum.inr 1))
  let targetFun : ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) → A ⊕ B := fun x =>
    match x with
    | Sum.inl (Sum.inl j) => crossPlace j
    | Sum.inl (Sum.inr a) => Sum.inl (eA (Sum.inl a))
    | Sum.inr b => Sum.inr (eB (Sum.inl b))
  let targetInv : (A ⊕ B) → ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) := fun z =>
    match z with
    | Sum.inl a =>
      match eA.symm a with
      | Sum.inl r => Sum.inl (Sum.inr r)
      | Sum.inr _ => Sum.inl (Sum.inl 0)
    | Sum.inr b =>
      match eB.symm b with
      | Sum.inl r => Sum.inr r
      | Sum.inr r => if r = 0 then Sum.inl (Sum.inl 1) else Sum.inl (Sum.inl 2)
  let targetEquiv : ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) ≃ (A ⊕ B) := {
    toFun := targetFun
    invFun := targetInv
    left_inv := by
      intro x
      rcases x with x | x
      · rcases x with x | x
        · fin_cases x <;> simp [targetInv, targetFun, crossPlace]
        · simp [targetInv, targetFun, crossPlace]
      · simp [targetInv, targetFun, crossPlace]
    right_inv := by
      intro z
      rcases z with z | z
      · generalize hr : eA.symm z = r
        rcases r with r | r
        · have hz : z = eA (Sum.inl r) := by
            rw [← eA.apply_symm_apply z, hr]
          simp [targetInv, targetFun, crossPlace, hz]
        · have hz : z = eA (Sum.inr r) := by
            rw [← eA.apply_symm_apply z, hr]
          simpa [targetInv, targetFun, crossPlace, hz] using
            (Subsingleton.elim (0 : Fin 1) r)
      · generalize hr : eB.symm z = r
        rcases r with r | r
        · have hz : z = eB (Sum.inl r) := by
            rw [← eB.apply_symm_apply z, hr]
          simp [targetInv, targetFun, crossPlace, hz]
        · have hz : z = eB (Sum.inr r) := by
            rw [← eB.apply_symm_apply z, hr]
          fin_cases r <;> simp [targetInv, targetFun, crossPlace, hz]
  }
  let indexFun : (Fin (1 + kA + kB) × Fin 3) →
      ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) := fun q =>
    Fin.addCases
      (fun b => Fin.addCases
        (fun _ => Sum.inl (Sum.inl q.2))
        (fun a => Sum.inl (Sum.inr (finProdFinEquiv (a, q.2)))) b)
      (fun b => Sum.inr (finProdFinEquiv (b, q.2))) q.1
  let indexInv : (((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3))) →
      (Fin (1 + kA + kB) × Fin 3) := fun x =>
    match x with
    | Sum.inl (Sum.inl j) => (Fin.castAdd kB (Fin.castAdd kA 0), j)
    | Sum.inl (Sum.inr r) =>
      let p := finProdFinEquiv.symm r
      (Fin.castAdd kB (Fin.natAdd 1 p.1), p.2)
    | Sum.inr r =>
      let p := finProdFinEquiv.symm r
      (Fin.natAdd (1 + kA) p.1, p.2)
  let indexEquiv : (Fin (1 + kA + kB) × Fin 3) ≃
      ((Fin 3 ⊕ Fin (kA * 3)) ⊕ Fin (kB * 3)) := {
    toFun := indexFun
    invFun := indexInv
    left_inv := by
      intro q
      rcases q with ⟨b,j⟩
      refine Fin.addCases (fun b => ?_) (fun b => ?_) b
      · refine Fin.addCases (fun b => ?_) (fun b => ?_) b
        · fin_cases b
          simp [indexInv, indexFun]
        · have hprod := finProdFinEquiv.left_inv (b, j)
          have hprod' : (finProdFinEquiv (b, j)).divNat = b ∧
              (finProdFinEquiv (b, j)).modNat = j :=
            ⟨congrArg Prod.fst hprod, congrArg Prod.snd hprod⟩
          simp [indexInv, indexFun, Fin.addCases_left, Fin.addCases_right, hprod']
      · have hprod := finProdFinEquiv.left_inv (b, j)
        have hprod' : (finProdFinEquiv (b, j)).divNat = b ∧
            (finProdFinEquiv (b, j)).modNat = j :=
          ⟨congrArg Prod.fst hprod, congrArg Prod.snd hprod⟩
        simp [indexInv, indexFun, Fin.addCases_right, hprod']
    right_inv := by
      intro x
      rcases x with x | x
      · rcases x with x | x
        · simp [indexInv, indexFun]
        · simpa [indexInv, indexFun, Fin.addCases_left, Fin.addCases_right] using
            (finProdFinEquiv.right_inv x)
      · simpa [indexInv, indexFun, Fin.addCases_left, Fin.addCases_right] using
          (finProdFinEquiv.right_inv x)
  }
  let place : (Fin (1 + kA + kB) × Fin 3) ≃ (A ⊕ B) :=
    indexEquiv.trans targetEquiv
  refine ⟨{
    blockCount := 1 + kA + kB
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro b
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · refine Fin.addCases (fun b => ?_) (fun b => ?_) b
      · fin_cases b
        simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
          Fin.addCases_left, Fin.addCases_right] using cross01
      · have h := (edgeA b).1
        simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
          finProdFinEquiv, Fin.addCases_left, Fin.addCases_right] using h
    · have h := (edgeB b).1
      simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
        finProdFinEquiv, Fin.addCases_left, Fin.addCases_right] using h
  · intro b
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · refine Fin.addCases (fun b => ?_) (fun b => ?_) b
      · fin_cases b
        simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
          Fin.addCases_left, Fin.addCases_right] using cross12
      · have h := (edgeA b).2
        simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
          finProdFinEquiv, Fin.addCases_left, Fin.addCases_right] using h
    · have h := (edgeB b).2
      simpa [place, indexEquiv, indexFun, targetEquiv, targetFun, crossPlace,
        finProdFinEquiv, Fin.addCases_left, Fin.addCases_right] using h

#print axioms R03SP01ThreePieceCrossAssembly

/-- Candidate two-cycle residue construction.  A cycle of order 1 modulo 3
    and a cycle of order 2 modulo 3 are cut at a cross edge and tiled by the
    preceding assembly lemma. -/
theorem R03SP01TwoCycleResidueAssembly
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (2 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (kA * 3 - 1),
      G.Adj (Sum.inl (eA ⟨1 + i.val, by omega⟩))
        (Sum.inl (eA ⟨1 + (i.val + 1), by omega⟩)))
    (cycleB : ∀ i : Fin (kB * 3 - 1),
      G.Adj (Sum.inr (eB ⟨2 + i.val, by omega⟩))
        (Sum.inr (eB ⟨2 + (i.val + 1), by omega⟩)))
    (cross01 : G.Adj (Sum.inl (eA 0)) (Sum.inr (eB 0)))
    (cross12 : G.Adj (Sum.inr (eB 0)) (Sum.inr (eB 1))) :
    Nonempty (P3Factor G) := by
  let shiftA : (Fin (kA * 3) ⊕ Fin 1) ≃ Fin (1 + kA * 3) :=
    finSumFinEquiv.trans (finAddFlip (m := kA * 3) (n := 1))
  let shiftB : (Fin (kB * 3) ⊕ Fin 2) ≃ Fin (2 + kB * 3) :=
    finSumFinEquiv.trans (finAddFlip (m := kB * 3) (n := 2))
  let blockA : (Fin (kA * 3) ⊕ Fin 1) ≃ A := shiftA.trans eA
  let blockB : (Fin (kB * 3) ⊕ Fin 2) ≃ B := shiftB.trans eB
  have hshiftA_left (r : Fin (kA * 3)) :
      shiftA (Sum.inl r) = Fin.natAdd 1 r := by
    simp [shiftA, finSumFinEquiv, finAddFlip]
  have hshiftA_right (r : Fin 1) :
      shiftA (Sum.inr r) = Fin.castAdd (kA * 3) r := by
    simp [shiftA, finSumFinEquiv, finAddFlip]
  have hshiftB_left (r : Fin (kB * 3)) :
      shiftB (Sum.inl r) = Fin.natAdd 2 r := by
    simp [shiftB, finSumFinEquiv, finAddFlip]
  have hshiftB_right (r : Fin 2) :
      shiftB (Sum.inr r) = Fin.castAdd (kB * 3) r := by
    simp [shiftB, finSumFinEquiv, finAddFlip]
  have hblockA (b : Fin kA) (j : Fin 3) :
      blockA (Sum.inl (finProdFinEquiv (b, j))) =
        eA (Fin.natAdd 1 (finProdFinEquiv (b, j))) := by
    simp only [blockA, Equiv.trans_apply]
    rw [hshiftA_left]
  have hblockB (b : Fin kB) (j : Fin 3) :
      blockB (Sum.inl (finProdFinEquiv (b, j))) =
        eB (Fin.natAdd 2 (finProdFinEquiv (b, j))) := by
    simp only [blockB, Equiv.trans_apply]
    rw [hshiftB_left]
  have hblockA0 : blockA (Sum.inr (0 : Fin 1)) = eA 0 := by
    simp only [blockA, Equiv.trans_apply]
    rw [hshiftA_right]
    rfl
  have hblockB0 : blockB (Sum.inr (0 : Fin 2)) = eB 0 := by
    simp only [blockB, Equiv.trans_apply]
    rw [hshiftB_right]
    rfl
  have hblockB1 : blockB (Sum.inr (1 : Fin 2)) = eB 1 := by
    simp only [blockB, Equiv.trans_apply]
    rw [hshiftB_right]
    apply congrArg eB
    apply Fin.ext
    norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + kB * 3)]
  have hA : ∀ b : Fin kA,
      G.Adj (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      G.Adj (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    have hb := b.is_lt
    constructor
    · have hi : (finProdFinEquiv (b, (0 : Fin 3))).val + 1 < kA * 3 := by
        simp [finProdFinEquiv]
        omega
      have h := cycleA ⟨(finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩
      have h0 : blockA (Sum.inl (finProdFinEquiv (b, (0 : Fin 3)))) =
          eA ⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩ := by
        rw [hblockA]
        apply congrArg eA
        apply Fin.ext
        rfl
      have h1 : blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))) =
          eA ⟨1 + ((finProdFinEquiv (b, (0 : Fin 3))).val + 1), by omega⟩ := by
        rw [hblockA]
        apply congrArg eA
        apply Fin.ext
        simp [finProdFinEquiv]
        omega
      rw [h0, h1]
      exact h
    · have hi : (finProdFinEquiv (b, (1 : Fin 3))).val + 1 < kA * 3 := by
        simp [finProdFinEquiv]
        omega
      have h := cycleA ⟨(finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩
      have h1 : blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))) =
          eA ⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩ := by
        rw [hblockA]
        apply congrArg eA
        apply Fin.ext
        rfl
      have h2 : blockA (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))) =
          eA ⟨1 + ((finProdFinEquiv (b, (1 : Fin 3))).val + 1), by omega⟩ := by
        rw [hblockA]
        apply congrArg eA
        apply Fin.ext
        simp [finProdFinEquiv]
        omega
      rw [h1, h2]
      exact h
  have hB : ∀ b : Fin kB,
      G.Adj (Sum.inr (blockB (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inr (blockB (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      G.Adj (Sum.inr (blockB (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inr (blockB (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    have hb := b.is_lt
    constructor
    · have hi : (finProdFinEquiv (b, (0 : Fin 3))).val + 1 < kB * 3 := by
        simp [finProdFinEquiv]
        omega
      have h := cycleB ⟨(finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩
      have h0 : blockB (Sum.inl (finProdFinEquiv (b, (0 : Fin 3)))) =
          eB ⟨2 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩ := by
        rw [hblockB]
        apply congrArg eB
        apply Fin.ext
        rfl
      have h1 : blockB (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))) =
          eB ⟨2 + ((finProdFinEquiv (b, (0 : Fin 3))).val + 1), by omega⟩ := by
        rw [hblockB]
        apply congrArg eB
        apply Fin.ext
        simp [finProdFinEquiv]
        omega
      rw [h0, h1]
      exact h
    · have hi : (finProdFinEquiv (b, (1 : Fin 3))).val + 1 < kB * 3 := by
        simp [finProdFinEquiv]
        omega
      have h := cycleB ⟨(finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩
      have h1 : blockB (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))) =
          eB ⟨2 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩ := by
        rw [hblockB]
        apply congrArg eB
        apply Fin.ext
        rfl
      have h2 : blockB (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))) =
          eB ⟨2 + ((finProdFinEquiv (b, (1 : Fin 3))).val + 1), by omega⟩ := by
        rw [hblockB]
        apply congrArg eB
        apply Fin.ext
        simp [finProdFinEquiv]
        omega
      rw [h1, h2]
      exact h
  have hcross01 : G.Adj (Sum.inl (blockA (Sum.inr (0 : Fin 1))))
      (Sum.inr (blockB (Sum.inr (0 : Fin 2)))) := by
    rw [hblockA0, hblockB0]
    exact cross01
  have hcross12 : G.Adj (Sum.inr (blockB (Sum.inr (0 : Fin 2))))
      (Sum.inr (blockB (Sum.inr (1 : Fin 2)))) := by
    rw [hblockB0, hblockB1]
    exact cross12
  exact R03SP01ThreePieceCrossAssembly G kA kB blockA blockB hA hB hcross01 hcross12

#print axioms R03SP01TwoCycleResidueAssembly

/-- The same residue construction with actual cyclic successor hypotheses.
    The cyclic wrap edges are stronger than needed for the residual tiling, but
    make the two-cycle interpretation explicit. -/
theorem R03SP01TwoCycleCyclicOrderAssembly
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (2 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cross01 : G.Adj (Sum.inl (eA 0)) (Sum.inr (eB 0)))
    (cross12 : G.Adj (Sum.inr (eB 0)) (Sum.inr (eB 1))) :
    Nonempty (P3Factor G) := by
  have pathA : ∀ i : Fin (kA * 3 - 1),
      G.Adj (Sum.inl (eA ⟨1 + i.val, by omega⟩))
        (Sum.inl (eA ⟨1 + (i.val + 1), by omega⟩)) := by
    intro i
    have hi := i.is_lt
    have h := cycleA ⟨1 + i.val, by omega⟩
    have hs :
        (⟨((1 + i.val) + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩ : Fin (1 + kA * 3)) =
          ⟨1 + (i.val + 1), by omega⟩ := by
      apply Fin.ext
      calc
        ((1 + i.val) + 1) % (1 + kA * 3) = (1 + i.val) + 1 :=
          Nat.mod_eq_of_lt (by omega)
        _ = 1 + (i.val + 1) := by omega
    rw [hs] at h
    exact h
  have pathB : ∀ i : Fin (kB * 3 - 1),
      G.Adj (Sum.inr (eB ⟨2 + i.val, by omega⟩))
        (Sum.inr (eB ⟨2 + (i.val + 1), by omega⟩)) := by
    intro i
    have hi := i.is_lt
    have h := cycleB ⟨2 + i.val, by omega⟩
    have hs :
        (⟨((2 + i.val) + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩ : Fin (2 + kB * 3)) =
          ⟨2 + (i.val + 1), by omega⟩ := by
      apply Fin.ext
      calc
        ((2 + i.val) + 1) % (2 + kB * 3) = (2 + i.val) + 1 :=
          Nat.mod_eq_of_lt (by omega)
        _ = 2 + (i.val + 1) := by omega
    rw [hs] at h
    exact h
  exact R03SP01TwoCycleResidueAssembly G kA kB eA eB pathA pathB cross01 cross12

#print axioms R03SP01TwoCycleCyclicOrderAssembly

/-- Symmetric residue orientation: the order-2 side is named first. -/
theorem R03SP01TwoCycleCyclicOrderAssemblySwap
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (2 + kA * 3) ≃ A)
    (eB : Fin (1 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cross01 : G.Adj (Sum.inl (eA 0)) (Sum.inr (eB 0)))
    (cross12 : G.Adj (Sum.inl (eA 0)) (Sum.inl (eA 1))) :
    Nonempty (P3Factor G) := by
  let Gswap : SimpleGraph (B ⊕ A) := G.comap (Equiv.sumComm B A)
  have hcycleA : ∀ i : Fin (1 + kB * 3),
      Gswap.Adj (Sum.inl (eB i))
        (Sum.inl (eB ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    simpa [Gswap] using cycleB i
  have hcycleB : ∀ i : Fin (2 + kA * 3),
      Gswap.Adj (Sum.inr (eA i))
        (Sum.inr (eA ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    simpa [Gswap] using cycleA i
  have hcross01 : Gswap.Adj (Sum.inl (eB 0)) (Sum.inr (eA 0)) := by
    simpa [Gswap] using cross01.symm
  have hcross12 : Gswap.Adj (Sum.inr (eA 0)) (Sum.inr (eA 1)) := by
    simpa [Gswap] using cross12
  obtain ⟨p⟩ := R03SP01TwoCycleCyclicOrderAssembly
    Gswap kB kA eB eA hcycleA hcycleB hcross01 hcross12
  let swap : (B ⊕ A) ≃ (A ⊕ B) := Equiv.sumComm B A
  refine ⟨{
    blockCount := p.blockCount
    place := p.place.trans swap
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    have h := p.edge01 i
    simpa [Gswap, swap] using h
  · intro i
    have h := p.edge12 i
    simpa [Gswap, swap] using h

#print axioms R03SP01TwoCycleCyclicOrderAssemblySwap

/-- A walk crossing from the first summand to the second contains a cross edge. -/
theorem R03SP01ExistsCrossEdgeOfConnected
    {A B : Type u} (G : SimpleGraph (A ⊕ B))
    (a0 : A) (b0 : B) (hconn : G.Connected) :
    ∃ a : A, ∃ b : B, G.Adj (Sum.inl a) (Sum.inr b) := by
  let rec walkCross (a : A) (b : B) (p : G.Walk (Sum.inl a) (Sum.inr b)) :
      ∃ a' : A, ∃ b' : B, G.Adj (Sum.inl a') (Sum.inr b') := by
    obtain ⟨w, h, q, hpq⟩ := Walk.exists_eq_cons_of_ne (by simp) p
    cases w with
    | inl a' => exact walkCross a' b q
    | inr b' => exact ⟨a, b', h⟩
  termination_by p.length
  decreasing_by
    simp_all [Walk.length_cons]
  obtain ⟨hp⟩ := hconn (Sum.inl a0) (Sum.inr b0)
  exact walkCross _ _ hp

/-- Cyclic successor edges are preserved by shifting the chosen origin. -/
theorem R03SP01ShiftCyclicOrder
    {X : Type u} {n : Nat} (R : X → X → Prop)
    (e : Fin n ≃ X) (hn : 0 < n)
    (cycle : ∀ i : Fin n, R (e i)
      (e ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩))
    (s : Fin n) :
    ∀ i : Fin n, R ((finCycle s).trans e i)
      (((finCycle s).trans e) ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  intro i
  have h := cycle (finCycle s i)
  have hi : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = i + 1 := by
    ext
    simp [Fin.val_add]
  have hs : finCycle s (i + 1) = finCycle s i + 1 := by
    ext
    simp [finCycle_apply, Fin.add_def]
    ac_rfl
  have hsucc (j : Fin n) :
      (⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = j + 1 := by
    ext
    simp [Fin.val_add]
  rw [hsucc (finCycle s i)] at h
  simpa [Equiv.trans_apply, hi, hs] using h

/-- Connectedness supplies the exceptional cross edge after cyclic origins are shifted. -/
theorem R03SP01TwoCycleCyclicOrderAssemblyConnected
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (2 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨a, b, hab⟩ := R03SP01ExistsCrossEdgeOfConnected
    G (eA 0) (eB 0) hconn
  let sA : Fin (1 + kA * 3) := eA.symm a
  let sB : Fin (2 + kB * 3) := eB.symm b
  letI : NeZero (1 + kA * 3) := ⟨by omega⟩
  letI : NeZero (2 + kB * 3) := ⟨by omega⟩
  let eA' : Fin (1 + kA * 3) ≃ A := (finCycle sA).trans eA
  let eB' : Fin (2 + kB * 3) ≃ B := (finCycle sB).trans eB
  have heA0 : eA' 0 = a := by
    simp [eA', sA]
  have heB0 : eB' 0 = b := by
    simp [eB', sB]
  have hcycleA' : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA' i))
        (Sum.inl (eA' ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eA'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inl x) (Sum.inl y)) eA (by omega) cycleA sA
  have hcycleB' : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB' i))
        (Sum.inr (eB' ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eB'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inr x) (Sum.inr y)) eB (by omega) cycleB sB
  have hcross01' : G.Adj (Sum.inl (eA' 0)) (Sum.inr (eB' 0)) := by
    rw [heA0, heB0]
    exact hab
  have hcross12' : G.Adj (Sum.inr (eB' 0)) (Sum.inr (eB' 1)) := by
    have h := hcycleB' 0
    have hnext : (⟨((0 : Fin (2 + kB * 3)).val + 1) % (2 + kB * 3),
        Nat.mod_lt _ (by omega)⟩ : Fin (2 + kB * 3)) = 1 := by
      ext
      simp
    rw [hnext] at h
    exact h
  exact R03SP01TwoCycleCyclicOrderAssembly
    G kA kB eA' eB' hcycleA' hcycleB' hcross01' hcross12'

#print axioms R03SP01ExistsCrossEdgeOfConnected
#print axioms R03SP01ShiftCyclicOrder
#print axioms R03SP01TwoCycleCyclicOrderAssemblyConnected

/-- Connectedness version with the order-2 residue on the first summand. -/
theorem R03SP01TwoCycleCyclicOrderAssemblyConnectedSwap
    {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph (A ⊕ B))
    (kA kB : Nat)
    (eA : Fin (2 + kA * 3) ≃ A)
    (eB : Fin (1 + kB * 3) ≃ B)
    (cycleA : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)))
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨a, b, hab⟩ := R03SP01ExistsCrossEdgeOfConnected
    G (eA 0) (eB 0) hconn
  let sA : Fin (2 + kA * 3) := eA.symm a
  let sB : Fin (1 + kB * 3) := eB.symm b
  letI : NeZero (2 + kA * 3) := ⟨by omega⟩
  letI : NeZero (1 + kB * 3) := ⟨by omega⟩
  let eA' : Fin (2 + kA * 3) ≃ A := (finCycle sA).trans eA
  let eB' : Fin (1 + kB * 3) ≃ B := (finCycle sB).trans eB
  have heA0 : eA' 0 = a := by
    simp [eA', sA]
  have heB0 : eB' 0 = b := by
    simp [eB', sB]
  have hcycleA' : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA' i))
        (Sum.inl (eA' ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eA'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inl x) (Sum.inl y)) eA (by omega) cycleA sA
  have hcycleB' : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (eB' i))
        (Sum.inr (eB' ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eB'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inr x) (Sum.inr y)) eB (by omega) cycleB sB
  have hcross01' : G.Adj (Sum.inl (eA' 0)) (Sum.inr (eB' 0)) := by
    rw [heA0, heB0]
    exact hab
  have hcross12' : G.Adj (Sum.inl (eA' 0)) (Sum.inl (eA' 1)) := by
    have h := hcycleA' 0
    have hnext : (⟨((0 : Fin (2 + kA * 3)).val + 1) % (2 + kA * 3),
        Nat.mod_lt _ (by omega)⟩ : Fin (2 + kA * 3)) = 1 := by
      ext
      simp
    rw [hnext] at h
    exact h
  exact R03SP01TwoCycleCyclicOrderAssemblySwap
    G kA kB eA' eB' hcycleA' hcycleB' hcross01' hcross12'

#print axioms R03SP01TwoCycleCyclicOrderAssemblyConnectedSwap

theorem R03SP01CycleOrderOfIsCyclesComponent
    {V : Type u} [Fintype V]
    (F : SimpleGraph V)
    (hcycles : F.IsCycles)
    (h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2)
    (c : F.ConnectedComponent) (n : Nat) [Fintype c.supp]
    (hn : 0 < n)
    (hcard : Fintype.card c.supp = n) :
    ∃ e : Fin n ≃ c.supp, ∀ i : Fin n,
      F.Adj (e i : V)
        (e ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : V) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨v, hv⟩ := c.nonempty_supp
  have hvne : (F.neighborSet v).Nonempty := by
    have hcardv : (F.neighborSet v).ncard = 2 := by
      change Nat.card {w : V // F.Adj v w} = 2
      exact h2 v
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨p, hp, hpverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hvne
  have hpne : ¬ p.Nil := hp.not_nil
  let q := p.tail
  have hqnodup : q.support.Nodup := by
    rw [show q.support = p.support.tail by
      dsimp [q]
      exact p.support_tail_of_not_nil hpne]
    exact hp.support_nodup
  have hqset : {x : V | x ∈ q.support} = c.supp := by
    ext x
    constructor
    · intro hx
      have hxps : x ∈ p.support := by
        rw [p.mem_support_iff]
        right
        have hxq : x ∈ p.tail.support := by
          change x ∈ q.support at hx
          exact hx
        rw [p.support_tail_of_not_nil hpne] at hxq
        exact hxq
      rw [← hpverts]
      exact (p.mem_verts_toSubgraph).2 hxps
    · intro hx
      have hxverts : x ∈ p.toSubgraph.verts := hpverts ▸ hx
      have hxps : x ∈ p.support := (p.mem_verts_toSubgraph).1 hxverts
      rw [p.mem_support_iff] at hxps
      rcases hxps with rfl | hxt
      · change x ∈ p.tail.support
        rw [p.support_tail_of_not_nil hpne]
        exact p.end_mem_tail_support hpne
      · change x ∈ p.tail.support
        rw [p.support_tail_of_not_nil hpne]
        exact hxt
  let eList : Fin q.support.length ≃ {x : V // x ∈ q.support} :=
    List.Nodup.getEquiv q.support hqnodup
  let eSet : {x : V // x ∈ q.support} ≃ c.supp := Equiv.setCongr hqset
  have hlen : q.support.length = n := by
    calc
      q.support.length = Fintype.card {x : V // x ∈ q.support} := by
        symm
        simpa using (Fintype.card_congr eList).symm
      _ = Fintype.card c.supp := Fintype.card_congr eSet
      _ = n := hcard
  let e : Fin n ≃ c.supp :=
    (finCongr hlen.symm).trans (eList.trans eSet)
  refine ⟨e, ?_⟩
  intro i
  have he (j : Fin n) : (e j : V) = q.getVert (j : Nat) := by
    dsimp [e, eSet, eList]
    change q.support.get (finCongr hlen.symm j) = _
    rw [← q.getVert_comp_val_eq_get_support]
    rfl
  rw [he i]
  by_cases hi : (i : Nat) < q.length
  · have hadj := q.adj_getVert_succ hi
    have hin : i.val + 1 < n := by
      have hi' : i.val < q.support.length := by rw [hlen]; exact i.isLt
      have hlenq : q.length + 1 = n := q.length_support.symm.trans hlen
      rw [q.length_support] at hi'
      omega
    have hnext : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) =
        ⟨i.val + 1, by omega⟩ := by
      ext
      exact Nat.mod_eq_of_lt hin
    rw [hnext, he]
    exact hadj
  · have hilast : (i : Nat) = q.length := by
      have hqplus : q.support.length = q.length + 1 := q.length_support
      have hilt : (i : Nat) < q.support.length := by rw [hlen]; exact i.isLt
      omega
    have hqend : q.getVert q.length = p.getVert p.length := by
      simp only [q, SimpleGraph.Walk.getVert_tail]
      rw [p.length_tail_add_one hpne]
    have hqstart : q.getVert 0 = p.snd := by
      simp [q]
    have hadj : F.Adj (q.getVert q.length) (q.getVert 0) := by
      rw [hqend, hqstart, p.getVert_length]
      exact p.adj_snd hpne
    have hnlen : n = q.length + 1 := by
      calc
        n = q.support.length := hlen.symm
        _ = q.length + 1 := q.length_support
    have hnext : (⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      rw [hilast]
      apply Nat.mod_eq_zero_of_dvd
      rw [hnlen]
    have hfirst : q.getVert (i : Nat) = q.getVert q.length := by
      rw [hilast]
    rw [hfirst, hnext, he]
    exact hadj


theorem R03SP01TwoFactorTwoCycleP3Factor
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (eV : cA.supp ⊕ cB.supp ≃ V)
    (heV_inl : ∀ x : cA.supp, eV (Sum.inl x) = x.1)
    (heV_inr : ∀ x : cB.supp, eV (Sum.inr x) = x.1)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = 1 + kA * 3)
    (hcardB : Fintype.card cB.supp = 2 + kB * 3)
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  classical
  have hcycles : F.IsCycles := by
    intro v hv
    change Nat.card {w : V // F.Adj v w} = 2
    exact hTF.2 v
  have h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2 := fun v => by
    exact hTF.2 v
  obtain ⟨eA, hcyA⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cA (1 + kA * 3) (by omega) hcardA
  obtain ⟨eB, hcyB⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cB (2 + kB * 3) (by omega) hcardB
  let Gsum : SimpleGraph (cA.supp ⊕ cB.supp) := G.comap eV
  have hsumconn : Gsum.Connected := by
    apply (SimpleGraph.Iso.comap eV G).connected_iff.mpr hconn
  have hcycleA : ∀ i : Fin (1 + kA * 3),
      Gsum.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    have hf := hcyA i
    have hg := hTF.1 hf
    simpa [Gsum, heV_inl] using hg
  have hcycleB : ∀ i : Fin (2 + kB * 3),
      Gsum.Adj (Sum.inr (eB i))
        (Sum.inr (eB ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    have hf := hcyB i
    have hg := hTF.1 hf
    simpa [Gsum, heV_inr] using hg
  obtain ⟨p⟩ := R03SP01TwoCycleCyclicOrderAssemblyConnected
    Gsum kA kB eA eB hcycleA hcycleB hsumconn
  refine ⟨{
    blockCount := p.blockCount
    place := p.place.trans eV
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    exact p.edge01 i
  · intro i
    exact p.edge12 i

#print axioms R03SP01CycleOrderOfIsCyclesComponent
#print axioms R03SP01TwoFactorTwoCycleP3Factor

/-- The support sum of two distinct connected components is equivalent to the
whole vertex type when the two supports cover it. -/
theorem R03SP01TwoComponentSupportEquiv
    {V : Type u} [Fintype V]
    (F : SimpleGraph V)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp) :
    ∃ (eV : cA.supp ⊕ cB.supp ≃ V),
      (∀ x : cA.supp, eV (Sum.inl x) = x.1) ∧
      (∀ x : cB.supp, eV (Sum.inr x) = x.1) := by
  classical
  have hdisj : Disjoint cA.supp cB.supp :=
    (SimpleGraph.pairwise_disjoint_supp_connectedComponent F) hneq
  let eVFun : cA.supp ⊕ cB.supp → V := fun z =>
    match z with
    | Sum.inl x => x.1
    | Sum.inr x => x.1
  have hinj : Function.Injective eVFun := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact hxy
      | inr y =>
        exfalso
        change x.1 = y.1 at hxy
        apply (Set.disjoint_left.mp hdisj) x.2
        simpa [hxy] using y.2
    | inr x =>
      cases y with
      | inl y =>
        exfalso
        change x.1 = y.1 at hxy
        apply (Set.disjoint_left.mp hdisj) y.2
        simpa [hxy] using x.2
      | inr y =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hxy
  have hsurj : Function.Surjective eVFun := by
    intro v
    rcases hcover v with hv | hv
    · exact ⟨Sum.inl ⟨v, hv⟩, rfl⟩
    · exact ⟨Sum.inr ⟨v, hv⟩, rfl⟩
  let eV : cA.supp ⊕ cB.supp ≃ V := Equiv.ofBijective eVFun ⟨hinj, hsurj⟩
  refine ⟨eV, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl


end CubicP3Partition

open CubicP3Partition
open SimpleGraph
universe u
theorem solution
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = 1 + kA * 3)
    (hcardB : Fintype.card cB.supp = 2 + kB * 3)
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨eV, heV_inl, heV_inr⟩ := R03SP01TwoComponentSupportEquiv
    F cA cB hneq hcover
  exact R03SP01TwoFactorTwoCycleP3Factor G F hTF cA cB eV
    heV_inl heV_inr kA kB hcardA hcardB hconn

