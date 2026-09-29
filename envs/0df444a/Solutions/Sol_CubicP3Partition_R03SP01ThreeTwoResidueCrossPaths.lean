-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeTwoResidueCrossPaths
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:12:52.725002+00:00
-- url     : https://prove2.me/submissions/ac831444-8300-40b6-811f-e911e22e9c42

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_e65c87aed6_r03_sp01_three_two_residue_cross_paths_candidate

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

/-- Two-cycle assembly from a supplied cross edge, without requiring ambient
connectedness. The cyclic origins are shifted to the edge endpoints. -/
theorem R03SP01TwoCycleCyclicOrderAssemblyAtCross
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
    (iA : Fin (1 + kA * 3)) (iB : Fin (2 + kB * 3))
    (cross : G.Adj (Sum.inl (eA iA)) (Sum.inr (eB iB))) :
    Nonempty (P3Factor G) := by
  letI : NeZero (1 + kA * 3) := ⟨by omega⟩
  letI : NeZero (2 + kB * 3) := ⟨by omega⟩
  let eA' : Fin (1 + kA * 3) ≃ A := (finCycle iA).trans eA
  let eB' : Fin (2 + kB * 3) ≃ B := (finCycle iB).trans eB
  have heA0 : eA' 0 = eA iA := by simp [eA']
  have heB0 : eB' 0 = eB iB := by simp [eB']
  have hcycleA' : ∀ i : Fin (1 + kA * 3),
      G.Adj (Sum.inl (eA' i))
        (Sum.inl (eA' ⟨(i.val + 1) % (1 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eA'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inl x) (Sum.inl y)) eA (by omega) cycleA iA
  have hcycleB' : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (eB' i))
        (Sum.inr (eB' ⟨(i.val + 1) % (2 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eB'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inr x) (Sum.inr y)) eB (by omega) cycleB iB
  have hcross01' : G.Adj (Sum.inl (eA' 0)) (Sum.inr (eB' 0)) := by
    rw [heA0, heB0]
    exact cross
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

/-- Symmetric supplied-cross-edge form with the order-2 residue on the first
summand. -/
theorem R03SP01TwoCycleCyclicOrderAssemblyAtCrossSwap
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
    (iA : Fin (2 + kA * 3)) (iB : Fin (1 + kB * 3))
    (cross : G.Adj (Sum.inl (eA iA)) (Sum.inr (eB iB))) :
    Nonempty (P3Factor G) := by
  letI : NeZero (2 + kA * 3) := ⟨by omega⟩
  letI : NeZero (1 + kB * 3) := ⟨by omega⟩
  let eA' : Fin (2 + kA * 3) ≃ A := (finCycle iA).trans eA
  let eB' : Fin (1 + kB * 3) ≃ B := (finCycle iB).trans eB
  have heA0 : eA' 0 = eA iA := by simp [eA']
  have heB0 : eB' 0 = eB iB := by simp [eB']
  have hcycleA' : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA' i))
        (Sum.inl (eA' ⟨(i.val + 1) % (2 + kA * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eA'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inl x) (Sum.inl y)) eA (by omega) cycleA iA
  have hcycleB' : ∀ i : Fin (1 + kB * 3),
      G.Adj (Sum.inr (eB' i))
        (Sum.inr (eB' ⟨(i.val + 1) % (1 + kB * 3),
          Nat.mod_lt _ (by omega)⟩)) := by
    simpa [eB'] using R03SP01ShiftCyclicOrder
      (fun x y => G.Adj (Sum.inr x) (Sum.inr y)) eB (by omega) cycleB iB
  have hcross01' : G.Adj (Sum.inl (eA' 0)) (Sum.inr (eB' 0)) := by
    rw [heA0, heB0]
    exact cross
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

#print axioms R03SP01TwoCycleCyclicOrderAssemblyAtCross
#print axioms R03SP01TwoCycleCyclicOrderAssemblyAtCrossSwap

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

/-- Two-cycle bridge with the component-cover hypothesis rather than an
externally supplied support equivalence. -/
theorem R03SP01TwoFactorTwoCycleP3FactorOfCover
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

#print axioms R03SP01TwoComponentSupportEquiv
#print axioms R03SP01TwoFactorTwoCycleP3FactorOfCover

/-- The same component-cover bridge with the two nonzero residues reversed. -/
theorem R03SP01TwoFactorTwoCycleP3FactorOfCoverSwap
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = 2 + kA * 3)
    (hcardB : Fintype.card cB.supp = 1 + kB * 3)
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨eV, heV_inl, heV_inr⟩ := R03SP01TwoComponentSupportEquiv
    F cB cA hneq.symm (fun v =>
      (hcover v).elim (fun hv => Or.inr hv) (fun hv => Or.inl hv))
  exact R03SP01TwoFactorTwoCycleP3Factor G F hTF cB cA eV
    heV_inl heV_inr kB kA hcardB hcardA hconn

#print axioms R03SP01TwoFactorTwoCycleP3FactorOfCoverSwap

/-- The nonzero-residue two-component case can use only total-order
 divisibility; the arithmetic branch excludes the already-covered zero-zero
 profile. -/
theorem R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    [Fintype cA.supp] [Fintype cB.supp]
    (horder : 3 ∣ Fintype.card V)
    (hnotzero : ¬(3 ∣ Fintype.card cA.supp ∧ 3 ∣ Fintype.card cB.supp))
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  obtain ⟨eV, _, _⟩ := R03SP01TwoComponentSupportEquiv
    F cA cB hneq hcover
  have hcardV : Fintype.card V = Fintype.card cA.supp + Fintype.card cB.supp := by
    calc
      Fintype.card V = Fintype.card (cA.supp ⊕ cB.supp) := by
        exact (Fintype.card_congr eV).symm
      _ = Fintype.card cA.supp + Fintype.card cB.supp := by simp
  have hsum : 3 ∣ Fintype.card cA.supp + Fintype.card cB.supp := by
    rw [← hcardV]
    exact horder
  have hclass :
      (∃ kA kB : Nat,
        Fintype.card cA.supp = kA * 3 ∧
        Fintype.card cB.supp = kB * 3) ∨
      (∃ kA kB : Nat,
        Fintype.card cA.supp = 1 + kA * 3 ∧
        Fintype.card cB.supp = 2 + kB * 3) ∨
      (∃ kA kB : Nat,
        Fintype.card cA.supp = 2 + kA * 3 ∧
        Fintype.card cB.supp = 1 + kB * 3) := by
    obtain ⟨q, hq⟩ := hsum
    have ha := Nat.mod_add_div (Fintype.card cA.supp) 3
    have hb := Nat.mod_add_div (Fintype.card cB.supp) 3
    have hla := Nat.mod_lt (Fintype.card cA.supp) (by omega : 0 < 3)
    have hlb := Nat.mod_lt (Fintype.card cB.supp) (by omega : 0 < 3)
    have hm : (Fintype.card cA.supp + Fintype.card cB.supp) % 3 = 0 := by
      rw [hq]
      simp
    have ham := Nat.add_mod (Fintype.card cA.supp) (Fintype.card cB.supp) 3
    by_cases ha0 : Fintype.card cA.supp % 3 = 0
    · by_cases hb0 : Fintype.card cB.supp % 3 = 0
      · left
        exact ⟨Fintype.card cA.supp / 3, Fintype.card cB.supp / 3,
          by omega, by omega⟩
      · by_cases hb1 : Fintype.card cB.supp % 3 = 1
        · exfalso
          omega
        · have hb2 : Fintype.card cB.supp % 3 = 2 := by omega
          exfalso
          omega
    · by_cases ha1 : Fintype.card cA.supp % 3 = 1
      · by_cases hb0 : Fintype.card cB.supp % 3 = 0
        · exfalso
          omega
        · by_cases hb1 : Fintype.card cB.supp % 3 = 1
          · exfalso
            omega
          · have hb2 : Fintype.card cB.supp % 3 = 2 := by omega
            right
            left
            exact ⟨Fintype.card cA.supp / 3, Fintype.card cB.supp / 3,
              by omega, by omega⟩
      · have ha2 : Fintype.card cA.supp % 3 = 2 := by omega
        by_cases hb0 : Fintype.card cB.supp % 3 = 0
        · exfalso
          omega
        · by_cases hb1 : Fintype.card cB.supp % 3 = 1
          · right
            right
            exact ⟨Fintype.card cA.supp / 3, Fintype.card cB.supp / 3,
              by omega, by omega⟩
          · have hb2 : Fintype.card cB.supp % 3 = 2 := by omega
            exfalso
            omega
  rcases hclass with hzero | hnonzero
  · obtain ⟨kA, kB, hcardA, hcardB⟩ := hzero
    apply False.elim
    apply hnotzero
    constructor
    · exact ⟨kA, by omega⟩
    · exact ⟨kB, by omega⟩
  · rcases hnonzero with hAB | hBA
    · obtain ⟨kA, kB, hcardA, hcardB⟩ := hAB
      exact R03SP01TwoFactorTwoCycleP3FactorOfCover G F hTF cA cB hneq
        hcover kA kB hcardA hcardB hconn
    · obtain ⟨kA, kB, hcardA, hcardB⟩ := hBA
      exact R03SP01TwoFactorTwoCycleP3FactorOfCoverSwap G F hTF cA cB hneq
        hcover kA kB hcardA hcardB hconn

#print axioms R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder

/-- Component-cover bridge using one explicitly supplied cross edge between the
 two selected 2-factor components. This removes the ambient connectedness
 assumption from the two-cycle residue construction. -/
theorem R03SP01TwoFactorTwoCycleP3FactorOfCoverAtCross
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    (xA xB : V)
    (hxA : xA ∈ cA.supp) (hxB : xB ∈ cB.supp)
    (hcross : G.Adj xA xB)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = 1 + kA * 3)
    (hcardB : Fintype.card cB.supp = 2 + kB * 3) :
    Nonempty (P3Factor G) := by
  classical
  obtain ⟨eV, heV_inl, heV_inr⟩ := R03SP01TwoComponentSupportEquiv
    F cA cB hneq hcover
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
  let iA : Fin (1 + kA * 3) := eA.symm ⟨xA, hxA⟩
  let iB : Fin (2 + kB * 3) := eB.symm ⟨xB, hxB⟩
  have hcross' : Gsum.Adj (Sum.inl (eA iA)) (Sum.inr (eB iB)) := by
    simpa [Gsum, iA, iB, heV_inl, heV_inr] using hcross
  obtain ⟨p⟩ := R03SP01TwoCycleCyclicOrderAssemblyAtCross
    Gsum kA kB eA eB hcycleA hcycleB iA iB hcross'
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

#print axioms R03SP01TwoFactorTwoCycleP3FactorOfCover

/-- Consecutive triples in an explicitly cyclically ordered multiple-of-three
set form a P3Factor. -/
theorem R03SP01CyclicDivisibleP3Factor
    {A : Type u} [Fintype A]
    (G : SimpleGraph A) (k : Nat) (hpos : 0 < k * 3)
    (e : Fin (k * 3) ≃ A)
    (cycle : ∀ i : Fin (k * 3),
      G.Adj (e i)
        (e ⟨(i.val + 1) % (k * 3), Nat.mod_lt _ hpos⟩)) :
    Nonempty (P3Factor G) := by
  refine ⟨{
    blockCount := k
    place := finProdFinEquiv.trans e
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    have h := cycle (finProdFinEquiv (i, (0 : Fin 3)))
    have hn : (k * 3) ≠ 0 := by omega
    have hidx : (⟨((finProdFinEquiv (i, (0 : Fin 3))).val + 1) % (k * 3),
        Nat.mod_lt _ hpos⟩ : Fin (k * 3)) = finProdFinEquiv (i, (1 : Fin 3)) := by
      apply Fin.ext
      dsimp [finProdFinEquiv]
      change (0 + 3 * i.val + 1) % (k * 3) = 1 + 3 * i.val
      simp only [zero_add]
      have hlt : 3 * i.val + 1 < k * 3 := by omega
      calc
        (3 * i.val + 1) % (k * 3) = 3 * i.val + 1 := Nat.mod_eq_of_lt hlt
        _ = 1 + 3 * i.val := by omega
    rw [hidx] at h
    exact h
  · intro i
    have h := cycle (finProdFinEquiv (i, (1 : Fin 3)))
    have hn : (k * 3) ≠ 0 := by omega
    have hidx : (⟨((finProdFinEquiv (i, (1 : Fin 3))).val + 1) % (k * 3),
        Nat.mod_lt _ hpos⟩ : Fin (k * 3)) = finProdFinEquiv (i, (2 : Fin 3)) := by
      apply Fin.ext
      dsimp [finProdFinEquiv]
      change (1 + 3 * i.val + 1) % (k * 3) = 2 + 3 * i.val
      have hlt : 1 + 3 * i.val + 1 < k * 3 := by omega
      calc
        (1 + 3 * i.val + 1) % (k * 3) = 1 + 3 * i.val + 1 := Nat.mod_eq_of_lt hlt
        _ = 2 + 3 * i.val := by omega
    rw [hidx] at h
    exact h

theorem R03SP01P3FactorSum
    {A B : Type u} [Fintype A] [Fintype B]
    (GA : SimpleGraph A) (GB : SimpleGraph B)
    (G : SimpleGraph (A ⊕ B))
    (pA : P3Factor GA) (pB : P3Factor GB)
    (hA : ∀ {x y : A}, GA.Adj x y → G.Adj (Sum.inl x) (Sum.inl y))
    (hB : ∀ {x y : B}, GB.Adj x y → G.Adj (Sum.inr x) (Sum.inr y)) :
    Nonempty (P3Factor G) := by
  let blockEquiv : Fin (pA.blockCount + pB.blockCount) ≃
      Fin pA.blockCount ⊕ Fin pB.blockCount := finSumFinEquiv.symm
  let sourceEquiv : (Fin (pA.blockCount + pB.blockCount) × Fin 3) ≃
      ((Fin pA.blockCount × Fin 3) ⊕ (Fin pB.blockCount × Fin 3)) :=
    (blockEquiv.prodCongr (Equiv.refl (Fin 3))).trans R03SP01SumProdDistrib
  let placeEquiv : ((Fin pA.blockCount × Fin 3) ⊕
      (Fin pB.blockCount × Fin 3)) ≃ (A ⊕ B) :=
    Equiv.sumCongr pA.place pB.place
  let place : (Fin (pA.blockCount + pB.blockCount) × Fin 3) ≃ (A ⊕ B) :=
    sourceEquiv.trans placeEquiv
  refine ⟨{
    blockCount := pA.blockCount + pB.blockCount
    place := place
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    generalize hb : blockEquiv i = z
    cases z with
    | inl z =>
      have h := pA.edge01 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hA h
    | inr z =>
      have h := pB.edge01 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hB h
  · intro i
    generalize hb : blockEquiv i = z
    cases z with
    | inl z =>
      have h := pA.edge12 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hA h
    | inr z =>
      have h := pB.edge12 z
      simpa [place, placeEquiv, sourceEquiv, R03SP01SumProdDistrib, hb] using hB h

#print axioms R03SP01CyclicDivisibleP3Factor
#print axioms R03SP01P3FactorSum

/-- The zero-zero residue profile of two cycle components is closed by
independent consecutive-triple tilings on each component and binary factor
sum gluing. -/
theorem R03SP01TwoFactorTwoCycleP3FactorZeroZero
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    (kA kB : Nat)
    [Fintype cA.supp] [Fintype cB.supp]
    (hcardA : Fintype.card cA.supp = kA * 3)
    (hcardB : Fintype.card cB.supp = kB * 3) :
    Nonempty (P3Factor G) := by
  classical
  obtain ⟨eV, heV_inl, heV_inr⟩ := R03SP01TwoComponentSupportEquiv
    F cA cB hneq hcover
  have hcycles : F.IsCycles := by
    intro v hv
    change Nat.card {w : V // F.Adj v w} = 2
    exact hTF.2 v
  have h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2 := fun v => by
    exact hTF.2 v
  have hposA : 0 < Fintype.card cA.supp := by
    obtain ⟨v, hv⟩ := cA.nonempty_supp
    letI : Nonempty cA.supp := ⟨⟨v, hv⟩⟩
    exact Fintype.card_pos
  have hposB : 0 < Fintype.card cB.supp := by
    obtain ⟨v, hv⟩ := cB.nonempty_supp
    letI : Nonempty cB.supp := ⟨⟨v, hv⟩⟩
    exact Fintype.card_pos
  obtain ⟨eA, hcyA⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cA (kA * 3) (by omega) hcardA
  obtain ⟨eB, hcyB⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cB (kB * 3) (by omega) hcardB
  let GA : SimpleGraph cA.supp := G.induce cA.supp
  let GB : SimpleGraph cB.supp := G.induce cB.supp
  let Gsum : SimpleGraph (cA.supp ⊕ cB.supp) := G.comap eV
  have hGAcycle : ∀ i : Fin (kA * 3),
      GA.Adj (eA i)
        (eA ⟨(i.val + 1) % (kA * 3), Nat.mod_lt _ (by omega)⟩) := by
    intro i
    have hf := hcyA i
    have hg := hTF.1 hf
    simpa [GA] using hg
  have hGBcycle : ∀ i : Fin (kB * 3),
      GB.Adj (eB i)
        (eB ⟨(i.val + 1) % (kB * 3), Nat.mod_lt _ (by omega)⟩) := by
    intro i
    have hf := hcyB i
    have hg := hTF.1 hf
    simpa [GB] using hg
  obtain ⟨pA⟩ := R03SP01CyclicDivisibleP3Factor GA kA (by omega)
    eA hGAcycle
  obtain ⟨pB⟩ := R03SP01CyclicDivisibleP3Factor GB kB (by omega)
    eB hGBcycle
  have hA : ∀ {x y : cA.supp}, GA.Adj x y →
      Gsum.Adj (Sum.inl x) (Sum.inl y) := by
    intro x y hxy
    have hg : G.Adj x.1 y.1 := hxy
    simpa [Gsum, heV_inl] using hg
  have hB : ∀ {x y : cB.supp}, GB.Adj x y →
      Gsum.Adj (Sum.inr x) (Sum.inr y) := by
    intro x y hxy
    have hg : G.Adj x.1 y.1 := hxy
    simpa [Gsum, heV_inr] using hg
  obtain ⟨p⟩ := R03SP01P3FactorSum GA GB Gsum pA pB hA hB
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

#print axioms R03SP01TwoFactorTwoCycleP3FactorZeroZero

/-- Exact-two-component closure: total-order divisibility selects either the
zero-zero tiling branch or the nonzero two-cycle cross-edge branch. -/
theorem R03SP01TwoFactorTwoCycleP3FactorOfDivisibleOrder
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    [Fintype cA.supp] [Fintype cB.supp]
    (horder : 3 ∣ Fintype.card V)
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by
  by_cases hA : 3 ∣ Fintype.card cA.supp
  · by_cases hB : 3 ∣ Fintype.card cB.supp
    · obtain ⟨kA, hkA⟩ := hA
      obtain ⟨kB, hkB⟩ := hB
      exact R03SP01TwoFactorTwoCycleP3FactorZeroZero G F hTF cA cB
        hneq hcover kA kB (by omega) (by omega)
    · have hnotzero : ¬(3 ∣ Fintype.card cA.supp ∧
        3 ∣ Fintype.card cB.supp) := by
        intro h
        exact hB h.2
      exact R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder
        G F hTF cA cB hneq hcover horder hnotzero hconn
  · have hnotzero : ¬(3 ∣ Fintype.card cA.supp ∧
      3 ∣ Fintype.card cB.supp) := by
      intro h
      exact hA h.1
    exact R03SP01TwoFactorTwoCycleNonzeroOfDivisibleOrder
      G F hTF cA cB hneq hcover horder hnotzero hconn

#print axioms R03SP01TwoFactorTwoCycleP3FactorOfDivisibleOrder

/-- Three equal 1-residue cycle components can be repaired by a two-edge
cross path through their exceptional vertices. The remaining vertices are
consecutive path triples. -/
theorem R03SP01ThreeOneResidueCrossPath
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB cC : F.ConnectedComponent)
    (eV : cA.supp ⊕ (cB.supp ⊕ cC.supp) ≃ V)
    (heA : ∀ x : cA.supp, eV (Sum.inl x) = x.1)
    (heB : ∀ x : cB.supp, eV (Sum.inr (Sum.inl x)) = x.1)
    (heC : ∀ x : cC.supp, eV (Sum.inr (Sum.inr x)) = x.1)
    (kA kB kC : Nat)
    [Fintype cA.supp] [Fintype cB.supp] [Fintype cC.supp]
    (hcardA : Fintype.card cA.supp = 1 + kA * 3)
    (hcardB : Fintype.card cB.supp = 1 + kB * 3)
    (hcardC : Fintype.card cC.supp = 1 + kC * 3)
    (xA xB xC : V)
    (hxA : xA ∈ cA.supp) (hxB : xB ∈ cB.supp) (hxC : xC ∈ cC.supp)
    (hAB : G.Adj xA xB) (hBC : G.Adj xB xC) :
    Nonempty (P3Factor G) := by
  classical
  have hcycles : F.IsCycles := by
    intro v hv
    change Nat.card {w : V // F.Adj v w} = 2
    exact hTF.2 v
  have h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2 := fun v => by
    exact hTF.2 v
  obtain ⟨eAraw, hcyAraw⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cA (1 + kA * 3) (by omega) hcardA
  obtain ⟨eBraw, hcyBraw⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cB (1 + kB * 3) (by omega) hcardB
  obtain ⟨eCraw, hcyCraw⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cC (1 + kC * 3) (by omega) hcardC
  letI : NeZero (1 + kA * 3) := ⟨by omega⟩
  letI : NeZero (1 + kB * 3) := ⟨by omega⟩
  letI : NeZero (1 + kC * 3) := ⟨by omega⟩
  let iA : Fin (1 + kA * 3) := eAraw.symm ⟨xA, hxA⟩
  let iB : Fin (1 + kB * 3) := eBraw.symm ⟨xB, hxB⟩
  let iC : Fin (1 + kC * 3) := eCraw.symm ⟨xC, hxC⟩
  let eA : Fin (1 + kA * 3) ≃ cA.supp := (finCycle iA).trans eAraw
  let eB : Fin (1 + kB * 3) ≃ cB.supp := (finCycle iB).trans eBraw
  let eC : Fin (1 + kC * 3) ≃ cC.supp := (finCycle iC).trans eCraw
  have hcyA : ∀ i : Fin (1 + kA * 3),
      F.Adj (eA i) (eA ⟨(i.val + 1) % (1 + kA * 3), Nat.mod_lt _ (by omega)⟩) := by
    simpa [eA] using R03SP01ShiftCyclicOrder (X := cA.supp) (n := 1 + kA * 3)
      (fun x y : cA.supp => F.Adj x y) eAraw (by omega) hcyAraw iA
  have hcyB : ∀ i : Fin (1 + kB * 3),
      F.Adj (eB i) (eB ⟨(i.val + 1) % (1 + kB * 3), Nat.mod_lt _ (by omega)⟩) := by
    simpa [eB] using R03SP01ShiftCyclicOrder (X := cB.supp) (n := 1 + kB * 3)
      (fun x y : cB.supp => F.Adj x y) eBraw (by omega) hcyBraw iB
  have hcyC : ∀ i : Fin (1 + kC * 3),
      F.Adj (eC i) (eC ⟨(i.val + 1) % (1 + kC * 3), Nat.mod_lt _ (by omega)⟩) := by
    simpa [eC] using R03SP01ShiftCyclicOrder (X := cC.supp) (n := 1 + kC * 3)
      (fun x y : cC.supp => F.Adj x y) eCraw (by omega) hcyCraw iC
  let Gsum : SimpleGraph (cA.supp ⊕ (cB.supp ⊕ cC.supp)) := G.comap eV
  let shiftA : (Fin (kA * 3) ⊕ Fin 1) ≃ Fin (1 + kA * 3) :=
    finSumFinEquiv.trans (finAddFlip (m := kA * 3) (n := 1))
  let blockA : (Fin (kA * 3) ⊕ Fin 1) ≃ cA.supp := shiftA.trans eA
  let shiftB : (Fin (kB * 3) ⊕ Fin 1) ≃ Fin (1 + kB * 3) :=
    finSumFinEquiv.trans (finAddFlip (m := kB * 3) (n := 1))
  let shiftC : (Fin (kC * 3) ⊕ Fin 1) ≃ Fin (1 + kC * 3) :=
    finSumFinEquiv.trans (finAddFlip (m := kC * 3) (n := 1))
  let r : Fin ((kB + kC) * 3) ≃ Fin (kB * 3) ⊕ Fin (kC * 3) :=
    (finCongr (by omega : (kB + kC) * 3 = kB * 3 + kC * 3)).trans
      finSumFinEquiv.symm
  let pairSource : (Fin ((kB + kC) * 3) ⊕ Fin 2) ≃
      ((Fin (kB * 3) ⊕ Fin 1) ⊕ (Fin (kC * 3) ⊕ Fin 1)) := {
    toFun := fun z => match z with
      | Sum.inl q => match r q with
        | Sum.inl b => Sum.inl (Sum.inl b)
        | Sum.inr c => Sum.inr (Sum.inl c)
      | Sum.inr j => if j = 0 then Sum.inl (Sum.inr 0) else Sum.inr (Sum.inr 0)
    invFun := fun z => match z with
      | Sum.inl q => match q with
        | Sum.inl b => Sum.inl (r.symm (Sum.inl b))
        | Sum.inr _ => Sum.inr 0
      | Sum.inr q => match q with
        | Sum.inl c => Sum.inl (r.symm (Sum.inr c))
        | Sum.inr _ => Sum.inr 1
    left_inv := by
      intro z
      rcases z with z | j
      · generalize hz : r z = q
        rcases q with b | c
        · have h : r.symm (Sum.inl b) = z := by
            rw [← hz]
            exact r.symm_apply_apply z
          simp [hz, h]
        · have h : r.symm (Sum.inr c) = z := by
            rw [← hz]
            exact r.symm_apply_apply z
          simp [hz, h]
      · fin_cases j <;> rfl
    right_inv := by
      intro z
      rcases z with z | z
      · rcases z with b | one
        · simp
        · have hone : one = 0 := Subsingleton.elim _ _
          subst one
          simp
      · rcases z with c | one
        · simp
        · have hone : one = 0 := Subsingleton.elim _ _
          subst one
          simp
  }
  let pairTarget : ((Fin (kB * 3) ⊕ Fin 1) ⊕
      (Fin (kC * 3) ⊕ Fin 1)) ≃ (cB.supp ⊕ cC.supp) :=
    (Equiv.sumCongr shiftB shiftC).trans (Equiv.sumCongr eB eC)
  let blockPair : (Fin ((kB + kC) * 3) ⊕ Fin 2) ≃
      (cB.supp ⊕ cC.supp) := pairSource.trans pairTarget
  have hrB (b : Fin kB) (j : Fin 3) :
      r (finProdFinEquiv (Fin.castAdd kC b, j)) =
        Sum.inl (finProdFinEquiv (b, j)) := by
    dsimp [r]
    have hcong :
        (finCongr (by omega : (kB + kC) * 3 = kB * 3 + kC * 3))
            (finProdFinEquiv (Fin.castAdd kC b, j)) =
          Fin.castAdd (kC * 3) (finProdFinEquiv (b, j)) := by
      ext
      simp [finProdFinEquiv]
    rw [hcong]
    exact finSumFinEquiv_symm_apply_castAdd _
  have hrC (b : Fin kC) (j : Fin 3) :
      r (finProdFinEquiv (Fin.natAdd kB b, j)) =
        Sum.inr (finProdFinEquiv (b, j)) := by
    dsimp [r]
    have hcong :
        (finCongr (by omega : (kB + kC) * 3 = kB * 3 + kC * 3))
            (finProdFinEquiv (Fin.natAdd kB b, j)) =
          Fin.natAdd (kB * 3) (finProdFinEquiv (b, j)) := by
      ext
      simp [finProdFinEquiv]
      omega
    rw [hcong]
    exact finSumFinEquiv_symm_apply_natAdd _
  have hpairB (b : Fin kB) (j : Fin 3) :
      blockPair (Sum.inl (finProdFinEquiv (Fin.castAdd kC b, j))) =
        Sum.inl (eB (Fin.natAdd 1 (finProdFinEquiv (b, j)))) := by
    dsimp [blockPair, pairSource, pairTarget]
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
    rw [hrB]
    simp [shiftB, finSumFinEquiv, finAddFlip]
  have hpairC (b : Fin kC) (j : Fin 3) :
      blockPair (Sum.inl (finProdFinEquiv (Fin.natAdd kB b, j))) =
        Sum.inr (eC (Fin.natAdd 1 (finProdFinEquiv (b, j)))) := by
    dsimp [blockPair, pairSource, pairTarget]
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
    rw [hrC]
    simp [shiftC, finSumFinEquiv, finAddFlip]
  have hblockA (b : Fin kA) (j : Fin 3) :
      blockA (Sum.inl (finProdFinEquiv (b, j))) =
        eA (Fin.natAdd 1 (finProdFinEquiv (b, j))) := by
    simp only [blockA, Equiv.trans_apply]
    simp [shiftA, finSumFinEquiv, finAddFlip]
  have hblockA0 : blockA (Sum.inr (0 : Fin 1)) = eA 0 := by
    simp [blockA, shiftA, finSumFinEquiv, finAddFlip]
    apply Fin.ext
    rfl
  have hpair0 : blockPair (Sum.inr (0 : Fin 2)) = Sum.inl (eB 0) := by
    dsimp [blockPair, pairSource, pairTarget]
    simp [shiftB, shiftC, finSumFinEquiv, finAddFlip]
    apply Fin.ext
    rfl
  have hpair1 : blockPair (Sum.inr (1 : Fin 2)) = Sum.inr (eC 0) := by
    dsimp [blockPair, pairSource, pairTarget]
    simp [shiftB, shiftC, finSumFinEquiv, finAddFlip]
    apply Fin.ext
    rfl
  have hAedges : ∀ b : Fin kA,
      Gsum.Adj (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      Gsum.Adj (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inl (blockA (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    have hb := b.is_lt
    have hnA : 0 < 1 + kA * 3 := by omega
    have hp0 : (finProdFinEquiv (b, (0 : Fin 3))).val + 1 < kA * 3 := by
      simp [finProdFinEquiv]
      omega
    have hp1 : (finProdFinEquiv (b, (1 : Fin 3))).val + 1 < kA * 3 := by
      simp [finProdFinEquiv]
      omega
    constructor
    · rw [hblockA b 0, hblockA b 1]
      have h0 := hcyA ⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩
      have hg := hTF.1 h0
      have hg' : Gsum.Adj
          (Sum.inl (eA ⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩))
          (Sum.inl (eA ⟨(1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
            (1 + kA * 3), Nat.mod_lt _ hnA⟩)) := by
        simpa [Gsum, heA] using hg
      have he0 : (⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩ : Fin (1 + kA * 3)) =
          Fin.natAdd 1 (finProdFinEquiv (b, (0 : Fin 3))) := by
        ext
        rfl
      have he1 : (⟨(1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
            (1 + kA * 3), Nat.mod_lt _ hnA⟩ : Fin (1 + kA * 3)) =
          Fin.natAdd 1 (finProdFinEquiv (b, (1 : Fin 3))) := by
        have hlt : 1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1 <
            1 + kA * 3 := by
          simp [finProdFinEquiv]
          omega
        apply Fin.ext
        change (1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
          (1 + kA * 3) = 1 + (finProdFinEquiv (b, (1 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      rw [he0, he1] at hg'
      exact hg'
    · rw [hblockA b 1, hblockA b 2]
      have h1 := hcyA ⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩
      have hg := hTF.1 h1
      have hg' : Gsum.Adj
          (Sum.inl (eA ⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩))
          (Sum.inl (eA ⟨(1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
            (1 + kA * 3), Nat.mod_lt _ hnA⟩)) := by
        simpa [Gsum, heA] using hg
      have he0 : (⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩ : Fin (1 + kA * 3)) =
          Fin.natAdd 1 (finProdFinEquiv (b, (1 : Fin 3))) := by
        ext
        rfl
      have he1 : (⟨(1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
            (1 + kA * 3), Nat.mod_lt _ hnA⟩ : Fin (1 + kA * 3)) =
          Fin.natAdd 1 (finProdFinEquiv (b, (2 : Fin 3))) := by
        have hlt : 1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1 <
            1 + kA * 3 := by
          simp [finProdFinEquiv]
          omega
        apply Fin.ext
        change (1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
          (1 + kA * 3) = 1 + (finProdFinEquiv (b, (2 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      rw [he0, he1] at hg'
      exact hg'
  have hBedges : ∀ b : Fin (kB + kC),
      Gsum.Adj (Sum.inr (blockPair (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inr (blockPair (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      Gsum.Adj (Sum.inr (blockPair (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inr (blockPair (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · have hb := b.is_lt
      have hnB : 0 < 1 + kB * 3 := by omega
      have hp0 : (finProdFinEquiv (b, (0 : Fin 3))).val + 1 < kB * 3 := by
        simp [finProdFinEquiv]
        omega
      have hp1 : (finProdFinEquiv (b, (1 : Fin 3))).val + 1 < kB * 3 := by
        simp [finProdFinEquiv]
        omega
      constructor
      · rw [hpairB b 0, hpairB b 1]
        have h := hcyB ⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩
        have hg := hTF.1 h
        have hg' : Gsum.Adj
            (Sum.inr (Sum.inl (eB ⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩)))
            (Sum.inr (Sum.inl (eB ⟨(1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
              (1 + kB * 3), Nat.mod_lt _ hnB⟩))) := by
          simpa [Gsum, heB] using hg
        have he0 : (⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩ : Fin (1 + kB * 3)) =
            Fin.natAdd 1 (finProdFinEquiv (b, (0 : Fin 3))) := by
          ext
          rfl
        have he1 : (⟨(1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
              (1 + kB * 3), Nat.mod_lt _ hnB⟩ : Fin (1 + kB * 3)) =
            Fin.natAdd 1 (finProdFinEquiv (b, (1 : Fin 3))) := by
          have hlt : 1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1 <
              1 + kB * 3 := by
            simp [finProdFinEquiv]
            omega
          apply Fin.ext
          change (1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
            (1 + kB * 3) = 1 + (finProdFinEquiv (b, (1 : Fin 3))).val
          rw [Nat.mod_eq_of_lt hlt]
          simp [finProdFinEquiv]
          omega
        rw [he0, he1] at hg'
        exact hg'
      · rw [hpairB b 1, hpairB b 2]
        have h := hcyB ⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩
        have hg := hTF.1 h
        have hg' : Gsum.Adj
            (Sum.inr (Sum.inl (eB ⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩)))
            (Sum.inr (Sum.inl (eB ⟨(1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
              (1 + kB * 3), Nat.mod_lt _ hnB⟩))) := by
          simpa [Gsum, heB] using hg
        have he0 : (⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩ : Fin (1 + kB * 3)) =
            Fin.natAdd 1 (finProdFinEquiv (b, (1 : Fin 3))) := by
          ext
          rfl
        have he1 : (⟨(1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
              (1 + kB * 3), Nat.mod_lt _ hnB⟩ : Fin (1 + kB * 3)) =
            Fin.natAdd 1 (finProdFinEquiv (b, (2 : Fin 3))) := by
          have hlt : 1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1 <
              1 + kB * 3 := by
            simp [finProdFinEquiv]
            omega
          apply Fin.ext
          change (1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
            (1 + kB * 3) = 1 + (finProdFinEquiv (b, (2 : Fin 3))).val
          rw [Nat.mod_eq_of_lt hlt]
          simp [finProdFinEquiv]
          omega
        rw [he0, he1] at hg'
        exact hg'
    · have hb := b.is_lt
      have hnC : 0 < 1 + kC * 3 := by omega
      have hp0 : (finProdFinEquiv (b, (0 : Fin 3))).val + 1 < kC * 3 := by
        simp [finProdFinEquiv]
        omega
      have hp1 : (finProdFinEquiv (b, (1 : Fin 3))).val + 1 < kC * 3 := by
        simp [finProdFinEquiv]
        omega
      constructor
      · rw [hpairC b 0, hpairC b 1]
        have h := hcyC ⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩
        have hg := hTF.1 h
        have hg' : Gsum.Adj
            (Sum.inr (Sum.inr (eC ⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩)))
            (Sum.inr (Sum.inr (eC ⟨(1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
              (1 + kC * 3), Nat.mod_lt _ hnC⟩))) := by
          simpa [Gsum, heC] using hg
        have he0 : (⟨1 + (finProdFinEquiv (b, (0 : Fin 3))).val, by omega⟩ : Fin (1 + kC * 3)) =
            Fin.natAdd 1 (finProdFinEquiv (b, (0 : Fin 3))) := by
          ext
          rfl
        have he1 : (⟨(1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
              (1 + kC * 3), Nat.mod_lt _ hnC⟩ : Fin (1 + kC * 3)) =
            Fin.natAdd 1 (finProdFinEquiv (b, (1 : Fin 3))) := by
          have hlt : 1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1 <
              1 + kC * 3 := by
            simp [finProdFinEquiv]
            omega
          apply Fin.ext
          change (1 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
            (1 + kC * 3) = 1 + (finProdFinEquiv (b, (1 : Fin 3))).val
          rw [Nat.mod_eq_of_lt hlt]
          simp [finProdFinEquiv]
          omega
        rw [he0, he1] at hg'
        exact hg'
      · rw [hpairC b 1, hpairC b 2]
        have h := hcyC ⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩
        have hg := hTF.1 h
        have hg' : Gsum.Adj
            (Sum.inr (Sum.inr (eC ⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩)))
            (Sum.inr (Sum.inr (eC ⟨(1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
              (1 + kC * 3), Nat.mod_lt _ hnC⟩))) := by
          simpa [Gsum, heC] using hg
        have he0 : (⟨1 + (finProdFinEquiv (b, (1 : Fin 3))).val, by omega⟩ : Fin (1 + kC * 3)) =
            Fin.natAdd 1 (finProdFinEquiv (b, (1 : Fin 3))) := by
          ext
          rfl
        have he1 : (⟨(1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
              (1 + kC * 3), Nat.mod_lt _ hnC⟩ : Fin (1 + kC * 3)) =
            Fin.natAdd 1 (finProdFinEquiv (b, (2 : Fin 3))) := by
          have hlt : 1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1 <
              1 + kC * 3 := by
            simp [finProdFinEquiv]
            omega
          apply Fin.ext
          change (1 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
            (1 + kC * 3) = 1 + (finProdFinEquiv (b, (2 : Fin 3))).val
          rw [Nat.mod_eq_of_lt hlt]
          simp [finProdFinEquiv]
          omega
        rw [he0, he1] at hg'
        exact hg'
  have hcross01 : Gsum.Adj
      (Sum.inl (blockA (Sum.inr (0 : Fin 1))))
      (Sum.inr (blockPair (Sum.inr (0 : Fin 2)))) := by
    rw [hblockA0, hpair0]
    have heA0 : eA 0 = (⟨xA, hxA⟩ : cA.supp) := by
      simp [eA, iA]
    have heB0 : eB 0 = (⟨xB, hxB⟩ : cB.supp) := by
      simp [eB, iB]
    have hg : Gsum.Adj (Sum.inl (⟨xA, hxA⟩ : cA.supp))
        (Sum.inr (Sum.inl (⟨xB, hxB⟩ : cB.supp))) := by
      change G.Adj (eV (Sum.inl (⟨xA, hxA⟩ : cA.supp)))
        (eV (Sum.inr (Sum.inl (⟨xB, hxB⟩ : cB.supp))))
      rw [heA, heB]
      exact hAB
    rw [← heA0, ← heB0] at hg
    exact hg
  have hcross12 : Gsum.Adj
      (Sum.inr (blockPair (Sum.inr (0 : Fin 2))))
      (Sum.inr (blockPair (Sum.inr (1 : Fin 2)))) := by
    rw [hpair0, hpair1]
    have heB0 : eB 0 = (⟨xB, hxB⟩ : cB.supp) := by
      simp [eB, iB]
    have heC0 : eC 0 = (⟨xC, hxC⟩ : cC.supp) := by
      simp [eC, iC]
    have hg : Gsum.Adj
        (Sum.inr (Sum.inl (⟨xB, hxB⟩ : cB.supp)))
        (Sum.inr (Sum.inr (⟨xC, hxC⟩ : cC.supp))) := by
      change G.Adj (eV (Sum.inr (Sum.inl (⟨xB, hxB⟩ : cB.supp))))
        (eV (Sum.inr (Sum.inr (⟨xC, hxC⟩ : cC.supp))))
      rw [heB, heC]
      exact hBC
    rw [← heB0, ← heC0] at hg
    exact hg
  obtain ⟨p⟩ := R03SP01ThreePieceCrossAssembly
    Gsum kA (kB + kC) blockA blockPair hAedges hBedges hcross01 hcross12
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

#print axioms R03SP01ThreeOneResidueCrossPath

/-- Three divisible cycle components are compositional: each component is
consecutively tiled and the three local factors are glued. -/
theorem R03SP01ThreeDivisibleComponents
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB cC : F.ConnectedComponent)
    (eV : cA.supp ⊕ (cB.supp ⊕ cC.supp) ≃ V)
    (heA : ∀ x : cA.supp, eV (Sum.inl x) = x.1)
    (heB : ∀ x : cB.supp, eV (Sum.inr (Sum.inl x)) = x.1)
    (heC : ∀ x : cC.supp, eV (Sum.inr (Sum.inr x)) = x.1)
    (kA kB kC : Nat)
    [Fintype cA.supp] [Fintype cB.supp] [Fintype cC.supp]
    (hcardA : Fintype.card cA.supp = kA * 3)
    (hcardB : Fintype.card cB.supp = kB * 3)
    (hcardC : Fintype.card cC.supp = kC * 3) :
    Nonempty (P3Factor G) := by
  classical
  have hcycles : F.IsCycles := by
    intro v hv
    change Nat.card {w : V // F.Adj v w} = 2
    exact hTF.2 v
  have h2 : ∀ v : V, Nat.card {w : V // F.Adj v w} = 2 := fun v => by
    exact hTF.2 v
  have hposA : 0 < Fintype.card cA.supp := by
    obtain ⟨v, hv⟩ := cA.nonempty_supp
    letI : Nonempty cA.supp := ⟨⟨v, hv⟩⟩
    exact Fintype.card_pos
  have hposB : 0 < Fintype.card cB.supp := by
    obtain ⟨v, hv⟩ := cB.nonempty_supp
    letI : Nonempty cB.supp := ⟨⟨v, hv⟩⟩
    exact Fintype.card_pos
  have hposC : 0 < Fintype.card cC.supp := by
    obtain ⟨v, hv⟩ := cC.nonempty_supp
    letI : Nonempty cC.supp := ⟨⟨v, hv⟩⟩
    exact Fintype.card_pos
  obtain ⟨eA, hcyA⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cA (kA * 3) (by omega) hcardA
  obtain ⟨eB, hcyB⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cB (kB * 3) (by omega) hcardB
  obtain ⟨eC, hcyC⟩ := R03SP01CycleOrderOfIsCyclesComponent
    F hcycles h2 cC (kC * 3) (by omega) hcardC
  let Gsum : SimpleGraph (cA.supp ⊕ (cB.supp ⊕ cC.supp)) := G.comap eV
  let GA : SimpleGraph cA.supp := G.induce cA.supp
  let GB : SimpleGraph cB.supp := G.induce cB.supp
  let GC : SimpleGraph cC.supp := G.induce cC.supp
  have hGAcycle : ∀ i : Fin (kA * 3),
      GA.Adj (eA i)
        (eA ⟨(i.val + 1) % (kA * 3), Nat.mod_lt _ (by omega)⟩) := by
    intro i
    simpa [GA] using hTF.1 (hcyA i)
  have hGBcycle : ∀ i : Fin (kB * 3),
      GB.Adj (eB i)
        (eB ⟨(i.val + 1) % (kB * 3), Nat.mod_lt _ (by omega)⟩) := by
    intro i
    simpa [GB] using hTF.1 (hcyB i)
  have hGCcycle : ∀ i : Fin (kC * 3),
      GC.Adj (eC i)
        (eC ⟨(i.val + 1) % (kC * 3), Nat.mod_lt _ (by omega)⟩) := by
    intro i
    simpa [GC] using hTF.1 (hcyC i)
  obtain ⟨pA⟩ := R03SP01CyclicDivisibleP3Factor GA kA (by omega) eA hGAcycle
  obtain ⟨pB⟩ := R03SP01CyclicDivisibleP3Factor GB kB (by omega) eB hGBcycle
  obtain ⟨pC⟩ := R03SP01CyclicDivisibleP3Factor GC kC (by omega) eC hGCcycle
  let assoc : (cA.supp ⊕ cB.supp) ⊕ cC.supp ≃
      cA.supp ⊕ (cB.supp ⊕ cC.supp) :=
    Equiv.sumAssoc cA.supp cB.supp cC.supp
  let Gleft : SimpleGraph ((cA.supp ⊕ cB.supp) ⊕ cC.supp) :=
    Gsum.comap assoc
  let GAB : SimpleGraph (cA.supp ⊕ cB.supp) := {
    Adj := fun x y => Gleft.Adj (Sum.inl x) (Sum.inl y)
    symm := ⟨by
      intro x y h
      exact Gleft.adj_symm h⟩
    loopless := ⟨by
      intro x h
      exact Gleft.loopless.irrefl (Sum.inl x) h⟩
  }
  have hA : ∀ {x y : cA.supp}, GA.Adj x y →
      GAB.Adj (Sum.inl x) (Sum.inl y) := by
    intro x y hxy
    have hg : G.Adj x.1 y.1 := hxy
    simpa [GAB, Gleft, Gsum, assoc, heA] using hg
  have hB : ∀ {x y : cB.supp}, GB.Adj x y →
      GAB.Adj (Sum.inr x) (Sum.inr y) := by
    intro x y hxy
    have hg : G.Adj x.1 y.1 := hxy
    simpa [GAB, Gleft, Gsum, assoc, heB] using hg
  obtain ⟨pAB⟩ := R03SP01P3FactorSum GA GB GAB pA pB hA hB
  have hAB : ∀ {x y : cA.supp ⊕ cB.supp}, GAB.Adj x y →
      Gleft.Adj (Sum.inl x) (Sum.inl y) := by
    intro x y hxy
    exact hxy
  have hC : ∀ {x y : cC.supp}, GC.Adj x y →
      Gleft.Adj (Sum.inr x) (Sum.inr y) := by
    intro x y hxy
    have hg : G.Adj x.1 y.1 := hxy
    simpa [Gleft, Gsum, assoc, heC] using hg
  obtain ⟨p⟩ := R03SP01P3FactorSum GAB GC Gleft pAB pC hAB hC
  refine ⟨{
    blockCount := p.blockCount
    place := p.place.trans (assoc.trans eV)
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    exact p.edge01 i
  · intro i
    exact p.edge12 i

#print axioms R03SP01ThreeDivisibleComponents


end CubicP3Partition

open CubicP3Partition
open SimpleGraph
universe u
theorem solution
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (G : SimpleGraph (A ⊕ (B ⊕ C)))
    (kA kB kC : Nat)
    (eA : Fin (2 + kA * 3) ≃ A)
    (eB : Fin (2 + kB * 3) ≃ B)
    (eC : Fin (2 + kC * 3) ≃ C)
    (cycleA : ∀ i : Fin (2 + kA * 3),
      G.Adj (Sum.inl (eA i))
        (Sum.inl (eA ⟨(i.val + 1) % (2 + kA * 3), Nat.mod_lt _ (by omega)⟩)))
    (cycleB : ∀ i : Fin (2 + kB * 3),
      G.Adj (Sum.inr (Sum.inl (eB i)))
        (Sum.inr (Sum.inl (eB ⟨(i.val + 1) % (2 + kB * 3), Nat.mod_lt _ (by omega)⟩))))
    (cycleC : ∀ i : Fin (2 + kC * 3),
      G.Adj (Sum.inr (Sum.inr (eC i)))
        (Sum.inr (Sum.inr (eC ⟨(i.val + 1) % (2 + kC * 3), Nat.mod_lt _ (by omega)⟩))))
    (crossAB : G.Adj (Sum.inl (eA 0))
      (Sum.inr (Sum.inl (eB 0))))
    (crossAC : G.Adj (Sum.inl (eA 1))
      (Sum.inr (Sum.inr (eC 0)))) :
    Nonempty (P3Factor G) := by
  classical
  let M : Type := Fin (kA * 3)
  let AL : Type := M ⊕ Fin 1
  let AR : Type := Fin (0 * 3) ⊕ Fin 1
  let MB : Type := Fin (kB * 3)
  let BT : Type := MB ⊕ Fin 2
  let MC : Type := Fin (kC * 3)
  let CT : Type := MC ⊕ Fin 2
  let aReorder : AL ⊕ AR ≃ (Fin 1 ⊕ Fin 1) ⊕ M := {
    toFun := fun z => match z with
      | Sum.inl (Sum.inl r) => Sum.inr r
      | Sum.inl (Sum.inr s) => Sum.inl (Sum.inl s)
      | Sum.inr (Sum.inl r) => Fin.elim0 r
      | Sum.inr (Sum.inr s) => Sum.inl (Sum.inr s)
    invFun := fun z => match z with
      | Sum.inl (Sum.inl s) => Sum.inl (Sum.inr s)
      | Sum.inl (Sum.inr s) => Sum.inr (Sum.inr s)
      | Sum.inr r => Sum.inl (Sum.inl r)
    left_inv := by
      intro z
      rcases z with z | z
      · rcases z with r | s <;> rfl
      · rcases z with r | s
        · exact Fin.elim0 r
        · rfl
    right_inv := by
      intro z
      rcases z with z | r
      · rcases z with s | s <;> rfl
      · rfl
  }
  let aFin01 : (Fin 1 ⊕ Fin 1) ≃ Fin 2 :=
    finSumFinEquiv
  let aFin0 : ((Fin 1 ⊕ Fin 1) ⊕ M) ≃ Fin ((1 + 1) + (kA * 3)) :=
    (Equiv.sumCongr aFin01 (Equiv.refl M)).trans
      (finSumFinEquiv (m := 2) (n := kA * 3))
  let aFin1 : Fin ((1 + 1) + (kA * 3)) ≃ Fin (2 + kA * 3) :=
    finCongr (by omega)
  let aJoin : AL ⊕ AR ≃ A :=
    ((aReorder.trans aFin0).trans aFin1).trans eA
  let bJoinIndex : BT ≃ Fin (2 + kB * 3) :=
    (Equiv.sumComm (Fin (kB * 3)) (Fin 2)).trans finSumFinEquiv
  let cJoinIndex : CT ≃ Fin (2 + kC * 3) :=
    (Equiv.sumComm (Fin (kC * 3)) (Fin 2)).trans finSumFinEquiv
  let bJoin : BT ≃ B := bJoinIndex.trans eB
  let cJoin : CT ≃ C := cJoinIndex.trans eC
  let reorderInner : BT ⊕ (AR ⊕ CT) ≃ AR ⊕ (BT ⊕ CT) :=
    (Equiv.sumAssoc BT AR CT).symm.trans
      ((Equiv.sumCongr (Equiv.sumComm BT AR) (Equiv.refl CT)).trans
        (Equiv.sumAssoc AR BT CT))
  let reorder : (AL ⊕ BT) ⊕ (AR ⊕ CT) ≃
      (AL ⊕ AR) ⊕ (BT ⊕ CT) :=
    (Equiv.sumAssoc AL BT (AR ⊕ CT)).trans
      ((Equiv.sumCongr (Equiv.refl AL) reorderInner).trans
        (Equiv.sumAssoc AL AR (BT ⊕ CT)).symm)
  let combined : (AL ⊕ BT) ⊕ (AR ⊕ CT) ≃ A ⊕ (B ⊕ C) :=
    reorder.trans (Equiv.sumCongr aJoin (Equiv.sumCongr bJoin cJoin))
  let blockAL : AL → A := fun z => match z with
    | Sum.inl r => eA ⟨2 + r.val, by omega⟩
    | Sum.inr _ => eA 0
  let blockAR : AR → A := fun z => match z with
    | Sum.inl r => Fin.elim0 r
    | Sum.inr _ => eA 1
  have hAL : ∀ z : AL, aJoin (Sum.inl z) = blockAL z := by
    intro z
    rcases z with r | r
    · simp [aJoin, aReorder, aFin01, aFin0, aFin1, blockAL, finSumFinEquiv]
      apply Fin.ext
      simp [finSumFinEquiv]
    · fin_cases r
      simp [aJoin, aReorder, aFin01, aFin0, aFin1, blockAL, finSumFinEquiv]
      apply Fin.ext
      norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + kA * 3)]
  have hAR : ∀ z : AR, aJoin (Sum.inr z) = blockAR z := by
    intro z
    rcases z with r | r
    · exact Fin.elim0 r
    · fin_cases r
      simp [aJoin, aReorder, aFin01, aFin0, aFin1, blockAR, finSumFinEquiv]
      apply Fin.ext
      norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + kA * 3)]
  have hcombAL (z : AL) :
      combined (Sum.inl (Sum.inl z)) = Sum.inl (blockAL z) := by
    simp [combined, reorder, reorderInner, hAL]
  have hcombBT (z : BT) :
      combined (Sum.inl (Sum.inr z)) = Sum.inr (Sum.inl (bJoin z)) := by
    simp [combined, reorder, reorderInner, hAL, hAR]
  have hcombAR (z : AR) :
      combined (Sum.inr (Sum.inl z)) = Sum.inl (blockAR z) := by
    simp [combined, reorder, reorderInner, hAL, hAR]
  have hcombCT (z : CT) :
      combined (Sum.inr (Sum.inr z)) = Sum.inr (Sum.inr (cJoin z)) := by
    simp [combined, reorder, reorderInner, hAL, hAR]
  have hbjoinRes (r : Fin (kB * 3)) :
      bJoin (Sum.inl r) = eB ⟨2 + r.val, by omega⟩ := by
    change eB ((Equiv.sumComm (Fin (kB * 3)) (Fin 2)).trans
      finSumFinEquiv (Sum.inl r)) = eB ⟨2 + r.val, by omega⟩
    apply congrArg eB
    apply Fin.ext
    simp [Equiv.sumComm_apply, finSumFinEquiv]
  have hbjoin0 : bJoin (Sum.inr (0 : Fin 2)) = eB 0 := by
    change eB ((Equiv.sumComm (Fin (kB * 3)) (Fin 2)).trans
      finSumFinEquiv (Sum.inr (0 : Fin 2))) = eB 0
    apply congrArg eB
    apply Fin.ext
    simp [Equiv.sumComm_apply, finSumFinEquiv]
  have hbjoin1 : bJoin (Sum.inr (1 : Fin 2)) = eB 1 := by
    change eB ((Equiv.sumComm (Fin (kB * 3)) (Fin 2)).trans
      finSumFinEquiv (Sum.inr (1 : Fin 2))) = eB 1
    apply congrArg eB
    apply Fin.ext
    simp [Equiv.sumComm_apply, finSumFinEquiv]
    norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + kB * 3)]
  have hcjoinRes (r : Fin (kC * 3)) :
      cJoin (Sum.inl r) = eC ⟨2 + r.val, by omega⟩ := by
    change eC ((Equiv.sumComm (Fin (kC * 3)) (Fin 2)).trans
      finSumFinEquiv (Sum.inl r)) = eC ⟨2 + r.val, by omega⟩
    apply congrArg eC
    apply Fin.ext
    simp [Equiv.sumComm_apply, finSumFinEquiv]
  have hcjoin0 : cJoin (Sum.inr (0 : Fin 2)) = eC 0 := by
    change eC ((Equiv.sumComm (Fin (kC * 3)) (Fin 2)).trans
      finSumFinEquiv (Sum.inr (0 : Fin 2))) = eC 0
    apply congrArg eC
    apply Fin.ext
    simp [Equiv.sumComm_apply, finSumFinEquiv]
  have hcjoin1 : cJoin (Sum.inr (1 : Fin 2)) = eC 1 := by
    change eC ((Equiv.sumComm (Fin (kC * 3)) (Fin 2)).trans
      finSumFinEquiv (Sum.inr (1 : Fin 2))) = eC 1
    apply congrArg eC
    apply Fin.ext
    simp [Equiv.sumComm_apply, finSumFinEquiv]
    norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + kC * 3)]
  let H : SimpleGraph ((AL ⊕ BT) ⊕ (AR ⊕ CT)) := G.comap combined
  let H1 : SimpleGraph (AL ⊕ BT) := {
    Adj := fun x y => H.Adj (Sum.inl x) (Sum.inl y)
    symm := ⟨by intro x y h; exact H.adj_symm h⟩
    loopless := ⟨by intro x h; exact H.loopless.irrefl (Sum.inl x) h⟩
  }
  let H2 : SimpleGraph (AR ⊕ CT) := {
    Adj := fun x y => H.Adj (Sum.inr x) (Sum.inr y)
    symm := ⟨by intro x y h; exact H.adj_symm h⟩
    loopless := ⟨by intro x h; exact H.loopless.irrefl (Sum.inr x) h⟩
  }
  let idAL : (Fin (kA * 3) ⊕ Fin 1) ≃ AL := Equiv.refl AL
  let idBT : (Fin (kB * 3) ⊕ Fin 2) ≃ BT := Equiv.refl BT
  have edgeAL : ∀ b : Fin kA,
      H1.Adj (Sum.inl (idAL (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inl (idAL (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      H1.Adj (Sum.inl (idAL (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inl (idAL (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    dsimp [idAL]
    constructor
    · change G.Adj (combined (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (b, (0 : Fin 3)))))))
        (combined (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))))
      rw [hcombAL, hcombAL]
      dsimp [blockAL]
      have h := cycleA ⟨2 + (finProdFinEquiv (b, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext : (⟨(2 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
          (2 + kA * 3), Nat.mod_lt _ (by omega)⟩ : Fin (2 + kA * 3)) =
          ⟨2 + (finProdFinEquiv (b, (1 : Fin 3))).val, by
            simp [finProdFinEquiv]
            omega⟩ := by
        have hlt : 2 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1 <
            2 + kA * 3 := by
          simp [finProdFinEquiv]
          omega
        apply Fin.ext
        change (2 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
          (2 + kA * 3) = 2 + (finProdFinEquiv (b, (1 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      rw [hnext] at h
      exact h
    · change G.Adj (combined (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))))
        (combined (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))))
      rw [hcombAL, hcombAL]
      dsimp [blockAL]
      have h := cycleA ⟨2 + (finProdFinEquiv (b, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext : (⟨(2 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
          (2 + kA * 3), Nat.mod_lt _ (by omega)⟩ : Fin (2 + kA * 3)) =
          ⟨2 + (finProdFinEquiv (b, (2 : Fin 3))).val, by
            simp [finProdFinEquiv]
            omega⟩ := by
        have hlt : 2 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1 <
            2 + kA * 3 := by
          simp [finProdFinEquiv]
          omega
        apply Fin.ext
        change (2 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
          (2 + kA * 3) = 2 + (finProdFinEquiv (b, (2 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      rw [hnext] at h
      exact h
  have edgeBT : ∀ b : Fin kB,
      H1.Adj (Sum.inr (idBT (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inr (idBT (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      H1.Adj (Sum.inr (idBT (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inr (idBT (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    dsimp [idBT]
    constructor
    · change G.Adj (combined (Sum.inl (Sum.inr (Sum.inl (finProdFinEquiv (b, (0 : Fin 3)))))))
        (combined (Sum.inl (Sum.inr (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))))
      rw [hcombBT, hcombBT, hbjoinRes, hbjoinRes]
      have h := cycleB ⟨2 + (finProdFinEquiv (b, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext : (⟨(2 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
          (2 + kB * 3), Nat.mod_lt _ (by omega)⟩ : Fin (2 + kB * 3)) =
          ⟨2 + (finProdFinEquiv (b, (1 : Fin 3))).val, by
            simp [finProdFinEquiv]
            omega⟩ := by
        have hlt : 2 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1 <
            2 + kB * 3 := by
          simp [finProdFinEquiv]
          omega
        apply Fin.ext
        change (2 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
          (2 + kB * 3) = 2 + (finProdFinEquiv (b, (1 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      rw [hnext] at h
      exact h
    · change G.Adj (combined (Sum.inl (Sum.inr (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))))
        (combined (Sum.inl (Sum.inr (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))))
      rw [hcombBT, hcombBT, hbjoinRes, hbjoinRes]
      have h := cycleB ⟨2 + (finProdFinEquiv (b, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext : (⟨(2 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
          (2 + kB * 3), Nat.mod_lt _ (by omega)⟩ : Fin (2 + kB * 3)) =
          ⟨2 + (finProdFinEquiv (b, (2 : Fin 3))).val, by
            simp [finProdFinEquiv]
            omega⟩ := by
        have hlt : 2 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1 <
            2 + kB * 3 := by
          simp [finProdFinEquiv]
          omega
        apply Fin.ext
        change (2 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
          (2 + kB * 3) = 2 + (finProdFinEquiv (b, (2 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      rw [hnext] at h
      exact h
  have cross1 : H1.Adj (Sum.inl (idAL (Sum.inr (0 : Fin 1))))
      (Sum.inr (idBT (Sum.inr (0 : Fin 2)))) := by
    dsimp [idAL, idBT]
    change G.Adj (combined (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))))
      (combined (Sum.inl (Sum.inr (Sum.inr (0 : Fin 2)))))
    rw [hcombAL, hcombBT, hbjoin0]
    dsimp [blockAL]
    exact crossAB
  have cross1b : H1.Adj (Sum.inr (idBT (Sum.inr (0 : Fin 2))))
      (Sum.inr (idBT (Sum.inr (1 : Fin 2)))) := by
    dsimp [idBT]
    change G.Adj (combined (Sum.inl (Sum.inr (Sum.inr (0 : Fin 2)))))
      (combined (Sum.inl (Sum.inr (Sum.inr (1 : Fin 2)))))
    rw [hcombBT, hcombBT, hbjoin0, hbjoin1]
    have hnext : (⟨((0 : Fin (2 + kB * 3)).val + 1) % (2 + kB * 3),
        Nat.mod_lt _ (by omega)⟩ : Fin (2 + kB * 3)) = 1 := by
      apply Fin.ext
      norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + kB * 3)]
    have h := cycleB 0
    rw [hnext] at h
    exact h
  obtain ⟨p1⟩ := R03SP01ThreePieceCrossAssembly
    H1 kA kB idAL idBT edgeAL edgeBT cross1 cross1b
  let idAR : (Fin (0 * 3) ⊕ Fin 1) ≃ AR := Equiv.refl AR
  let idCT : (Fin (kC * 3) ⊕ Fin 2) ≃ CT := Equiv.refl CT
  have edgeAR : ∀ b : Fin 0,
      H2.Adj (Sum.inl (idAR (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inl (idAR (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      H2.Adj (Sum.inl (idAR (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inl (idAR (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    dsimp [idAR]
    exact Fin.elim0 b
  have edgeCT : ∀ b : Fin kC,
      H2.Adj (Sum.inr (idCT (Sum.inl (finProdFinEquiv (b, (0 : Fin 3))))))
        (Sum.inr (idCT (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))) ∧
      H2.Adj (Sum.inr (idCT (Sum.inl (finProdFinEquiv (b, (1 : Fin 3))))))
        (Sum.inr (idCT (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))) := by
    intro b
    dsimp [idCT]
    constructor
    · change G.Adj (combined (Sum.inr (Sum.inr (Sum.inl (finProdFinEquiv (b, (0 : Fin 3)))))))
        (combined (Sum.inr (Sum.inr (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))))
      rw [hcombCT, hcombCT, hcjoinRes, hcjoinRes]
      have h := cycleC ⟨2 + (finProdFinEquiv (b, (0 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext : (⟨(2 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
          (2 + kC * 3), Nat.mod_lt _ (by omega)⟩ : Fin (2 + kC * 3)) =
          ⟨2 + (finProdFinEquiv (b, (1 : Fin 3))).val, by
            simp [finProdFinEquiv]
            omega⟩ := by
        have hlt : 2 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1 <
            2 + kC * 3 := by
          simp [finProdFinEquiv]
          omega
        apply Fin.ext
        change (2 + (finProdFinEquiv (b, (0 : Fin 3))).val + 1) %
          (2 + kC * 3) = 2 + (finProdFinEquiv (b, (1 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      rw [hnext] at h
      exact h
    · change G.Adj (combined (Sum.inr (Sum.inr (Sum.inl (finProdFinEquiv (b, (1 : Fin 3)))))))
        (combined (Sum.inr (Sum.inr (Sum.inl (finProdFinEquiv (b, (2 : Fin 3)))))))
      rw [hcombCT, hcombCT, hcjoinRes, hcjoinRes]
      have h := cycleC ⟨2 + (finProdFinEquiv (b, (1 : Fin 3))).val, by
        simp [finProdFinEquiv]
        omega⟩
      have hnext : (⟨(2 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
          (2 + kC * 3), Nat.mod_lt _ (by omega)⟩ : Fin (2 + kC * 3)) =
          ⟨2 + (finProdFinEquiv (b, (2 : Fin 3))).val, by
            simp [finProdFinEquiv]
            omega⟩ := by
        have hlt : 2 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1 <
            2 + kC * 3 := by
          simp [finProdFinEquiv]
          omega
        apply Fin.ext
        change (2 + (finProdFinEquiv (b, (1 : Fin 3))).val + 1) %
          (2 + kC * 3) = 2 + (finProdFinEquiv (b, (2 : Fin 3))).val
        rw [Nat.mod_eq_of_lt hlt]
        simp [finProdFinEquiv]
        omega
      rw [hnext] at h
      exact h
  have cross2 : H2.Adj (Sum.inl (idAR (Sum.inr (0 : Fin 1))))
      (Sum.inr (idCT (Sum.inr (0 : Fin 2)))) := by
    dsimp [idAR, idCT]
    change G.Adj (combined (Sum.inr (Sum.inl (Sum.inr (0 : Fin 1)))))
      (combined (Sum.inr (Sum.inr (Sum.inr (0 : Fin 2)))))
    rw [hcombAR, hcombCT, hcjoin0]
    dsimp [blockAR]
    exact crossAC
  have cross2b : H2.Adj (Sum.inr (idCT (Sum.inr (0 : Fin 2))))
      (Sum.inr (idCT (Sum.inr (1 : Fin 2)))) := by
    dsimp [idCT]
    change G.Adj (combined (Sum.inr (Sum.inr (Sum.inr (0 : Fin 2)))))
      (combined (Sum.inr (Sum.inr (Sum.inr (1 : Fin 2)))))
    rw [hcombCT, hcombCT, hcjoin0, hcjoin1]
    have hnext : (⟨((0 : Fin (2 + kC * 3)).val + 1) % (2 + kC * 3),
        Nat.mod_lt _ (by omega)⟩ : Fin (2 + kC * 3)) = 1 := by
      apply Fin.ext
      norm_num [Nat.mod_eq_of_lt (by omega : 1 < 2 + kC * 3)]
    have h := cycleC 0
    rw [hnext] at h
    exact h
  obtain ⟨p2⟩ := R03SP01ThreePieceCrossAssembly
    H2 0 kC idAR idCT edgeAR edgeCT cross2 cross2b
  have h1 : ∀ {x y : AL ⊕ BT}, H1.Adj x y →
      H.Adj (Sum.inl x) (Sum.inl y) := by intro x y h; exact h
  have h2 : ∀ {x y : AR ⊕ CT}, H2.Adj x y →
      H.Adj (Sum.inr x) (Sum.inr y) := by intro x y h; exact h
  obtain ⟨p⟩ := R03SP01P3FactorSum H1 H2 H p1 p2 h1 h2
  refine ⟨{
    blockCount := p.blockCount
    place := p.place.trans combined
    edge01 := ?_
    edge12 := ?_
  }⟩
  · intro i
    exact p.edge01 i
  · intro i
    exact p.edge12 i
