-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreePieceCrossAssembly
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:31:01.302946+00:00
-- url     : https://prove2.me/submissions/a9ad3146-b220-4ac1-8248-86bae6edf245

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition
universe u
set_option maxHeartbeats 1000000


end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
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

