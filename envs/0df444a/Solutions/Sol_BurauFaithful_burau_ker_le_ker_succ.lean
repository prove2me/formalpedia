-- Prove2me | solution 1 for BurauFaithful.burau_ker_le_ker_succ
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T00:21:33.224727+00:00
-- url     : https://prove2.me/submissions/cb2fb126-abc5-47f8-b233-a72eca9c8271

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BurauFaithful_StandardInclusion

namespace BurauFaithful

open Matrix BraidsLinksMCG

private noncomputable def appendIdentity (n : ℕ) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial ℤ) →*
      Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (LaurentPolynomial ℤ) where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]

private noncomputable def splitLast (n : ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) (LaurentPolynomial ℤ) ≃+*
      Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (LaurentPolynomial ℤ) :=
  Matrix.reindexRingEquiv (LaurentPolynomial ℤ) finSumFinEquiv.symm

private lemma generator_block (n : ℕ) (i : Fin (n-1)) :
    splitLast n (burauMatrix (strandIdx i)) =
      appendIdentity n (burauMatrix i) := by
  classical
  apply Matrix.ext
  intro a b
  change burauMatrix (strandIdx i) (finSumFinEquiv a) (finSumFinEquiv b) =
    Matrix.fromBlocks (burauMatrix i) 0 0 1 a b
  have hi := i.isLt
  rcases a with a | a <;> rcases b with b | b
  · simp [burauMatrix_apply, strandIdx]
  · have hb : b = 0 := Subsingleton.elim _ _
    subst b
    have ha := a.isLt
    simp [burauMatrix_apply, strandIdx, show (a:ℕ) ≠ n by omega,
      show n ≠ (i:ℕ) by omega, show n ≠ (i:ℕ)+1 by omega]
  · have ha : a = 0 := Subsingleton.elim _ _
    subst a
    have hb := b.isLt
    simp [burauMatrix_apply, strandIdx, show n ≠ (b:ℕ) by omega,
      show n ≠ (i:ℕ) by omega, show n ≠ (i:ℕ)+1 by omega]
  · have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst a
    subst b
    simp [burauMatrix_apply, strandIdx,
      show n ≠ (i:ℕ) by omega, show n ≠ (i:ℕ)+1 by omega]

private lemma representation_block (n : ℕ) (Φ : ArtinBraidGroup n) :
    Units.map (splitLast n).toMonoidHom
        (burauRep (n+1) (standardInclusion n Φ)) =
      Units.map (appendIdentity n) (burauRep n Φ) := by
  let L : ArtinBraidGroup n →* GL (Fin n ⊕ Fin 1) (LaurentPolynomial ℤ) :=
    (Units.map (splitLast n).toMonoidHom).comp
      ((burauRep (n+1)).comp (standardInclusion n))
  let R : ArtinBraidGroup n →* GL (Fin n ⊕ Fin 1) (LaurentPolynomial ℤ) :=
    (Units.map (appendIdentity n)).comp (burauRep n)
  have heq : L = R := by
    apply PresentedGroup.ext
    intro i
    change Units.map (splitLast n).toMonoidHom
        (burauRep (n + 1) (standardInclusion n (PresentedGroup.of i))) =
      Units.map (appendIdentity n) (burauRep n (PresentedGroup.of i))
    have hinc : standardInclusion n (PresentedGroup.of i) =
        PresentedGroup.of (rels := braidRels (n + 1)) (strandIdx i) :=
      PresentedGroup.toGroup.of (sigma_relations_map n)
    have hgen (k : ℕ) (j : Fin (k - 1)) :
        burauRep k (PresentedGroup.of j) = burauGen j :=
      PresentedGroup.toGroup.of (burauGen_relations k)
    rw [hinc, hgen, hgen]
    apply Units.ext
    change splitLast n (burauMatrix (strandIdx i)) =
      appendIdentity n (burauMatrix i)
    exact generator_block n i
  exact congrArg (fun F : ArtinBraidGroup n →*
    GL (Fin n ⊕ Fin 1) (LaurentPolynomial ℤ) => F Φ) heq

theorem burau_ker_le_ker_succ (n : ℕ) (Φ : BraidsLinksMCG.ArtinBraidGroup n)
    (h : burauRep n Φ = 1) : burauRep (n + 1) (standardInclusion n Φ) = 1 := by
  have hb := representation_block n Φ
  rw [h, map_one] at hb
  apply Units.map_injective (f := (splitLast n).toMonoidHom) (splitLast n).injective
  simpa only [map_one] using hb

end BurauFaithful

theorem solution (n : ℕ) (Φ : BraidsLinksMCG.ArtinBraidGroup n)
    (h : BurauFaithful.burauRep n Φ = 1) :
    BurauFaithful.burauRep (n + 1) (BurauFaithful.standardInclusion n Φ) = 1 :=
  BurauFaithful.burau_ker_le_ker_succ n Φ h

#print axioms BurauFaithful.burau_ker_le_ker_succ
#print axioms solution
