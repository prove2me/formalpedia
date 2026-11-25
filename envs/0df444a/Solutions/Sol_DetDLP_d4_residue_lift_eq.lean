-- Prove2me | solution 1 for DetDLP.d4_residue_lift_eq
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T08:29:46.786301+00:00
-- url     : https://prove2.me/submissions/2379613f-25cb-4c2f-9bed-ac1fb84e7d31

import Definitions.Def_DetDLP_D4StoppedNode
set_option autoImplicit false
open Polynomial DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4StoppedNode
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem readCoeff {R : Type*} [CommRing R] {g : R[X]} (hg : g.Monic)
    {n : ℕ} (hn : Nontrivial R → g.natDegree = n) (b : Fin n → R) (i : Fin n) :
    (AdjoinRoot.modByMonicHom hg (AdjoinRoot.mk _ (∑ j : Fin n, monomial j.val (b j)))).coeff i = b i := by
  nontriviality R
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hg).mpr]
  · simp only [finsetSum_coeff, coeff_monomial, Fin.val_eq_val, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [degree_eq_natDegree hg.ne_zero, hn inferInstance]
    simp_rw [← C_mul_X_pow_eq_monomial]
    exact degree_sum_fin_lt _

private theorem readBase {R : Type*} [CommRing R] {g : R[X]} (hg : g.Monic)
    {n : ℕ} (hn : Nontrivial R → g.natDegree = n) (b : R) (i : Fin n) :
    (AdjoinRoot.modByMonicHom hg (AdjoinRoot.of _ b)).coeff i = if i.val = 0 then b else 0 := by
  nontriviality R
  rw [← AdjoinRoot.mk_C, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hg).mpr, coeff_C]
  · apply degree_C_le.trans_lt
    rw [degree_eq_natDegree hg.ne_zero, hn inferInstance]
    exact_mod_cast Nat.zero_lt_of_lt i.isLt

private theorem padEq (l κ : ℕ) (a : Fin l → ℕ) :
    (List.ofFn fun k : Fin (l*κ) => if (finProdFinEquiv.symm k).2.val = 0 then a (finProdFinEquiv.symm k).1 else 0) = pad κ (List.ofFn a) := by
  rw [List.ofFn_mul, pad, List.flatMap_def, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  have h (j : Fin κ) : (⟨i.val * κ + j.val, by nlinarith [Nat.mul_le_mul_right κ i.isLt,j.isLt]⟩ : Fin (l*κ)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp_rw [h, Equiv.symm_apply_apply]
  cases κ with
  | zero => simp
  | succ n => rw [List.ofFn_succ]; simp [List.ofFn_const]

theorem solution (f : ℤ[X]) (l p q : ℕ) (hf : f.Monic) (hpq : p ≤ q) :
    (∀ z : B f l p, residue f l q hf (lift hf q z) = residue f l p hf z) ∧
    (∀ a : Fin l → ℕ, (∀ j, a j < 2^q) → residue f l q hf (liftBase f l q a) =
      encodeNatListBin (pad f.natDegree (List.ofFn a))) := by
  constructor
  · intro z
    unfold residue
    congr 1
    apply congrArg List.ofFn
    funext k
    generalize hj : (finProdFinEquiv.symm k).1 = j
    generalize hi : (finProdFinEquiv.symm k).2 = i
    have hw : word f l p hf z j i < 2^q :=
      (ZMod.val_lt _).trans_le (Nat.pow_le_pow_right (by decide) hpq)
    unfold lift word
    rw [readCoeff (monic_X_pow l) (fun _ => natDegree_X_pow l), readCoeff (hf.map _) (fun _ => hf.natDegree_map _), ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hw
  · intro a ha
    unfold residue
    rw [← padEq]
    congr 1
    apply congrArg List.ofFn
    funext k
    generalize hj : (finProdFinEquiv.symm k).1 = j
    generalize hi : (finProdFinEquiv.symm k).2 = i
    unfold word liftBase
    rw [readCoeff (monic_X_pow l) (fun _ => natDegree_X_pow l), readBase (hf.map _) (fun _ => hf.natDegree_map _)]
    split <;> simp_all [ZMod.val_natCast, Nat.mod_eq_of_lt]
