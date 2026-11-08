-- Prove2me | solution 1 for BaconOQEC.decodeZ
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:17:50.110007+00:00
-- url     : https://prove2.me/submissions/a3fa71be-176a-457d-ab86-40e4b6fed6dc

import Mathlib
import Definitions.Def_BaconOQEC_rowPar
import Definitions.Def_BaconOQEC_syndOf
import Definitions.Def_BaconOQEC_recZ

namespace Aux_Bacon_decodeZ
open BaconOQEC

theorem two_z : ∀ x : ZMod 2, x + x = 0 := by decide

theorem one_add_ne : ∀ x : ZMod 2, (1 + x ≠ 0) ↔ x = 0 := by decide

theorem ham_compl {m : ℕ} (v : Fin (m + 1) → ZMod 2) :
    hammingNorm (1 + v) + hammingNorm v = m + 1 := by
  unfold hammingNorm
  have : (Finset.univ.filter (fun i => (1 + v) i ≠ 0)) =
      Finset.univ.filter (fun i => ¬ (v i ≠ 0)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.one_apply]
    rw [one_add_ne]; simp
  rw [this, add_comm, Finset.card_filter_add_card_filter_not]
  simp

theorem synd_eq {m : ℕ} (a b : Bits m) (i : Fin m) :
    (syndOf a b).1 i = rowPar b i.castSucc + rowPar b i.succ := by
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  simp only [syndOf, symp, SX, Pi.zero_apply, mul_zero, zero_add]
  calc ∑ r, ∑ c, b r c * (if r = i.castSucc ∨ r = i.succ then 1 else 0)
      = ∑ r, (if r = i.castSucc ∨ r = i.succ then rowPar b r else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        split_ifs <;> simp [rowPar]
    _ = rowPar b i.castSucc + rowPar b i.succ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        have : Finset.univ.filter (fun r => r = i.castSucc ∨ r = i.succ) = {i.castSucc, i.succ} := by
          ext r; simp
        rw [this, Finset.sum_pair hne]

theorem f_eq {m : ℕ} (a b : Bits m) (k : Fin (m + 1)) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < (k : ℕ)), (syndOf a b).1 i =
      rowPar b 0 + rowPar b k := by
  induction k using Fin.induction with
  | zero => simp [two_z]
  | succ j ih =>
    have : Finset.univ.filter (fun i : Fin m => (i : ℕ) < (j.succ : ℕ)) =
        insert j (Finset.univ.filter (fun i : Fin m => (i : ℕ) < (j.castSucc : ℕ))) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.val_succ, Fin.coe_castSucc, Fin.ext_iff]; omega
    rw [this, Finset.sum_insert (by simp), ih, synd_eq]
    have := two_z (rowPar b j.castSucc)
    linear_combination this

end Aux_Bacon_decodeZ

open BaconOQEC Aux_Bacon_decodeZ in
theorem solution (m : ℕ) (a b : Bits m) (j0 : Fin (m + 1)) :
    let b' := b + recZ (syndOf a b) j0
    (∃ c : ZMod 2, ∀ i, rowPar b' i = c) ∧
    (hammingNorm (rowPar b) ≤ m / 2 → ∀ i, rowPar b' i = 0) := by
  intro b'
  set R := rowPar b with hR
  have hf : (fun k : Fin (m + 1) =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < (k : ℕ)), (syndOf a b).1 i) =
      fun k => R 0 + R k := by
    funext k; exact f_eq a b k
  have hrow : ∀ i, rowPar b' i = R i + repDecode (syndOf a b).1 i := by
    intro i
    simp only [b', rowPar, recZ, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] <;> rfl
  have hg : repDecode (syndOf a b).1 =
      if hammingNorm (fun k => R 0 + R k) ≤ hammingNorm (1 + fun k => R 0 + R k)
      then (fun k => R 0 + R k) else 1 + fun k => R 0 + R k := by
    unfold repDecode
    simp only
    rw [hf]
  have hconst : ∀ i, R i + (R 0 + R i) = R 0 := by
    intro i; linear_combination two_z (R i)
  refine ⟨?_, ?_⟩
  · by_cases hc : hammingNorm (fun k => R 0 + R k) ≤ hammingNorm (1 + fun k => R 0 + R k)
    · refine ⟨R 0, fun i => ?_⟩
      rw [hrow, hg, if_pos hc, hconst]
    · refine ⟨1 + R 0, fun i => ?_⟩
      rw [hrow, hg, if_neg hc]
      simp only [Pi.add_apply, Pi.one_apply]
      linear_combination two_z (R i)
  · intro hham i
    have hcomp := ham_compl R
    rw [hrow, hg]
    have hR0 : R 0 = 0 ∨ R 0 = 1 := (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) (R 0)
    rcases hR0 with h0 | h0
    · have e : (fun k => R 0 + R k) = R := by funext k; rw [h0, zero_add]
      rw [e, if_pos (by omega)]
      exact two_z _
    · have e : (fun k => R 0 + R k) = 1 + R := by funext k; rw [h0]; rfl
      have e2 : (1 + (1 + R)) = R := by funext k; simp only [Pi.add_apply, Pi.one_apply];
                                         linear_combination two_z (1 : ZMod 2)
      rw [e, e2, if_neg (by omega)]
      exact two_z _
