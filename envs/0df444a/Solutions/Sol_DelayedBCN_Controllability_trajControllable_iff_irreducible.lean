-- Prove2me | solution 1 for DelayedBCN.Controllability.trajControllable_iff_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:57:14.463635+00:00
-- url     : https://prove2.me/submissions/e434d4b2-4810-4dba-bdf2-9f142152b005

import Mathlib
import Definitions.Def_DelayedBCN_Controllability_Model
import Definitions.Def_DelayedBCN_Controllability_Matrix
import Theorems.Thm_DelayedBCN_Controllability_trajControllableUnder_iff_irreducible

open DelayedBCN.Controllability

namespace DelayedBCN.Controllability

variable {μ n m : ℕ} (F : Network μ n m) (X0 : Traj μ n)

lemma solAux_trajAt_append_left (k1 k2 : ℕ) (U : Fin k1 → Input m) (V : Fin k2 → Input m) :
    ∀ i ≤ k1, trajAt F X0 (Fin.append U V) i = trajAt F X0 U i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hi' : i < k1 := Nat.lt_of_succ_le hi
    have h1 : i < k1 + k2 := by omega
    have hstep : trajAt F X0 (Fin.append U V) (i + 1)
        = step F ((Fin.append U V) ⟨i, h1⟩) (trajAt F X0 (Fin.append U V) i) := by
      simp only [trajAt, dif_pos h1]
    have hentry : (Fin.append U V) ⟨i, h1⟩ = U ⟨i, hi'⟩ := by
      rw [show (⟨i, h1⟩ : Fin (k1 + k2)) = Fin.castAdd k2 ⟨i, hi'⟩ from rfl,
        Fin.append_left]
    rw [hstep, hentry]
    simp only [trajAt, dif_pos hi']
    rw [ih (Nat.le_of_lt hi')]

lemma solAux_trajAt_comp_aux (k1 k2 : ℕ) (U : Fin k1 → Input m) (V : Fin k2 → Input m) :
    ∀ j ≤ k2, trajAt F X0 (Fin.append U V) (k1 + j)
      = trajAt F (trajAt F X0 U k1) V j := by
  intro j
  induction j with
  | zero =>
    intro _
    show trajAt F X0 (Fin.append U V) k1 = trajAt F (trajAt F X0 U k1) V 0
    rw [solAux_trajAt_append_left F X0 k1 k2 U V k1 le_rfl]
    rfl
  | succ j ih =>
    intro hj
    have hj' : j < k2 := Nat.lt_of_succ_le hj
    have h1 : k1 + j < k1 + k2 := by omega
    have hstepL : trajAt F X0 (Fin.append U V) (k1 + (j + 1))
        = step F ((Fin.append U V) ⟨k1 + j, h1⟩)
            (trajAt F X0 (Fin.append U V) (k1 + j)) := by
      have hk : k1 + (j + 1) = (k1 + j) + 1 := by ring
      rw [hk]
      simp only [trajAt, dif_pos h1]
    have hentry : (Fin.append U V) ⟨k1 + j, h1⟩ = V ⟨j, hj'⟩ := by
      rw [show (⟨k1 + j, h1⟩ : Fin (k1 + k2)) = Fin.natAdd k1 ⟨j, hj'⟩ from rfl,
        Fin.append_right]
    have hstepR : trajAt F (trajAt F X0 U k1) V (j + 1)
        = step F (V ⟨j, hj'⟩) (trajAt F (trajAt F X0 U k1) V j) := by
      simp only [trajAt, dif_pos hj']
    rw [hstepL, hentry, ih (Nat.le_of_lt hj'), hstepR]

lemma solAux_trajAt_comp (k1 k2 : ℕ) (U : Fin k1 → Input m) (V : Fin k2 → Input m) :
    trajAt F X0 (Fin.append U V) (k1 + k2) = trajAt F (trajAt F X0 U k1) V k2 :=
  solAux_trajAt_comp_aux F X0 k1 k2 U V k2 le_rfl

lemma solAux_mem_trajReachableSet_iff {Xd : Traj μ n} :
    Xd ∈ trajReachableSet F X0 ↔
      ∃ k, ∃ _ : 1 ≤ k, ∃ U : Fin k → Input m, trajAt F X0 U k = Xd := by
  simp only [trajReachableSet, trajReachableSetAt, IsTrajReachableAt, Set.mem_iUnion,
    Set.mem_ofPred_eq, exists_prop]

lemma solAux_trajControllable_iff_under_empty :
    TrajControllable F ↔ TrajControllableUnder F ∅ := by
  constructor
  · intro h a b _ _
    have hb : b ∈ trajReachableSet F a := by
      rw [h a]; exact Set.mem_univ b
    rw [solAux_mem_trajReachableSet_iff] at hb
    obtain ⟨k, hk, U, hU⟩ := hb
    exact ⟨k, U, hU, fun i => by simp⟩
  · intro h X0
    ext Xd
    rw [solAux_mem_trajReachableSet_iff]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rcases h X0 Xd (by simp) (by simp) with ⟨k, U, hU, -⟩
    rcases k with _ | k'
    · have hX : X0 = Xd := hU
      by_cases hss : Subsingleton (Traj μ n)
      · refine ⟨1, le_rfl, fun _ => (default : Input m), ?_⟩
        have hstep : step F (default : Input m) X0 = X0 := Subsingleton.elim _ _
        simp only [trajAt, dif_pos (show 0 < 1 by norm_num)]
        rw [hstep]
        exact hX
      · have hnt : Nontrivial (Traj μ n) := not_subsingleton_iff_nontrivial.mp hss
        obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
        have hXc : (if ha : a = X0 then b else a) ≠ X0 := by
          by_cases ha : a = X0
          · simp only [dif_pos ha]
            rw [ha] at hab
            exact fun h => hab h.symm
          · simpa only [dif_neg ha] using ha
        rcases h X0 (if ha : a = X0 then b else a) (by simp) (by simp)
          with ⟨k1, U1, hU1, -⟩
        rcases h (if ha : a = X0 then b else a) X0 (by simp) (by simp)
          with ⟨k2, U2, hU2, -⟩
        have hk1 : 1 ≤ k1 := by
          rcases Nat.eq_zero_or_pos k1 with h0 | hpos
          · exfalso
            cases h0
            exact hXc hU1.symm
          · exact hpos
        have hk2 : 1 ≤ k2 := by
          rcases Nat.eq_zero_or_pos k2 with h0 | hpos
          · exfalso
            cases h0
            exact hXc hU2
          · exact hpos
        refine ⟨k1 + k2, by omega, Fin.append U1 U2, ?_⟩
        rw [solAux_trajAt_comp F X0 k1 k2 U1 U2, hU1, hU2]
        exact hX
    · exact ⟨k' + 1, Nat.succ_le_succ (Nat.zero_le k'), U, hU⟩

lemma solAux_isReducibleMat_submatrix_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (A : Matrix ι ι ℝ) :
    IsReducibleMat (A.submatrix e e) ↔ IsReducibleMat A := by
  constructor
  · rintro ⟨f, r, hr1, hr2, hzero⟩
    have hc : Fintype.card ι' = Fintype.card ι := Fintype.card_congr e
    refine ⟨(finCongr hc.symm).trans (f.trans e), r, hr1, ?_, ?_⟩
    · rw [← hc]; exact hr2
    · intro i j hi hj
      exact hzero (finCongr hc.symm i) (finCongr hc.symm j) hi hj
  · rintro ⟨g, r, hr1, hr2, hzero⟩
    have hc : Fintype.card ι' = Fintype.card ι := Fintype.card_congr e
    refine ⟨(finCongr hc).trans (g.trans e.symm), r, hr1, ?_, ?_⟩
    · rw [hc]; exact hr2
    · intro i j hi hj
      have h1 : ((finCongr hc).trans (g.trans e.symm)) i = e.symm (g (finCongr hc i)) := rfl
      have h2 : ((finCongr hc).trans (g.trans e.symm)) j = e.symm (g (finCongr hc j)) := rfl
      rw [h1, h2]
      show A (e (e.symm (g (finCongr hc i)))) (e (e.symm (g (finCongr hc j)))) = 0
      rw [e.apply_symm_apply, e.apply_symm_apply]
      exact hzero (finCongr hc i) (finCongr hc j) hi hj

lemma solAux_isIrreducibleMat_submatrix_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) (A : Matrix ι ι ℝ) :
    IsIrreducibleMat (A.submatrix e e) ↔ IsIrreducibleMat A :=
  not_congr (solAux_isReducibleMat_submatrix_equiv e A)

end DelayedBCN.Controllability

open DelayedBCN.Controllability

/-- Theorem 3.10: TrajControllable is equivalent to irreducibility of the transition-count
matrix `Q`, by reduction to the proved Theorem 3.12 for the emptied forbidden set. -/
theorem solution {μ n m : ℕ} [NeZero μ] (F : Network μ n m) :
    TrajControllable F ↔ IsIrreducibleMat ((Q F).map (fun x : ℕ => (x : ℝ))) := by
  let e : {a : Traj μ n // a ∉ (∅ : Finset (Traj μ n))} ≃ Traj μ n :=
    { toFun := fun a => a.1
      invFun := fun a => ⟨a, Finset.notMem_empty a⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  have hsub : ((QDeleted F ∅).map (fun x : ℕ => (x : ℝ))).submatrix e.symm e.symm
      = (Q F).map (fun x : ℕ => (x : ℝ)) := by
    ext i j
    rfl
  rw [solAux_trajControllable_iff_under_empty F,
    trajControllableUnder_iff_irreducible F ∅]
  rw [← hsub]
  exact (solAux_isIrreducibleMat_submatrix_equiv e.symm
    ((QDeleted F ∅).map (fun x : ℕ => (x : ℝ)))).symm
