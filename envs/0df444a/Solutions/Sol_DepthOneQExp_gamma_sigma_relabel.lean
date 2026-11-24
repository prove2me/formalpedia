-- Prove2me | solution 1 for DepthOneQExp.gamma_sigma_relabel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:23:28.560409+00:00
-- url     : https://prove2.me/submissions/bd73519f-163a-45f1-bcd9-b68defa67226

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_gamma
import Definitions.Def_DepthOneQExp_sigma
import Definitions.Def_DepthOneQExp_relabel
import Definitions.Def_DepthOneQExp_cnotGroup
import Definitions.Def_DepthOneQExp_cnotU

open DepthOneQExp Matrix

namespace DepthOneQExp.RelabelAux

theorem cnotPerm_apply' (n a b : ℕ) (x : MITMSynthesis.Q n) : cnotPerm n a b x =
    fun k : Fin n => if (k : ℕ) = b % n ∧ a % n ≠ b % n then x k + bit x a else x k := rfl

theorem mod3s (s q r : ℕ) (hr : r < 3) : (3 * q + r) % (3 * s) = 3 * (q % s) + r := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  have h1 : 3 * q + r = (3 * s) * (q / s) + (3 * (q % s) + r) := by
    have := Nat.div_add_mod q s
    nlinarith
  rw [h1, Nat.mul_add_mod]
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt q hs
  omega

theorem mod3_eq (s i a : ℕ) : (3 * i + a) % (3 * s) % 3 = a % 3 := by
  rw [Nat.mod_mod_of_dvd _ (Dvd.intro s rfl)]
  omega

/-- action of a layer `∏_{i<k} CNOT_{3i+a', 3i+b'}` -/
theorem layer_apply (s a' b' : ℕ) (hb : b' < 3) (hab : a' % 3 ≠ b') (k : ℕ) (hk : k ≤ s)
    (x : MITMSynthesis.Q (3 * s)) (t : Fin (3 * s)) :
    (((List.range k).map fun i => cnotPerm (3 * s) (3 * i + a') (3 * i + b')).prod x) t =
      if (t : ℕ) % 3 = b' ∧ (t : ℕ) / 3 < k then
        x t + x ⟨(3 * ((t : ℕ) / 3) + a') % (3 * s), Nat.mod_lt _ (by have := t.2; omega)⟩
      else x t := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      Equiv.Perm.mul_apply, ih (by omega)]
    set y := cnotPerm (3 * s) (3 * k + a') (3 * k + b') x
    have hk3 : 3 * k + b' < 3 * s := by omega
    have hmodb : (3 * k + b') % (3 * s) = 3 * k + b' := Nat.mod_eq_of_lt hk3
    have hne : (3 * k + a') % (3 * s) ≠ (3 * k + b') % (3 * s) := by
      intro h
      have := congrArg (· % 3) h
      simp only [mod3_eq] at this
      omega
    have hy : ∀ w : Fin (3 * s), y w = if (w : ℕ) = 3 * k + b' then
        x w + x ⟨(3 * k + a') % (3 * s), Nat.mod_lt _ (by omega)⟩ else x w := by
      intro w
      simp only [y, cnotPerm_apply', hmodb]
      by_cases hw : (w : ℕ) = 3 * k + b'
      · rw [if_pos ⟨hw, by rwa [hmodb] at hne⟩, if_pos hw]
        simp [bit, show (3 * k + a') % (3 * s) < 3 * s from Nat.mod_lt _ (by omega)]
      · rw [if_neg (fun h => hw h.1), if_neg hw]
    have hctrl : ∀ w : Fin (3 * s), ((3 * ((w : ℕ) / 3) + a') % (3 * s)) ≠ 3 * k + b' := by
      intro w h
      have := congrArg (· % 3) h
      simp only [mod3_eq] at this
      omega
    by_cases ht : (t : ℕ) = 3 * k + b'
    · have h1 : ¬ ((t : ℕ) % 3 = b' ∧ (t : ℕ) / 3 < k) := by omega
      have h2 : (t : ℕ) % 3 = b' ∧ (t : ℕ) / 3 < k + 1 := by omega
      have h3 : (t : ℕ) / 3 = k := by omega
      rw [if_neg h1, if_pos h2, hy, if_pos ht]
      congr 2
      simp only [h3]
    · rw [hy t, if_neg ht]
      by_cases hc : (t : ℕ) % 3 = b' ∧ (t : ℕ) / 3 < k
      · have h2 : (t : ℕ) % 3 = b' ∧ (t : ℕ) / 3 < k + 1 := ⟨hc.1, by omega⟩
        rw [if_pos hc, if_pos h2, hy, if_neg (hctrl t)]
      · have h2 : ¬ ((t : ℕ) % 3 = b' ∧ (t : ℕ) / 3 < k + 1) := by omega
        rw [if_neg hc, if_neg h2]

/-- a bit string as an `𝔽₂`-vector -/
def toZ {n : ℕ} (x : MITMSynthesis.Q n) : Fin n → ZMod 2 := x

/-- new labels: block `c`, offset `i` ↦ qubit `3 i + c` -/
def E3 (s : ℕ) : Fin 3 × Fin s ≃ Fin (3 * s) :=
  (Equiv.prodComm (Fin 3) (Fin s)).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm s 3)))

theorem E3_val (s : ℕ) (c : Fin 3) (i : Fin s) : (E3 s (c, i) : ℕ) = 3 * i + c := by
  simp [E3, finProdFinEquiv]; ring

theorem lhs_apply (s : ℕ) (a b : Fin 3) (hab : a ≠ b) (r : Matrix (Fin s) (Fin s) (ZMod 2))
    (x : MITMSynthesis.Q (3 * s)) (c : Fin 3) (i : Fin s) :
    toZ ((relabel s * gamma (3 * s) ⟨blockElem s a b r, det_blockElem s hab r⟩ * (relabel s)⁻¹) x) (E3 s (c, i)) =
      toZ x (E3 s (c, i)) + if c = a then ∑ j, r i j * toZ x (E3 s (b, j)) else 0 := by
  have he : (finProdFinEquiv.symm.trans ((Equiv.prodComm (Fin 3) (Fin s)).trans
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm s 3))))) = finProdFinEquiv.symm.trans (E3 s) := rfl
  simp only [Equiv.Perm.mul_apply, relabel, Equiv.Perm.inv_def, he]
  set e := finProdFinEquiv.symm.trans (E3 s) with hedef
  show (blockElem s a b r *ᵥ toZ (fun m => x (e m))) (e.symm (E3 s (c, i))) = _
  have h1 : e.symm (E3 s (c, i)) = finProdFinEquiv (c, i) := by simp [hedef]
  rw [h1, blockElem, reindex_apply, submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  have h2 : (toZ fun m => x (e m)) ∘ finProdFinEquiv = fun q => toZ x (E3 s q) := by
    funext q; simp only [Function.comp_apply, hedef, Equiv.trans_apply]
    show x ((E3 s) (finProdFinEquiv.symm (finProdFinEquiv q))) = x (E3 s q)
    rw [Equiv.symm_apply_apply]
  rw [h2]
  congr 1
  simp only [mulVec, dotProduct, of_apply]
  rw [Fintype.sum_prod_type]
  split_ifs with hca
  · rw [Finset.sum_eq_single b]
    · simp [hca]
    · intro d _ hd; simp [hd]
    · simp
  · simp [hca]

theorem E3_surj (s : ℕ) (t : Fin (3 * s)) : ∃ c i, t = E3 s (c, i) :=
  ⟨((E3 s).symm t).1, ((E3 s).symm t).2, by simp⟩

theorem perm_ext_E3 (s : ℕ) (σ τ : Equiv.Perm (MITMSynthesis.Q (3 * s)))
    (h : ∀ x c i, toZ (σ x) (E3 s (c, i)) = toZ (τ x) (E3 s (c, i))) : σ = τ := by
  refine Equiv.ext fun x => funext fun t => ?_
  obtain ⟨c, i, rfl⟩ := E3_surj s t
  exact h x c i

theorem layer_E3 (s a' b' : ℕ) (hb : b' < 3) (hab : a' % 3 ≠ b') (x : MITMSynthesis.Q (3 * s))
    (c : Fin 3) (i : Fin s) :
    toZ ((((List.range s).map fun i => cnotPerm (3 * s) (3 * i + a') (3 * i + b')).prod) x) (E3 s (c, i)) =
      if (c : ℕ) = b' then toZ x (E3 s (c, i)) +
        toZ x ⟨(3 * i + a') % (3 * s), Nat.mod_lt _ (by have := i.2; omega)⟩ else toZ x (E3 s (c, i)) := by
  unfold toZ
  rw [layer_apply s a' b' hb hab s le_rfl]
  have hv := E3_val s c i
  have h1 : ((E3 s (c, i) : ℕ) % 3 = b' ∧ (E3 s (c, i) : ℕ) / 3 < s) ↔ (c : ℕ) = b' := by
    rw [hv]; have := c.2; have := i.2; omega
  have h2 : (E3 s (c, i) : ℕ) / 3 = i := by rw [hv]; have := c.2; omega
  by_cases hc : (c : ℕ) = b'
  · rw [if_pos (h1.2 hc)]
    simp only [h2]
    exact (if_pos hc).symm
  · rw [if_neg (fun h => hc (h1.1 h))]
    exact (if_neg hc).symm

theorem caseI (s : ℕ) (a b : Fin 3) (hab : a ≠ b) :
    relabel s * gamma (3 * s) ⟨blockElem s a b 1, det_blockElem s hab 1⟩ * (relabel s)⁻¹ =
      ((List.range s).map fun i => cnotPerm (3 * s) (3 * i + b) (3 * i + a)).prod := by
  apply perm_ext_E3
  intro x c i
  rw [lhs_apply s a b hab, layer_E3 s b a a.2 (by have := b.2; rw [Nat.mod_eq_of_lt this]; exact fun h => hab (Fin.ext h).symm)]
  have hsum : ∑ j, (1 : Matrix (Fin s) (Fin s) (ZMod 2)) i j * toZ x (E3 s (b, j)) = toZ x (E3 s (b, i)) := by
    simp [Matrix.one_apply]
  rw [hsum]
  by_cases hc : c = a
  · rw [if_pos hc, if_pos (congrArg Fin.val hc)]
    congr 2
    exact Fin.ext (by simp only [Fin.val_mk, E3_val]; rw [mod3s s i b b.2, Nat.mod_eq_of_lt i.2])
  · rw [if_neg hc, if_neg (fun h => hc (Fin.ext h)), add_zero]

theorem caseA (s : ℕ) (hs : 1 ≤ s) (a b : Fin 3) (hab : a ≠ b) :
    relabel s * gamma (3 * s) ⟨blockElem s a b (kassabovA s), det_blockElem s hab _⟩ * (relabel s)⁻¹ =
      ((List.range s).map fun i => cnotPerm (3 * s) (3 * i + (3 + b)) (3 * i + a)).prod := by
  apply perm_ext_E3
  intro x c i
  have hab' : (3 + (b : ℕ)) % 3 ≠ a := by
    have := b.2; have := a.2; intro h; apply hab; apply Fin.ext; omega
  rw [lhs_apply s a b hab, layer_E3 s (3 + b) a a.2 hab']
  have hsum : ∑ j, kassabovA s i j * toZ x (E3 s (b, j)) =
      toZ x (E3 s (b, ⟨((i : ℕ) + 1) % s, Nat.mod_lt _ (by omega)⟩)) := by
    rw [Finset.sum_eq_single ⟨((i : ℕ) + 1) % s, Nat.mod_lt _ (by omega)⟩]
    · simp [kassabovA]
    · intro j _ hj
      have : ¬ ((j : ℕ) = ((i : ℕ) + 1) % s) := fun h => hj (Fin.ext h)
      simp [kassabovA, this]
    · simp
  rw [hsum]
  by_cases hc : c = a
  · rw [if_pos hc, if_pos (congrArg Fin.val hc)]
    congr 2
    exact Fin.ext (by
      simp only [E3_val]
      rw [show 3 * (i : ℕ) + (3 + b) = 3 * ((i : ℕ) + 1) + b by ring, mod3s s _ b b.2])
  · rw [if_neg hc, if_neg (fun h => hc (Fin.ext h)), add_zero]

theorem cnot_toZ (n a' b' : ℕ) (hn : 0 < n) (x : MITMSynthesis.Q n) (t : Fin n) :
    toZ (cnotPerm n a' b' x) t = if (t : ℕ) = b' % n ∧ a' % n ≠ b' % n then
      toZ x t + toZ x ⟨a' % n, Nat.mod_lt _ hn⟩ else toZ x t := by
  unfold toZ
  rw [cnotPerm_apply']
  simp only [bit, dif_pos (Nat.mod_lt a' hn)]
  split_ifs with h
  · exact (if_pos h).symm
  · exact (if_neg h).symm

theorem caseB (s : ℕ) (hs : 1 ≤ s) (a b : Fin 3) (hab : a ≠ b) :
    relabel s * gamma (3 * s) ⟨blockElem s a b (kassabovB s), det_blockElem s hab _⟩ * (relabel s)⁻¹ =
      cnotPerm (3 * s) b a := by
  apply perm_ext_E3
  intro x c i
  rw [lhs_apply s a b hab]
  have hsum : ∑ j, kassabovB s i j * toZ x (E3 s (b, j)) =
      if (i : ℕ) = 0 then toZ x (E3 s (b, ⟨0, by omega⟩)) else 0 := by
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · simp [kassabovB]
    · intro j _ hj
      have : ¬ ((j : ℕ) = 0) := fun h => hj (Fin.ext h)
      simp [kassabovB, this]
    · simp
  rw [hsum, cnot_toZ _ _ _ (by omega)]
  have ha3 : (a : ℕ) < 3 * s := by have := a.2; omega
  have hb3 : (b : ℕ) < 3 * s := by have := b.2; omega
  have hne : (b : ℕ) % (3 * s) ≠ (a : ℕ) % (3 * s) := by
    rw [Nat.mod_eq_of_lt ha3, Nat.mod_eq_of_lt hb3]; exact fun h => hab (Fin.ext h).symm
  have hv := E3_val s c i
  by_cases hci : c = a ∧ (i : ℕ) = 0
  · have h1 : (E3 s (c, i) : ℕ) = (a : ℕ) % (3 * s) := by
      rw [hv, Nat.mod_eq_of_lt ha3, hci.2, hci.1]; ring
    have h0 : (⟨(b : ℕ) % (3 * s), Nat.mod_lt _ (by omega)⟩ : Fin (3 * s)) = E3 s (b, ⟨0, by omega⟩) :=
      Fin.ext (by simp [E3_val, Nat.mod_eq_of_lt hb3])
    simp only [hci.1, hci.2, if_true, h0]
    rw [if_pos ⟨by rw [E3_val, hci.2, Nat.mod_eq_of_lt ha3]; ring, hne⟩]
  · have h1 : ¬ ((E3 s (c, i) : ℕ) = (a : ℕ) % (3 * s) ∧ (b : ℕ) % (3 * s) ≠ (a : ℕ) % (3 * s)) := by
      rintro ⟨h, -⟩
      rw [hv, Nat.mod_eq_of_lt ha3] at h
      apply hci
      have := c.2; have := a.2
      exact ⟨Fin.ext (by omega), by omega⟩
    rw [if_neg h1]
    by_cases hc : c = a
    · have : ¬ (i : ℕ) = 0 := fun h => hci ⟨hc, h⟩
      simp only [hc, if_true, this, if_false, add_zero]
    · simp only [hc, if_false, add_zero]

end DepthOneQExp.RelabelAux


open DepthOneQExp.RelabelAux in
theorem solution (s : ℕ) (hs : 1 ≤ s) :
    ∃ τ : Fin 14 ≃ Fin 14, ∀ j : Fin 14,
      relabel s * gamma (3 * s) (sigma s j) * (relabel s)⁻¹ =
        ((cnotU s (τ j) : cnotGroup (3 * s)) : Equiv.Perm (MITMSynthesis.Q (3 * s))) := by
  refine ⟨Equiv.ofBijective (![6, 8, 4, 9, 5, 7, 11, 10, 13, 12, 1, 0, 3, 2] : Fin 14 → Fin 14)
    (by decide), fun j => ?_⟩
  fin_cases j
  · have h := caseI s 0 1 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseI s 0 2 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseI s 1 0 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseI s 1 2 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseI s 2 0 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseI s 2 1 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseA s hs 0 1 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseA s hs 1 0 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseA s hs 1 2 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseA s hs 2 1 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseB s hs 0 1 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseB s hs 1 0 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseB s hs 1 2 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
  · have h := caseB s hs 2 1 (by decide)
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd] at h
    convert h using 1
    · rfl
    · simp only [Equiv.ofBijective_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
      unfold cnotU
      dsimp only
      simp only [Matrix.cons_val, Fin.reduceFinMk, SubmonoidClass.coe_list_prod, List.map_map]
      try rfl
