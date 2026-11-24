-- Prove2me | solution 1 for DepthOneQExp.gamma_cnot_and_range
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:33:09.135595+00:00
-- url     : https://prove2.me/submissions/d4fda776-c3d3-40be-a605-fdfcafad6944

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_cnotPerm
import Definitions.Def_DepthOneQExp_cnotGroup
import Definitions.Def_DepthOneQExp_gamma

open DepthOneQExp Matrix

namespace DepthOneQExp.GammaAux

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem gamma_transvection (n : ℕ) (i j : Fin n) (h : i ≠ j) (c : ZMod 2) :
    gamma n (⟨transvection i j c, det_transvection_of_ne i j h c⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) =
      if c = 0 then 1 else cnotPerm n j i := by
  refine Equiv.ext fun x => funext fun k => ?_
  change ((transvection i j c) *ᵥ (x : Fin n → ZMod 2)) k = _
  have e1 : ∀ y : Fin n → ZMod 2, (transvection i j c *ᵥ y) k = y k + (if k = i then c * y j else 0) := by
    intro y
    simp only [transvection, Matrix.add_mulVec, Matrix.one_mulVec, single_mulVec, Pi.add_apply,
      Function.update_apply, Pi.zero_apply]
  refine (e1 x).trans ?_
  have hi : (i : ℕ) % n = i := Nat.mod_eq_of_lt i.isLt
  have hj : (j : ℕ) % n = j := Nat.mod_eq_of_lt j.isLt
  have hij : (j : ℕ) ≠ i := fun e => h (Fin.ext e).symm
  have hb : bit x j = x j := by simp [bit, hj]
  rcases zmod2_cases c with rfl | rfl
  · rw [if_pos rfl]
    show (x k + if k = i then 0 * x j else 0 : ZMod 2) = x k
    split_ifs <;> simp
  · rw [if_neg one_ne_zero]
    show (x k + if k = i then 1 * x j else 0 : ZMod 2) =
      (if (k : ℕ) = i % n ∧ j % n ≠ i % n then x k + bit x j else x k : Fin 2)
    rw [hi, hj, hb]
    by_cases hk : k = i
    · subst hk
      simp [hij]
    · have : (k : ℕ) ≠ i := fun e => hk (Fin.ext e)
      simp [hk, this]

theorem cnotPerm_mod (n a b : ℕ) : cnotPerm n (a % n) (b % n) = cnotPerm n a b := by
  ext x k
  simp [cnotPerm, bit]

theorem cnotPerm_self_mod (n a b : ℕ) (h : a % n = b % n) : cnotPerm n a b = 1 := by
  ext x k
  simp [cnotPerm, h]

/-- A transvection structure as an element of `SL`. -/
def tsl {n : ℕ} (t : TransvectionStruct (Fin n) (ZMod 2)) : SpecialLinearGroup (Fin n) (ZMod 2) :=
  ⟨t.toMatrix, det_transvection_of_ne t.i t.j t.hij t.c⟩

theorem gamma_tsl_mem {n : ℕ} (t : TransvectionStruct (Fin n) (ZMod 2)) :
    gamma n (tsl t) ∈ cnotGroup n := by
  have := gamma_transvection n t.i t.j t.hij t.c
  have e : tsl t = ⟨transvection t.i t.j t.c, det_transvection_of_ne t.i t.j t.hij t.c⟩ := rfl
  rw [e, this]
  split_ifs
  · exact one_mem _
  · exact cnotPerm_mem_cnotGroup _ _ _

theorem coe_list_prod_tsl {n : ℕ} (L : List (TransvectionStruct (Fin n) (ZMod 2))) :
    ((L.map tsl).prod : SpecialLinearGroup (Fin n) (ZMod 2)) =
      ((L.map TransvectionStruct.toMatrix).prod : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  induction L with
  | nil => simp
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    show (tsl t).1 * ((L.map tsl).prod).1 = _
    rw [show ((L.map tsl).prod).1 = _ from ih]
    rfl

theorem gamma_list_mem {n : ℕ} (L : List (TransvectionStruct (Fin n) (ZMod 2))) :
    gamma n (L.map tsl).prod ∈ cnotGroup n := by
  rw [map_list_prod, List.map_map]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
  exact gamma_tsl_mem t

theorem range_gamma (n : ℕ) : (gamma n).range = cnotGroup n := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    obtain ⟨L, L', D, hg⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec
      (g : Matrix (Fin n) (Fin n) (ZMod 2))
    have hdet : (diagonal D).det = 1 := by
      have := congrArg Matrix.det hg
      rw [g.prop, det_mul, det_mul] at this
      have h1 : ∀ L : List (TransvectionStruct (Fin n) (ZMod 2)),
          (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
        intro L
        rw [← coe_list_prod_tsl]
        exact ((L.map tsl).prod).prop
      rw [h1, h1, one_mul, mul_one] at this
      exact this.symm
    have hD : diagonal D = 1 := by
      rw [det_diagonal] at hdet
      have : ∀ i, D i = 1 := by
        intro i
        rcases zmod2_cases (D i) with h0 | h1
        · exfalso
          rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at hdet
          exact zero_ne_one hdet
        · exact h1
      ext a b
      simp [diagonal, Matrix.one_apply, this]
    have hg' : g = (L.map tsl).prod * (L'.map tsl).prod := by
      apply Subtype.ext
      show g.1 = ((L.map tsl).prod).1 * ((L'.map tsl).prod).1
      rw [show ((L.map tsl).prod).1 = _ from coe_list_prod_tsl L,
        show ((L'.map tsl).prod).1 = _ from coe_list_prod_tsl L', show g.1 = _ from hg, hD, mul_one]
    rw [hg', map_mul]
    exact mul_mem (gamma_list_mem L) (gamma_list_mem L')
  · apply (Subgroup.closure_le _).2
    rintro _ ⟨a, b, rfl⟩
    by_cases h : a % n = b % n
    · rw [cnotPerm_self_mod n a b h]
      exact one_mem _
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · have : cnotPerm 0 a b = 1 := Subsingleton.elim _ _
        rw [this]
        exact one_mem _
      have hne : (⟨b % n, Nat.mod_lt _ hn⟩ : Fin n) ≠ ⟨a % n, Nat.mod_lt _ hn⟩ :=
        fun e => h (congrArg Fin.val e).symm
      refine ⟨⟨transvection _ _ 1, det_transvection_of_ne _ _ hne 1⟩, ?_⟩
      rw [gamma_transvection _ _ _ hne, if_neg one_ne_zero]
      exact cnotPerm_mod n a b

end DepthOneQExp.GammaAux

open DepthOneQExp.GammaAux in
theorem solution (n : ℕ) :
    (∀ (i j : Fin n) (h : i ≠ j),
      gamma n ⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j h 1⟩ =
        cnotPerm n j i) ∧
    (gamma n).range = cnotGroup n := by
  refine ⟨fun i j h => ?_, range_gamma n⟩
  rw [gamma_transvection n i j h 1, if_neg one_ne_zero]
