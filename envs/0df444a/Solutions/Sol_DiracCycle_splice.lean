-- Prove2me | solution 1 for DiracCycle.splice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:52:28.754933+00:00
-- url     : https://prove2.me/submissions/f4216f6f-5b03-48ce-8b58-1af475bc7b9b

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
public import Theorems.Thm_Hamiltonicity_CycArr_of_fun
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}
namespace DiracCycle
theorem _root_.solution {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) {d : ℕ} (hd1 : 1 ≤ d) (hdm : d < m)
    (Q : G.Walk (f 0) (f d)) (hQ : Q.IsPath) (hQl : 2 ≤ Q.length)
    (hint : ∀ y ∈ Q.support, ∀ i, f i = y → y = f 0 ∨ y = f d) :
    ∃ m' g, CycArr G m' g ∧ (∀ y ∈ Q.support, ∃ i, g i = y) ∧
      ∀ i, d ≤ i → i ≤ m → ∃ j, g j = f i := by
  set l := Q.length with hl
  have hm := hC.three_le
  set q := Q.getVert with hq
  have hq0 : q 0 = f 0 := Q.getVert_zero
  have hql : q l = f d := Q.getVert_length
  have hqinj : ∀ i j, i ≤ l → j ≤ l → q i = q j → i = j := fun i j hi hj h =>
    hQ.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) h
  have hqoff : ∀ i, 0 < i → i < l → ∀ j, f j ≠ q i := by
    intro i hi0 hil j hj
    rcases hint (q i) (Q.getVert_mem_support i) j hj with h | h
    · have := hqinj i 0 (by omega) (by omega) (h.trans hq0.symm)
      omega
    · have := hqinj i l (by omega) le_rfl (h.trans hql.symm)
      omega
  have hfinj : ∀ i j, i < m → j < m → f i = f j → i = j := hC.inj
  set h : ℕ → V := fun j => if j ≤ l then q j else f (j - l + d) with hh
  have hA : ∀ j, j ≤ l → h j = q j := fun j hj => by
    simp only [hh]
    rw [if_pos hj]
  have hB : ∀ j, l < j → h j = f (j - l + d) := fun j hj => by
    simp only [hh]
    rw [if_neg (by omega)]
  have hend : h (l + (m - d)) = h 0 := by
    rw [hB _ (by omega), hA 0 (Nat.zero_le _), hq0,
      show l + (m - d) - l + d = 0 + m by omega, hC.periodic]
  have hCA := CycArr.of_fun (G := G) (m := l + (m - d)) (h := h) (by omega) ?_ ?_ hend
  · refine ⟨_, _, hCA, ?_, ?_⟩
    · intro y hy
      obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.1 hy
      refine ⟨n, ?_⟩
      rw [Nat.mod_eq_of_lt (by omega), hA n hnl]
      exact hn
    · intro i hi1 hi2
      by_cases him : i = m
      · subst him
        refine ⟨0, ?_⟩
        rw [Nat.zero_mod]
        rw [hA 0 (Nat.zero_le _), hq0, show i = 0 + i by omega, hC.periodic]
      by_cases hid : i = d
      · subst hid
        refine ⟨l, ?_⟩
        rw [Nat.mod_eq_of_lt (by omega), hA l le_rfl, hql]
      · refine ⟨i - d + l, ?_⟩
        rw [Nat.mod_eq_of_lt (by omega), hB _ (by omega), show i - d + l - l + d = i by omega]
  · intro a b ha hb hab
    have hmix : ∀ a b, a ≤ l → l < b → b < l + (m - d) → h a ≠ h b := by
      intro a b ha hb1 hb2 hab
      rw [hA a ha, hB b hb1] at hab
      by_cases ha0 : a = 0
      · subst ha0
        rw [hq0] at hab
        have := hfinj _ _ (by omega) (by omega) hab
        omega
      by_cases hal : a = l
      · subst hal
        rw [hql] at hab
        have := hfinj _ _ (by omega) (by omega) hab
        omega
      exact hqoff a (by omega) (by omega) _ hab.symm
    by_cases ha' : a ≤ l <;> by_cases hb' : b ≤ l
    · rw [hA a ha', hA b hb'] at hab
      exact hqinj a b ha' hb' hab
    · exact absurd hab (hmix a b ha' (by omega) hb)
    · exact absurd hab.symm (hmix b a hb' (by omega) ha)
    · rw [hB a (by omega), hB b (by omega)] at hab
      have := hfinj _ _ (by omega) (by omega) hab
      omega
  · intro j hj
    rcases lt_trichotomy j l with hjl | rfl | hjl
    · rw [hA j hjl.le, hA (j + 1) hjl]
      exact Q.adj_getVert_succ hjl
    · rw [hA _ le_rfl, hql, hB _ (by omega), show Q.length + 1 - Q.length + d = d + 1 by omega]
      exact hC.adj d
    · rw [hB j hjl, hB (j + 1) (by omega), show j + 1 - l + d = j - l + d + 1 by omega]
      exact hC.adj _
end DiracCycle
