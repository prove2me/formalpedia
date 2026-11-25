-- Prove2me | solution 1 for ErdosPosa.psi_restr_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:33:16.672595+00:00
-- url     : https://prove2.me/submissions/238f56b4-231a-4456-8f59-3daadde52dcd

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_ncard_eq_sum_ite
public import Theorems.Thm_ErdosPosa_deg_restr_compl_of_mem
public import Theorems.Thm_ErdosPosa_deg_restr_compl_of_notMem
public import Theorems.Thm_ErdosPosa_deg_split
public import Theorems.Thm_ErdosPosa_double_count
public import Theorems.Thm_ErdosPosa_MinCyc_two_nbrs
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable {H₀ : SimpleGraph V} {T : Set V}
namespace ErdosPosa
theorem _root_.solution [Fintype V] (hT : MinCyc H₀ T) (hdeg : ∀ v, deg H₀ v ≤ 3) :
    psi H₀ ≤ psi (restr H₀ Tᶜ) + 2 * ({t | t ∈ T ∧ deg H₀ t = 3}.ncard : ℤ) := by
  classical
  have hin : ∀ t ∈ T, 2 ≤ (H₀.neighborSet t ∩ T).ncard := by
    intro t ht
    obtain ⟨y, z, hy, hz, hyz, hty, htz⟩ := hT.two_nbrs ht
    calc 2 = ({y, z} : Set V).ncard := (Set.ncard_pair hyz).symm
      _ ≤ _ := by
        apply Set.ncard_le_ncard _ (Set.toFinite _)
        intro w hw
        rcases hw with rfl | rfl
        · exact ⟨hty, hy⟩
        · exact ⟨htz, hz⟩
  let e : V → ℤ := fun v => if v ∈ T ∧ deg H₀ v = 3 then 1 else 0
  have key1 : ∀ v, wt (deg H₀ v) ≤ wt (deg (restr H₀ Tᶜ) v) + e v +
      (if v ∉ T then ((H₀.neighborSet v ∩ T).ncard : ℤ) else 0) := by
    intro v
    have hs := deg_split (H₀ := H₀) (T := T) v
    by_cases hv : v ∈ T
    · have := hin v hv
      have := hdeg v
      rw [deg_restr_compl_of_mem hv]
      simp only [e, hv, true_and, not_true_eq_false, ↓reduceIte, add_zero]
      unfold wt
      split_ifs <;> omega
    · rw [deg_restr_compl_of_notMem hv]
      simp only [e, hv, false_and, not_false_eq_true, ↓reduceIte, add_zero]
      unfold wt
      split_ifs <;> omega
  have key2 : ∀ t, (if t ∈ T then ((H₀.neighborSet t \ T).ncard : ℤ) else 0) ≤ e t := by
    intro t
    by_cases ht : t ∈ T
    · have := hin t ht
      have := hdeg t
      have hs := deg_split (H₀ := H₀) (T := T) t
      simp only [e, ht, true_and, ↓reduceIte]
      split_ifs <;> omega
    · simp [e, ht]
  have s1 := Finset.sum_le_sum (s := Finset.univ) (fun v _ => key1 v)
  have s2 := Finset.sum_le_sum (s := Finset.univ) (fun v _ => key2 v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, double_count] at s1
  have hcount : ({t | t ∈ T ∧ deg H₀ t = 3}.ncard : ℤ) = ∑ v, e v := by
    rw [ncard_eq_sum_ite]; push_cast; rfl
  unfold psi
  linarith
end ErdosPosa
