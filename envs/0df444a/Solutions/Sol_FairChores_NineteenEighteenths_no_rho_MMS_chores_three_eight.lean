-- Prove2me | solution 1 for FairChores.NineteenEighteenths.no_rho_MMS_chores_three_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:33:19.08803+00:00
-- url     : https://prove2.me/submissions/af8d36ea-b898-4503-ac69-037377579120

import Mathlib
import Definitions.Def_RequestProject_ChoresExamples
import Definitions.Def_RequestProject_ChoresMMSPartition
import Definitions.Def_RequestProject_FeigeNorkinChores
import Definitions.Def_RequestProject_NineteenEighteenths
import Theorems.Thm_FairChores_NineteenEighteenths_MMS_agent_zero
import Theorems.Thm_FairChores_NineteenEighteenths_MMS_agent_one
import Theorems.Thm_FairChores_NineteenEighteenths_MMS_agent_two
import Theorems.Thm_FairChores_NineteenEighteenths_lamOf_ge_two
import Theorems.Thm_FairChores_NineteenEighteenths_lamOf_key
import Theorems.Thm_FairChores_FeigeNorkinChores_feigeNorkinChores_cover
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
open FairChores.NineteenEighteenths
open FeigeNorkinChores
namespace FairChores.NineteenEighteenths
theorem _root_.solution {rho : ℝ} (hrho : rho < 19/18) :
    ∀ o : Outcome (Fin 8) 3, o.Valid (instP (lamOf rho)) →
      ∃ i, rho * MMS 3 (instC (lamOf rho) i) (instP (lamOf rho))
        < cost (instC (lamOf rho) i) o i := by
  classical
  set lam := lamOf rho with hlamdef
  have hlam2 : 2 ≤ lam := lamOf_ge_two hrho
  have hlam0 : (0:ℝ) ≤ lam := by linarith
  have hkey : 720 * rho < lam * (380 - 360 * rho) := lamOf_key hrho
  have hrho380 : 360 * rho < 380 := by linarith
  intro o hvalid
  by_contra hcon
  push_neg at hcon
  obtain ⟨hdo, hdk, hcov, hpay0, hbudget⟩ := hvalid
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  rw [MMS_agent_zero hlam2] at h0
  rw [MMS_agent_one hlam2] at h1
  rw [MMS_agent_two hlam0] at h2
  -- the three costs, spelled out
  have hc0 : (∑ t ∈ o.kept 0, (fcR t : ℝ)) + o.pay 0 ≤ rho * 360 := by
    simpa [cost, instC] using h0
  have hc1 : (∑ t ∈ o.kept 1, (fcC t : ℝ)) + o.pay 1 ≤ rho * 360 := by
    simpa [cost, instC] using h1
  have hc2 : (∑ t ∈ o.kept 2, instP lam t) + o.pay 2 ≤ rho * (360 * lam) := by
    simpa [cost, instC] using h2
  -- agent `0` and agent `1` keep bundles costing less than `380`
  have hR : (∑ t ∈ o.kept 0, (fcR t : ℝ)) < 380 := by
    have := hpay0 0
    linarith
  have hC : (∑ t ∈ o.kept 1, (fcC t : ℝ)) < 380 := by
    have := hpay0 1
    linarith
  -- the chores that are outsourced or performed by agent `2` are cheap for agent `2`
  set B2 : Finset (Fin 8) := o.outsourced ∪ o.kept 2 with hB2
  have hdisj2 : Disjoint o.outsourced (o.kept 2) := hdo 2
  have hsplit : (∑ t ∈ B2, instP lam t)
      = (∑ t ∈ o.outsourced, instP lam t) + ∑ t ∈ o.kept 2, instP lam t := by
    rw [hB2, Finset.sum_union hdisj2]
  have hpay01 : o.pay 0 ≤ rho * 360 ∧ o.pay 1 ≤ rho * 360 := by
    constructor
    · have : (0:ℝ) ≤ ∑ t ∈ o.kept 0, (fcR t : ℝ) := Finset.sum_nonneg (fun t _ => by positivity)
      linarith
    · have : (0:ℝ) ≤ ∑ t ∈ o.kept 1, (fcC t : ℝ) := Finset.sum_nonneg (fun t _ => by positivity)
      linarith
  have hsum3 : ∑ j, o.pay j = o.pay 0 + o.pay 1 + o.pay 2 := by
    rw [Fin.sum_univ_three]
  have houts : (∑ t ∈ o.outsourced, instP lam t) ≤ o.pay 0 + o.pay 1 + o.pay 2 := by
    rw [← hsum3]; exact hbudget
  have hB2bound : (∑ t ∈ B2, instP lam t) ≤ 720 * rho + rho * (360 * lam) := by
    rw [hsplit]
    linarith [hpay01.1, hpay01.2, hc2]
  have hB2eq : (∑ t ∈ B2, instP lam t) = lam * ∑ t ∈ B2, (fcU t : ℝ) := by
    rw [Finset.mul_sum]; rfl
  have hU : (∑ t ∈ B2, (fcU t : ℝ)) < 380 := by
    have hlt : lam * ∑ t ∈ B2, (fcU t : ℝ) < lam * 380 := by
      rw [← hB2eq]
      nlinarith [hB2bound, hkey]
    have hlampos : (0:ℝ) < lam := by linarith
    exact lt_of_mul_lt_mul_left hlt hlampos.le
  -- every chore is kept by agent `0`, kept by agent `1`, or in `B2`
  have hcover : ∀ t : Fin 8,
      t ∈ (![o.kept 0, o.kept 1, B2] : Fin 3 → Finset (Fin 8)) 0 ∨
      t ∈ (![o.kept 0, o.kept 1, B2] : Fin 3 → Finset (Fin 8)) 1 ∨
      t ∈ (![o.kept 0, o.kept 1, B2] : Fin 3 → Finset (Fin 8)) 2 := by
    intro t
    have hmem : t ∈ o.outsourced ∪ Finset.univ.biUnion o.kept := by
      rw [hcov]; exact Finset.mem_univ t
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rcases Finset.mem_union.mp hmem with h | h
    · exact Or.inr (Or.inr (Finset.mem_union_left _ h))
    · obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp h
      have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
      rcases hk3 with rfl | rfl | rfl
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr (Finset.mem_union_right _ hk))
  obtain ⟨i, hi⟩ := feigeNorkinChores_cover ![o.kept 0, o.kept 1, B2] hcover
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi3 with rfl | rfl | rfl
  · simp only [fcW, Matrix.cons_val_zero] at hi
    have : (380 : ℝ) ≤ ∑ t ∈ o.kept 0, (fcR t : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hi
    linarith
  · simp only [fcW, Matrix.cons_val_one] at hi
    have : (380 : ℝ) ≤ ∑ t ∈ o.kept 1, (fcC t : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hi
    linarith
  · simp only [fcW, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hi
    have : (380 : ℝ) ≤ ∑ t ∈ B2, (fcU t : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hi
    linarith
end FairChores.NineteenEighteenths
