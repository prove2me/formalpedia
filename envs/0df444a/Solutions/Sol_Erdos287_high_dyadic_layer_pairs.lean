-- Prove2me | solution 1 for Erdos287.high_dyadic_layer_pairs
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:24:28.227048+00:00
-- url     : https://prove2.me/submissions/264098ad-a3cc-4bb9-a5ed-21a64fb13e27

import Mathlib
import Theorems.Thm_Erdos287_cofactor_cut_congruence
import Theorems.Thm_Erdos287_high_cofactor_exclusions

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A dense representation can use a dyadic layer above one tenth of its
maximum only in specific pairs of odd cofactors. -/
theorem solution (D : Finset ℕ) (m M e : ℕ) (hm : 0 < m) (he : 1 ≤ e)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hratio : M < 3 * m) (hupper : M < 10 * 2 ^ e) :
    let q := 2 ^ e
    let H := D.filter (fun n => q ∣ n)
    H = ∅ ∨ ∃ a ∈ ({3, 5, 7, 9} : Finset ℕ), ∃ b ∈ ({3, 5, 7, 9} : Finset ℕ),
      a < b ∧ (a ≠ 3 ∨ b ≠ 9) ∧ H = {a * q, b * q} := by
  let q : ℕ := 2 ^ e
  let H := D.filter (fun n => q ∣ n)
  let S : Finset ℕ := {3, 5, 7, 9}
  change
    H = ∅ ∨ ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (a ≠ 3 ∨ b ≠ 9) ∧ H = {a * q, b * q}
  change M < 10 * q at hupper
  have hq : 0 < q := pow_pos (by decide) _
  have hbounds (n : ℕ) (hn : n ∈ D) : m ≤ n ∧ n ≤ M := mem_Icc.mp (hD hn)
  have hpos (n : ℕ) (hn : n ∈ D) : 0 < n := hm.trans_le (hbounds n hn).1
  have hbase := (Erdos287.high_cofactor_exclusions D m M hm hD hsum).1
  have hdouble : D.filter (fun n => (2 * q) ∣ n) = ∅ := by
    have hpow : (2 : ℕ) ^ (e + 1) = 2 * q := pow_succ' _ _
    simpa only [hpow] using hbase (e + 1) (by omega) hratio (by rw [hpow]; omega)
  have hqnot : q ∉ D := by
    intro h
    have hM : M < 5 * q := by have := (hbounds q h).1; omega
    have hh : q ∈ H := mem_filter.mpr ⟨h, dvd_refl _⟩
    have heq : H = ∅ := hbase e he hratio hM
    simpa only [heq, notMem_empty] using hh
  have hcoef (n : ℕ) (hn : n ∈ H) : n / q ∈ S := by
    obtain ⟨hnD, hd⟩ := mem_filter.mp hn
    let c := n / q
    have hc : c * q = n := Nat.div_mul_cancel hd
    have hcpos : 0 < c := Nat.div_pos (Nat.le_of_dvd (hpos n hnD) hd) hq
    have hcmax : c < 10 := Nat.lt_of_mul_lt_mul_right (by
      rw [hc]
      exact (hbounds n hnD).2.trans_lt hupper)
    have hcodd : ¬ 2 ∣ c := by
      rintro ⟨t, ht⟩
      have hd' : 2 * q ∣ n := ⟨t, by rw [← hc, ht]; ring⟩
      have hh : n ∈ D.filter (fun x => (2 * q) ∣ x) := mem_filter.mpr ⟨hnD, hd'⟩
      simpa only [hdouble, notMem_empty] using hh
    have hcon : c ≠ 1 := by
      intro hc1
      have hqn : q = n := by simpa only [hc1, one_mul] using hc
      exact hqnot (hqn.symm ▸ hnD)
    have hcmod : c % 2 ≠ 0 := fun h => hcodd (Nat.dvd_of_mod_eq_zero h)
    have hs : c = 3 ∨ c = 5 ∨ c = 7 ∨ c = 9 := by omega
    change c ∈ S
    simpa [S] using hs
  let T := H.image (fun n => n / q)
  have hTS : T ⊆ S := by
    intro c hc
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hc
    exact hcoef n hn
  have hmap : T.image (fun c => c * q) = H := by
    rw [show T = H.image (fun n => n / q) from rfl, image_image]
    exact image_congr (fun n hn => Nat.div_mul_cancel (mem_filter.mp hn).2) |>.trans image_id
  have hnot39 : ¬ (3 ∈ T ∧ 9 ∈ T) := by
    intro ⟨h3, h9⟩
    have h3n : 3 * q ∈ H := hmap ▸ mem_image.mpr ⟨3, h3, rfl⟩
    have h9n : 9 * q ∈ H := hmap ▸ mem_image.mpr ⟨9, h9, rfl⟩
    have hl := (hbounds _ (mem_filter.mp h3n).1).1
    have hu := (hbounds _ (mem_filter.mp h9n).1).2
    omega
  have hLc : ∀ c ∈ S, c ∣ 315 := by decide
  have hres := Erdos287.cofactor_cut_congruence D 2 e 315 0 (by decide) he hpos hsum
    (fun n hn hd => hLc _ (hcoef n (mem_filter.mpr ⟨hn, hd⟩))) (by decide)
  change 2 ∣ ∑ n ∈ H, 315 / (n / q) at hres
  have hinj : Set.InjOn (fun n => n / q) (↑H : Set ℕ) := by
    intro x hx y hy h
    change x / q = y / q at h
    have hx' := Nat.div_mul_cancel (mem_filter.mp (show x ∈ H from hx)).2
    have hy' := Nat.div_mul_cancel (mem_filter.mp (show y ∈ H from hy)).2
    exact hx'.symm.trans ((congrArg (· * q) h).trans hy')
  have hres' : 2 ∣ ∑ c ∈ T, 315 / c := by
    rwa [show T = H.image (fun n => n / q) from rfl, sum_image (fun _ hx _ hy h => hinj hx hy h)]
  have hcheck : ∀ U ∈ S.powerset, ¬ (3 ∈ U ∧ 9 ∈ U) → (2 ∣ ∑ c ∈ U, 315 / c) →
      U = ∅ ∨ ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (a ≠ 3 ∨ b ≠ 9) ∧ U = {a, b} := by decide
  rcases hcheck T (mem_powerset.mpr hTS) hnot39 hres' with h | ⟨a, ha, b, hb, hab, hn, h⟩
  · exact Or.inl (by rw [← hmap, h, image_empty])
  · exact Or.inr ⟨a, ha, b, hb, hab, hn, by rw [← hmap, h, image_insert, image_singleton]⟩

