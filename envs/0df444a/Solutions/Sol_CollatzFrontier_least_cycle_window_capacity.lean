-- Prove2me | solution 1 for CollatzFrontier.least_cycle_window_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T18:09:46.187933+00:00
-- url     : https://prove2.me/submissions/0d96654c-7d47-4a19-a511-bf0a398380f1

import Mathlib
import Definitions.Def_syracuseStep
import Definitions.Def_collatzFrontierWordWindows

set_option autoImplicit false

open CollatzFrontier
open scoped BigOperators

namespace CollatzFrontierAux

/-- Every Syracuse step has an odd result, since its argument to `ordCompl` is positive. -/
theorem syracuseStep_odd (n : ℕ) : Odd (syracuseStep n) := by
  apply Nat.odd_iff.mpr
  have hnot : ¬ 2 ∣ syracuseStep n :=
    Nat.not_dvd_ordCompl Nat.prime_two (show 3 * n + 1 ≠ 0 by omega)
  have hne : syracuseStep n % 2 ≠ 0 := by
    intro hzero
    exact hnot (Nat.dvd_of_mod_eq_zero hzero)
  have hlt := Nat.mod_lt (syracuseStep n) (show 0 < 2 by decide)
  omega

theorem syracuse_iterate_odd (n : ℕ) (hn : Odd n) (i : ℕ) :
    Odd (syracuseStep^[i] n) := by
  cases i with
  | zero => exact hn
  | succ i =>
      rw [Function.iterate_succ_apply']
      exact syracuseStep_odd _

/-- Least-period iterates are distinct, using Mathlib's minimal-period API. -/
theorem least_period_iterates_injective (m p : ℕ) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    Function.Injective (fun i : Fin p => syracuseStep^[i.val] m) := by
  have hperiod : Function.IsPeriodicPt syracuseStep p m := hcyc
  have hpos := hperiod.minimalPeriod_pos hp
  have hle := hperiod.minimalPeriod_le hp
  have heq : Function.minimalPeriod syracuseStep m = p := by
    by_contra hne
    have hlt : Function.minimalPeriod syracuseStep m < p := by omega
    exact hmin _ hpos hlt (Function.iterate_minimalPeriod (f := syracuseStep) (x := m))
  intro i j hij
  apply Fin.ext
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (f := syracuseStep) (x := m)
    (by rw [heq]; exact i.isLt) (by rw [heq]; exact j.isLt)).mp hij

/-- Common exact dyadic rows force congruent endpoints modulo a power of three. -/
theorem dyadic_chain_endpoint_modEq (a b c : ℕ → ℕ) (k : ℕ)
    (hb : ∀ j < k, 2 ^ (a j) * b (j + 1) = 3 * b j + 1)
    (hc : ∀ j < k, 2 ^ (a j) * c (j + 1) = 3 * c j + 1) :
    b k ≡ c k [MOD 3 ^ k] := by
  induction k with
  | zero => change b 0 % 1 = c 0 % 1; omega
  | succ k ih =>
      have ht := ih (fun j hj => hb j (by omega)) (fun j hj => hc j (by omega))
      have hmul := (ht.mul_left' 3).add_right 1
      have hmod : 3 * b k + 1 ≡ 3 * c k + 1 [MOD 3 ^ (k + 1)] := by
        simpa [pow_succ, Nat.mul_comm] using hmul
      rw [← hb k (by omega), ← hc k (by omega)] at hmod
      exact Nat.ModEq.cancel_left_of_coprime
        (((by decide : Nat.Coprime 3 2).pow_left (k + 1)).pow_right (a k)) hmod

/-- Rank bound for a finite set whose distinct ordered entries are separated by `M`. -/
theorem spaced_finset_rank_lower (s : Finset ℕ) (M L : ℕ)
    (hlow : ∀ x ∈ s, L ≤ x)
    (hspace : ∀ x ∈ s, ∀ y ∈ s, x < y → x + M ≤ y) :
    ∀ j (hj : j < s.card), L + M * j ≤ s.orderEmbOfFin rfl ⟨j, hj⟩ := by
  intro j
  induction j with
  | zero => intro hj; simpa using hlow _ (s.orderEmbOfFin_mem rfl ⟨0, hj⟩)
  | succ j ih =>
      intro hj
      have hj' : j < s.card := by omega
      have hp := ih hj'
      have hlt := (s.orderEmbOfFin rfl).strictMono
        (show (⟨j, hj'⟩ : Fin s.card) < ⟨j + 1, hj⟩ from by exact_mod_cast Nat.lt_succ_self j)
      have hs := hspace _ (s.orderEmbOfFin_mem rfl ⟨j, hj'⟩)
        _ (s.orderEmbOfFin_mem rfl ⟨j + 1, hj⟩) hlt
      nlinarith

/-- Inclusive interval capacity for one residue class. The empty-set case is included. -/
theorem modEq_finset_interval_capacity (s : Finset ℕ) (M L U : ℕ) (hM : 0 < M)
    (hbounds : ∀ x ∈ s, L ≤ x ∧ x ≤ U)
    (hcongr : ∀ x ∈ s, ∀ y ∈ s, x ≡ y [MOD M]) :
    s.card ≤ (U - L) / M + 1 := by
  by_cases hs : s.Nonempty
  · have hcard : 0 < s.card := Finset.card_pos.mpr hs
    have hlast : s.card - 1 < s.card := by omega
    have hrank := spaced_finset_rank_lower s M L (fun x hx => (hbounds x hx).1)
      (by
        intro x hx y hy hxy
        have hd := (Nat.modEq_iff_dvd' hxy.le).mp (hcongr x hx y hy)
        have hg := Nat.le_of_dvd (Nat.sub_pos_of_lt hxy) hd
        omega) (s.card - 1) hlast
    have hu := (hbounds _ (s.orderEmbOfFin_mem rfl ⟨s.card - 1, hlast⟩)).2
    have hmul : (s.card - 1) * M ≤ U - L := by
      rw [Nat.mul_comm]
      omega
    have hdiv := (Nat.le_div_iff_mul_le hM).2 hmul
    omega
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

/-- Equal labels constrain distinct odd states to at most one class modulo `2*3^k`.
Summing the inclusive capacities bounds the entire finite family. -/
theorem labeled_odd_state_capacity {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (f : ι → ℕ) (label : ι → α) (k L U : ℕ)
    (hinj : Function.Injective f)
    (hodd : ∀ i ∈ s, Odd (f i))
    (hbounds : ∀ i ∈ s, L ≤ f i ∧ f i ≤ U)
    (hlabel : ∀ i ∈ s, ∀ j ∈ s, label i = label j → f i ≡ f j [MOD 3 ^ k]) :
    s.card ≤ (s.image label).card * ((U - L) / (2 * 3 ^ k) + 1) := by
  classical
  have hQ : Nat.Coprime 2 (3 ^ k) := ((by decide : Odd (3 : ℕ)).pow).coprime_two_left
  have hfiber (a : α) : ((s.filter (fun i => label i = a)).card) ≤
      (U - L) / (2 * 3 ^ k) + 1 := by
    let t := (s.filter (fun i => label i = a)).image f
    have hb : ∀ x ∈ t, L ≤ x ∧ x ≤ U := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hbounds i (Finset.mem_filter.mp hi).1
    have hm : ∀ x ∈ t, ∀ y ∈ t, x ≡ y [MOD 2 * 3 ^ k] := by
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨his, hil⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjs, hjl⟩ := Finset.mem_filter.mp hj
      apply (Nat.modEq_and_modEq_iff_modEq_mul hQ).mp
      constructor
      · exact (Nat.odd_iff.mp (hodd i his)).trans (Nat.odd_iff.mp (hodd j hjs)).symm
      · exact hlabel i his j hjs (hil.trans hjl.symm)
    have hc := modEq_finset_interval_capacity t (2 * 3 ^ k) L U (by positivity) hb hm
    simpa [t, Finset.card_image_of_injective _ hinj] using hc
  calc
    _ = ∑ a ∈ s.image label, (s.filter (fun i => label i = a)).card :=
      Finset.card_eq_sum_card_image label s
    _ ≤ ∑ _ ∈ s.image label, ((U - L) / (2 * 3 ^ k) + 1) :=
      Finset.sum_le_sum (fun a _ => hfiber a)
    _ = _ := by simp

lemma equal_orbit_windows_endpoint_modEq (m k i j : ℕ)
    (h : orbitValuationWindow m k i = orbitValuationWindow m k j) :
    syracuseStep^[i + k] m ≡ syracuseStep^[j + k] m [MOD 3 ^ k] := by
  let a := fun d : ℕ => (3 * syracuseStep^[i + d] m + 1).factorization 2
  let b := fun d : ℕ => syracuseStep^[i + d] m
  let c := fun d : ℕ => syracuseStep^[j + d] m
  have hb (d : ℕ) : 2 ^ (a d) * b (d + 1) = 3 * b d + 1 := by
    dsimp [a, b]
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    exact Nat.ordProj_mul_ordCompl_eq_self _ 2
  have hc (d : ℕ) (hd : d < k) : 2 ^ (a d) * c (d + 1) = 3 * c d + 1 := by
    have he := congrFun h ⟨d, hd⟩
    change a d = (3 * c d + 1).factorization 2 at he
    rw [he]
    dsimp [c]
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    exact Nat.ordProj_mul_ordCompl_eq_self _ 2
  exact dyadic_chain_endpoint_modEq a b c k (fun d _ => hb d) hc

end CollatzFrontierAux

open CollatzFrontierAux

/-- A realized least-period orbit needs enough valuation-window labels to house its
shifted endpoints. This is a complexity/range bound, not a bound on period alone. -/
theorem solution (m p k L U : ℕ) (hp : 0 < p) (hodd : Odd m)
    (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ d : ℕ, 0 < d → d < p → syracuseStep^[d] m ≠ m)
    (hbounds : ∀ d : ℕ, d < p → L ≤ syracuseStep^[d] m ∧ syracuseStep^[d] m ≤ U) :
    p ≤ ((Finset.univ : Finset (Fin p)).image
        (fun i : Fin p => orbitValuationWindow m k i.val)).card * ((U - L) / (2 * 3 ^ k) + 1) := by
  have hperiod : Function.IsPeriodicPt syracuseStep p m := hcyc
  have hmem : m ∈ Function.periodicPts syracuseStep := ⟨p, hp, hperiod⟩
  have hcyc' : syracuseStep^[p] (syracuseStep^[k] m) = syracuseStep^[k] m := hperiod.apply_iterate k
  have hmin' : ∀ d, 0 < d → d < p → syracuseStep^[d] (syracuseStep^[k] m) ≠ syracuseStep^[k] m := by
    intro d hd hdp heq
    exact hmin d hd hdp (Function.isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate hmem heq)
  have hi := least_period_iterates_injective (syracuseStep^[k] m) p hp hcyc' hmin'
  have hinj : Function.Injective (fun i : Fin p => syracuseStep^[i.val + k] m) := by
    intro i j hij
    apply hi
    simpa [Function.iterate_add_apply] using hij
  have hball (d : ℕ) : L ≤ syracuseStep^[d] m ∧ syracuseStep^[d] m ≤ U := by
    have hb := hbounds (d % p) (Nat.mod_lt d hp)
    rwa [hperiod.iterate_mod_apply d] at hb
  simpa using labeled_odd_state_capacity (Finset.univ : Finset (Fin p))
    (fun i : Fin p => syracuseStep^[i.val + k] m) (fun i : Fin p => orbitValuationWindow m k i.val)
    k L U hinj
    (fun i _ => syracuse_iterate_odd m hodd (i.val + k)) (fun i _ => hball (i.val + k))
    (fun i _ j _ h => equal_orbit_windows_endpoint_modEq m k i.val j.val h)

#print axioms solution
