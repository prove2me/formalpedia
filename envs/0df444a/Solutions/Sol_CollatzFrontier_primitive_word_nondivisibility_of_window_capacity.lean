-- Prove2me | solution 1 for CollatzFrontier.primitive_word_nondivisibility_of_window_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-04T18:09:45.299986+00:00
-- url     : https://prove2.me/submissions/c8a3d923-49ec-422d-a435-8c1077ba22b4

import Mathlib
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Definitions.Def_collatzFrontierWordWindows

set_option autoImplicit false

open CollatzFrontier
open scoped BigOperators

namespace CollatzFrontierAux

/- Self-contained restatement of the realized-cycle window-capacity interface
(the companion headline `CollatzFrontier.least_cycle_window_capacity`), so this
solution does not depend on any other Open platform submission. -/

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

/-- Realized-cycle window-capacity bound (local restatement of the companion headline). -/
theorem least_cycle_window_capacity (m p k L U : ℕ) (hp : 0 < p) (hodd : Odd m)
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

lemma word_constant_append (u v : List ℕ) :
    syracuseAffineConstant (u ++ v) =
      3 ^ v.length * syracuseAffineConstant u + 2 ^ u.sum * syracuseAffineConstant v := by
  induction u with
  | nil => simp [syracuseAffineConstant]
  | cons a u ih =>
      simp only [List.cons_append, syracuseAffineConstant, List.length_append, List.sum_cons]
      rw [ih, pow_add, pow_add]
      ring

lemma word_constant_pos (w : List ℕ) (hw : w ≠ []) : 0 < syracuseAffineConstant w := by
  cases w with
  | nil => contradiction
  | cons a w => simp only [syracuseAffineConstant]; positivity

lemma word_constant_odd (w : List ℕ) (hw : w ≠ [])
    (hpositive : ∀ a ∈ w, 0 < a) : Odd (syracuseAffineConstant w) := by
  cases w with
  | nil => contradiction
  | cons a w =>
      have ha : 0 < a := hpositive a (by simp)
      have htwo : Even ((2 : ℕ) ^ a) := even_two.pow_of_ne_zero (by omega)
      exact (show Odd ((3 : ℕ) ^ w.length) from (by decide : Odd (3 : ℕ)).pow).add_even
        (htwo.mul_right _)

lemma word_gap_odd (w : List ℕ) (hgap : 3 ^ w.length < 2 ^ w.sum) :
    Odd (2 ^ w.sum - 3 ^ w.length) := by
  have hsum : 0 < w.sum := by
    by_contra h; have hz : w.sum = 0 := by omega
    simp [hz] at hgap
  rw [Nat.odd_sub' hgap.le]
  exact iff_of_true ((by decide : Odd (3 : ℕ)).pow) (even_two.pow_of_ne_zero (by omega))

lemma word_rotation_balance (a : ℕ) (w : List ℕ) :
    2 ^ a * syracuseAffineConstant ((a :: w).rotate 1) + 3 ^ (a :: w).length =
      3 * syracuseAffineConstant (a :: w) + 2 ^ (a :: w).sum := by
  simp only [List.rotate_cons_succ, List.rotate_zero, word_constant_append,
    List.sum_cons, List.length_cons, syracuseAffineConstant,
    List.length_nil, pow_zero, mul_zero, add_zero]
  rw [pow_add, pow_succ]
  ring

lemma word_rotation_row (a : ℕ) (w : List ℕ)
    (hgap : 3 ^ (a :: w).length < 2 ^ (a :: w).sum) :
    2 ^ a * syracuseAffineConstant ((a :: w).rotate 1) =
      3 * syracuseAffineConstant (a :: w) + (2 ^ (a :: w).sum - 3 ^ (a :: w).length) := by
  have h := word_rotation_balance a w
  omega

lemma word_rotation_dvd_one (w : List ℕ) (hw : w ≠ [])
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant (w.rotate 1) := by
  cases w with
  | nil => contradiction
  | cons a w =>
      have hrow := word_rotation_row a w hgap
      have hd := dvd_add (dvd_mul_of_dvd_right hdiv 3) (dvd_refl (2 ^ (a :: w).sum - 3 ^ (a :: w).length))
      rw [← hrow] at hd
      exact ((word_gap_odd (a :: w) hgap).coprime_two_right.pow_right a).dvd_of_dvd_mul_left hd

lemma word_rotation_dvd (w : List ℕ) (hw : w ≠ [])
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) (d : ℕ) :
    (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant (w.rotate d) := by
  induction d with
  | zero => simpa using hdiv
  | succ d ih =>
      have hlen : (w.rotate d).length = w.length := List.length_rotate _ _
      have hsum : (w.rotate d).sum = w.sum := (List.rotate_perm _ _).sum_eq
      have hw' : w.rotate d ≠ [] := by simpa using hw
      have hgap' : 3 ^ (w.rotate d).length < 2 ^ (w.rotate d).sum := by simpa only [hlen, hsum] using hgap
      have hdiv' : (2 ^ (w.rotate d).sum - 3 ^ (w.rotate d).length) ∣ syracuseAffineConstant (w.rotate d) := by simpa only [hlen, hsum] using ih
      simpa only [hlen, hsum, List.rotate_rotate] using word_rotation_dvd_one (w.rotate d) hw' hgap' hdiv'

/-- The canonical candidate state for a word with a positive power gap. -/
def wordState (w : List ℕ) : ℕ := syracuseAffineConstant w / (2 ^ w.sum - 3 ^ w.length)

lemma word_state_factor (w : List ℕ)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    (2 ^ w.sum - 3 ^ w.length) * wordState w = syracuseAffineConstant w := by
  exact Nat.mul_div_cancel' hdiv

lemma word_state_pos (w : List ℕ) (hw : w ≠ [])
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    0 < wordState w := by
  have h := word_state_factor w hdiv
  have hp := word_constant_pos w hw
  nlinarith

lemma word_state_odd (w : List ℕ) (hw : w ≠ [])
    (hpositive : ∀ a ∈ w, 0 < a)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    Odd (wordState w) := by
  have h := word_constant_odd w hw hpositive
  rw [← word_state_factor w hdiv] at h
  exact Nat.Odd.of_mul_right h

lemma word_state_row (w : List ℕ) (hw : w ≠ [])
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    2 ^ w.head! * wordState (w.rotate 1) = 3 * wordState w + 1 := by
  have hrot := word_rotation_dvd_one w hw hgap hdiv
  have hc := word_state_factor w hdiv
  have hr := word_state_factor (w.rotate 1)
    (by simpa only [List.length_rotate, (List.rotate_perm w 1).sum_eq] using hrot)
  have hD : 0 < 2 ^ w.sum - 3 ^ w.length := Nat.sub_pos_of_lt hgap
  rw [List.length_rotate, (List.rotate_perm w 1).sum_eq] at hr
  cases w with
  | nil => contradiction
  | cons a w =>
      have hrow := word_rotation_row a w hgap
      simp only [List.head!_cons]
      apply Nat.eq_of_mul_eq_mul_left hD
      calc
        _ = 2 ^ a * ((2 ^ (a :: w).sum - 3 ^ (a :: w).length) * wordState ((a :: w).rotate 1)) := by ring
        _ = _ := by rw [hr, hrow, ← hc]; ring

lemma word_state_step (w : List ℕ) (hw : w ≠ [])
    (hpositive : ∀ a ∈ w, 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    syracuseStep (wordState w) = wordState (w.rotate 1) := by
  have hrot := word_rotation_dvd_one w hw hgap hdiv
  have hodd := word_state_odd (w.rotate 1) (by simpa using hw)
    (by simpa only [List.mem_rotate] using hpositive)
    (by simpa only [List.length_rotate, (List.rotate_perm w 1).sum_eq] using hrot)
  unfold syracuseStep
  rw [← word_state_row w hw hgap hdiv]
  exact Nat.ordCompl_pow_mul_of_not_dvd _ Nat.prime_two (by simpa using hodd.not_two_dvd_nat)

lemma word_state_valuation (w : List ℕ) (hw : w ≠ [])
    (hpositive : ∀ a ∈ w, 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    (3 * wordState w + 1).factorization 2 = w.head! := by
  have hrot := word_rotation_dvd_one w hw hgap hdiv
  have hd : (2 ^ (w.rotate 1).sum - 3 ^ (w.rotate 1).length) ∣ syracuseAffineConstant (w.rotate 1) := by
    simpa only [List.length_rotate, (List.rotate_perm w 1).sum_eq] using hrot
  have hne : w.rotate 1 ≠ [] := by simpa using hw
  have hodd := word_state_odd (w.rotate 1) hne
    (by simpa only [List.mem_rotate] using hpositive) hd
  have hpos := word_state_pos (w.rotate 1) hne hd
  rw [← word_state_row w hw hgap hdiv, Nat.factorization_mul (by positivity) (by omega)]
  change (2 ^ w.head!).factorization 2 + (wordState (w.rotate 1)).factorization 2 = w.head!
  rw [Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, Nat.add_zero]

lemma word_state_iterate (w : List ℕ) (hw : w ≠ [])
    (hpositive : ∀ a ∈ w, 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) (d : ℕ) :
    syracuseStep^[d] (wordState w) = wordState (w.rotate d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Function.iterate_succ_apply', ih]
      have hrot := word_rotation_dvd w hw hgap hdiv d
      have hd : (2 ^ (w.rotate d).sum - 3 ^ (w.rotate d).length) ∣ syracuseAffineConstant (w.rotate d) := by
        simpa only [List.length_rotate, (List.rotate_perm w d).sum_eq] using hrot
      rw [word_state_step (w.rotate d) (by simpa using hw)
        (by simpa only [List.mem_rotate] using hpositive)
        (by simpa only [List.length_rotate, (List.rotate_perm w d).sum_eq] using hgap) hd]
      simp only [List.rotate_rotate]

lemma word_iterate_valuation (w : List ℕ) (hw : w ≠ [])
    (hpositive : ∀ a ∈ w, 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) (d : ℕ) :
    (3 * syracuseStep^[d] (wordState w) + 1).factorization 2 = (w.rotate d).head! := by
  rw [word_state_iterate w hw hpositive hgap hdiv d]
  apply word_state_valuation (w.rotate d) (by simpa using hw)
    (by simpa only [List.mem_rotate] using hpositive)
    (by simpa only [List.length_rotate, (List.rotate_perm w d).sum_eq] using hgap)
  simpa only [List.length_rotate, (List.rotate_perm w d).sum_eq]
    using word_rotation_dvd w hw hgap hdiv d

lemma word_head_rotate (w : List ℕ) (d : ℕ) (hd : d < w.length) :
    (w.rotate d).head! = w[d] := by
  rw [List.head!_eq_head?_getD, List.head?_rotate hd, List.getElem?_eq_getElem hd]
  rfl

lemma word_state_injective_fixed_length (u v : List ℕ) (hlen : u.length = v.length)
    (hu : u ≠ []) (hv : v ≠ [])
    (hpu : ∀ a ∈ u, 0 < a) (hpv : ∀ a ∈ v, 0 < a)
    (hgu : 3 ^ u.length < 2 ^ u.sum) (hgv : 3 ^ v.length < 2 ^ v.sum)
    (hdu : (2 ^ u.sum - 3 ^ u.length) ∣ syracuseAffineConstant u)
    (hdv : (2 ^ v.sum - 3 ^ v.length) ∣ syracuseAffineConstant v)
    (heq : wordState u = wordState v) : u = v := by
  apply List.ext_getElem hlen
  intro i hi hi'
  rw [← word_head_rotate u i hi, ← word_head_rotate v i hi',
    ← word_iterate_valuation u hu hpu hgu hdu,
    ← word_iterate_valuation v hv hpv hgv hdv, heq]

lemma word_state_least_period (w : List ℕ) (hw : w ≠ [])
    (hpositive : ∀ a ∈ w, 0 < a)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w)
    (hprimitive : ∀ d, 0 < d → d < w.length → w.rotate d ≠ w) :
    syracuseStep^[w.length] (wordState w) = wordState w ∧
      ∀ d, 0 < d → d < w.length → syracuseStep^[d] (wordState w) ≠ wordState w := by
  constructor
  · rw [word_state_iterate w hw hpositive hgap hdiv, List.rotate_length]
  · intro d hd hdlt heq
    rw [word_state_iterate w hw hpositive hgap hdiv] at heq
    apply hprimitive d hd hdlt
    exact word_state_injective_fixed_length (w.rotate d) w (List.length_rotate _ _)
      (by simpa using hw) hw (by simpa only [List.mem_rotate] using hpositive) hpositive
      (by simpa only [List.length_rotate, (List.rotate_perm w d).sum_eq] using hgap) hgap
      (by simpa only [List.length_rotate, (List.rotate_perm w d).sum_eq]
        using word_rotation_dvd w hw hgap hdiv d) hdiv heq

/-- Word-specific complexity obstruction after canonical realization, assembled as a
reduction via the already-posed realized-cycle theorem `least_cycle_window_capacity`. -/
theorem primitive_word_window_capacity (w : List ℕ) (k L U : ℕ)
    (hw : w ≠ []) (hpositive : ∀ a ∈ w, 0 < a)
    (hprimitive : ∀ d, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hbounds : ∀ d < w.length,
      L * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d) ∧
      syracuseAffineConstant (w.rotate d) ≤ U * (2 ^ w.sum - 3 ^ w.length))
    (hdiv : (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) :
    w.length ≤ wordWindowCount w k * ((U - L) / (2 * 3 ^ k) + 1) := by
  have hp : 0 < w.length := List.length_pos_iff.mpr hw
  have hodd := word_state_odd w hw hpositive hdiv
  obtain ⟨hcyc, hmin⟩ := word_state_least_period w hw hpositive hgap hdiv hprimitive
  have hstatebounds : ∀ d < w.length,
      L ≤ syracuseStep^[d] (wordState w) ∧ syracuseStep^[d] (wordState w) ≤ U := by
    intro d hd
    rw [word_state_iterate w hw hpositive hgap hdiv]
    have hr := word_rotation_dvd w hw hgap hdiv d
    have hf := word_state_factor (w.rotate d)
      (by simpa only [List.length_rotate, (List.rotate_perm w d).sum_eq] using hr)
    rw [List.length_rotate, (List.rotate_perm w d).sum_eq] at hf
    have hb := hbounds d hd
    have hD : 0 < 2 ^ w.sum - 3 ^ w.length := Nat.sub_pos_of_lt hgap
    constructor <;> nlinarith
  have hc := least_cycle_window_capacity (wordState w) w.length k L U hp hodd hcyc hmin hstatebounds
  have hlabels : (fun i : Fin w.length => orbitValuationWindow (wordState w) k i.val) =
      (fun i : Fin w.length => wordValuationWindow w k i.val) := by
    funext i j
    exact word_iterate_valuation w hw hpositive hgap hdiv (i.val + j.val)
  -- Fallback (reviewer-suggested, not applied unless the verifier reports a
  -- decidability-instance mismatch between the `Finset.image` built here and
  -- `wordWindowCount`'s own elaboration in the def module's smaller import context):
  --   simpa only [wordWindowCount] using hlabels ▸ hc
  -- or:
  --   unfold wordWindowCount; convert hc using 3; exact hlabels.symm
  rw [hlabels] at hc
  exact hc

end CollatzFrontierAux

open CollatzFrontierAux

/-- Failure of the word-dependent window-capacity bound excludes canonical divisibility:
a primitive word whose cyclic windows are too few, and whose rotated affine constants all
sit inside one short multiple-of-`D` interval, cannot be the valuation word of a Syracuse
cycle, regardless of what that cycle's actual states would be. -/
theorem solution (w : List ℕ) (k L U : ℕ)
    (hw : w ≠ []) (hpositive : ∀ a ∈ w, 0 < a)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hbounds : ∀ d : ℕ, d < w.length →
      L * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d) ∧
      syracuseAffineConstant (w.rotate d) ≤ U * (2 ^ w.sum - 3 ^ w.length))
    (hcapacity : wordWindowCount w k * ((U - L) / (2 * 3 ^ k) + 1) < w.length) :
    ¬ (2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by
  intro hdiv
  exact (not_le_of_gt hcapacity)
    (primitive_word_window_capacity w k L U hw hpositive hprimitive hgap hbounds hdiv)

#print axioms solution
