-- Prove2me | solution 1 for Erdos195.zero_one_odd_finite_extension
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T12:04:20.089979+00:00
-- url     : https://prove2.me/submissions/74506e0f-c560-495d-b274-ecfad1d3ad16

import Definitions.Def_Erdos195_tree
import Theorems.Thm_Erdos195_treeLt_safe_iff
import Theorems.Thm_Erdos195_specified_first_safe_order
import Theorems.Thm_Erdos195_safe_parity_decomp
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Erdos195

private lemma odd_lift (x : ℤ) : (1 + 2 * x) % 2 = 1 := by omega

private lemma lift_inj {x y : ℤ} (h : 1 + 2 * x = 1 + 2 * y) : x = y := by omega

private lemma recover_half {z : ℤ} (hz : z % 2 = 1) : 1 + 2 * ((z - 1) / 2) = z := by
  have hsplit : (z - 1) % 2 + (z - 1) / 2 * 2 = z - 1 := Int.emod_add_ediv_mul (z - 1) 2
  have hmod : (z - 1) % 2 = 0 := by omega
  omega

private lemma half_of_lift (x : ℤ) : (1 + 2 * x) / 2 = x := by
  have hsplit : (1 + 2 * x) % 2 + (1 + 2 * x) / 2 * 2 = 1 + 2 * x :=
    Int.emod_add_ediv_mul (1 + 2 * x) 2
  have hmod : (1 + 2 * x) % 2 = 1 := odd_lift x
  omega

private lemma safe_singleton (θ : ℕ → ℤ → Bool) (a : ℤ) : Safe (treeLt θ) [a] := by
  rw [treeLt_safe_iff]
  constructor
  · intro x y hx hy hmid hord1 hord2
    have hx' : x = a := by simpa using hx
    have hy' : y = a := by simpa using hy
    subst hx'; subst hy'
    exact (lt_irrefl _ hord1).elim
  · intro x y hx hy hord h2 h3
    have hx' : x = a := by simpa using hx
    have hy' : y = a := by simpa using hy
    subst hx'; subst hy'
    exact (lt_irrefl _ hord).elim

private lemma filter_even_map_lift (A : List ℤ) :
    (A.map (fun t => 1 + 2 * t)).filter (fun x => decide (x % 2 = 0)) = [] := by
  induction A with
  | nil => simp
  | cons t ts ih =>
    have ht : decide (((1 + 2 * t : ℤ) % 2) = 0) = false := by
      have h := odd_lift t
      simp [h]
    simp [List.filter_cons, List.map_cons, ht, ih]

private lemma filter_odd_map_lift (A : List ℤ) :
    (A.map (fun t => 1 + 2 * t)).filter (fun x => decide (x % 2 = 1)) =
      A.map (fun t => 1 + 2 * t) := by
  induction A with
  | nil => simp
  | cons t ts ih =>
    have ht : decide (((1 + 2 * t : ℤ) % 2) = 1) = true := by
      have h := odd_lift t
      simp [h]
    simp [List.filter_cons, List.map_cons, ht, ih]

private lemma filter_even_cons_odds (A : List ℤ) :
    ((0 :: A.map (fun t => 1 + 2 * t)).filter (fun x => decide (x % 2 = 0))) = [0] := by
  have h0 : decide ((0 : ℤ) % 2 = 0) = true := by decide
  simp [List.filter_cons, h0, filter_even_map_lift]

private lemma filter_odd_cons_odds (A : List ℤ) :
    ((0 :: A.map (fun t => 1 + 2 * t)).filter (fun x => decide (x % 2 = 1))) =
      A.map (fun t => 1 + 2 * t) := by
  have h0 : decide ((0 : ℤ) % 2 = 1) = false := by decide
  simp [List.filter_cons, h0, filter_odd_map_lift]

private lemma map_half_lift (A : List ℤ) :
    (A.map (fun t => 1 + 2 * t)).map (fun z => z / 2) = A := by
  induction A with
  | nil => simp
  | cons t ts ih =>
    simp [half_of_lift, ih]

private lemma only_even_is_zero {A : List ℤ} {z : ℤ}
    (hz : z ∈ 0 :: A.map (fun t => 1 + 2 * t)) (he : z % 2 = 0) : z = 0 := by
  rcases List.mem_cons.mp hz with rfl | hz
  · rfl
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hz
    have : (1 + 2 * x) % 2 = 1 := odd_lift x
    omega

/-- Glue a safe word `A` to the word beginning with `0` followed by the odd lift of `A`. -/
private lemma exists_safe_glue_zero_odd {A : List ℤ}
    (hA : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) A) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (0 :: A.map (fun t => 1 + 2 * t)) := by
  obtain ⟨θ', hS⟩ := hA
  let Q : List ℤ := 0 :: A.map (fun t => 1 + 2 * t)
  let θ : ℕ → ℤ → Bool := fun k r =>
    if k = 0 then true else θ' (k - 1) ((r - 1) / 2)
  have hshift : (fun k r => θ (k + 1) (2 * r + 1)) = θ' := by
    funext k r
    have hk : k + 1 ≠ 0 := Nat.succ_ne_zero k
    have hr : ((2 * r + 1 : ℤ) - 1) / 2 = r := by omega
    simp [θ, hk, hr]
  have hQeven :
      Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
        ((Q.filter (fun x => decide (x % 2 = 0))).map (· / 2)) := by
    have hf : Q.filter (fun x => decide (x % 2 = 0)) = [0] := filter_even_cons_odds A
    rw [hf]
    simpa using safe_singleton (fun k r => θ (k + 1) (2 * r)) 0
  have hQodd :
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
        ((Q.filter (fun x => decide (x % 2 = 1))).map (· / 2)) := by
    have hf : Q.filter (fun x => decide (x % 2 = 1)) = A.map (fun t => 1 + 2 * t) :=
      filter_odd_cons_odds A
    rw [hf, map_half_lift, hshift]
    exact hS
  have hroot : ∀ a b : ℤ, a ∈ Q → b ∈ Q → (b - a) % 2 = 1 → Q.idxOf a < Q.idxOf b →
      (2 * b - a ∈ Q → Q.idxOf b < Q.idxOf (2 * b - a) →
        3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
      (2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q → (θ 0 0 = true ↔ b % 2 = 1)) := by
    intro a b ha hb hdiff hord
    constructor
    · intro h2mem h2ord
      exfalso
      -- Odd difference: the two ends have opposite parity to the middle? a and b have opposite parity.
      have hb01 : b % 2 = 0 ∨ b % 2 = 1 := Int.emod_two_eq b
      rcases hb01 with hbe | hbo
      · -- b even ⇒ b = 0, but then a occurs before 0, impossible
        have hb0 : b = 0 := only_even_is_zero hb hbe
        subst hb0
        have haodd : a % 2 = 1 := by omega
        have ha0 : a ≠ 0 := by omega
        have hidx : Q.idxOf a = (A.map (fun t => 1 + 2 * t)).idxOf a + 1 :=
          List.idxOf_cons_ne _ ha0.symm
        have : Q.idxOf 0 = 0 := rfl
        omega
      · -- b odd ⇒ a even ⇒ a = 0 ⇒ 2b-a = 2b even ⇒ 2b = 0 ⇒ b = 0, contradiction
        have hae : a % 2 = 0 := by omega
        have ha0 : a = 0 := only_even_is_zero ha hae
        subst ha0
        have h2e : (2 * b : ℤ) % 2 = 0 := by omega
        have h2Q : (2 * b : ℤ) ∈ Q := by simpa using h2mem
        have h20 : 2 * b = 0 := only_even_is_zero h2Q h2e
        omega
    · intro _ _
      have hb01 : b % 2 = 0 ∨ b % 2 = 1 := Int.emod_two_eq b
      have hbodd : b % 2 = 1 := by
        rcases hb01 with hbe | hbo
        · have hb0 : b = 0 := only_even_is_zero hb hbe
          subst hb0
          have haodd : a % 2 = 1 := by omega
          have ha0 : a ≠ 0 := by omega
          have hidx : Q.idxOf a = (A.map (fun t => 1 + 2 * t)).idxOf a + 1 :=
            List.idxOf_cons_ne _ ha0.symm
          have : Q.idxOf 0 = 0 := rfl
          omega
        · exact hbo
      simp [θ, hbodd]
  exact ⟨θ, (safe_parity_decomp θ Q).mpr ⟨hQeven, hQodd, hroot⟩⟩

theorem zero_one_odd_finite_extension (F : Finset ℤ) (hF : ∀ z ∈ F, z % 2 = 1) :
    ∃ Q : List ℤ, Q.Nodup ∧ (∃ T : List ℤ, Q = 0 :: 1 :: T) ∧ (∀ z ∈ F, z ∈ Q) ∧
      (∀ z ∈ Q, z % 2 = 0 → z = 0) ∧
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q := by
  classical
  let H : Finset ℤ := insert 0 (F.image fun z => (z - 1) / 2)
  have h0H : (0 : ℤ) ∈ H := Finset.mem_insert_self _ _
  obtain ⟨A, hndA, hmemA, hheadA, hsafeA⟩ := specified_first_safe_order H 0 h0H
  let Odd := A.map (fun t => 1 + 2 * t)
  let Q := 0 :: Odd
  have hnd : Q.Nodup := by
    refine (List.nodup_cons).2 ⟨?_, ?_⟩
    · intro h
      obtain ⟨x, hx, heq⟩ := List.mem_map.mp h
      have : (1 + 2 * x) % 2 = 1 := odd_lift x
      omega
    · exact hndA.map (fun {x y} h => lift_inj h)
  have hpref : ∃ T : List ℤ, Q = 0 :: 1 :: T := by
    cases A with
    | nil => cases hheadA
    | cons a t =>
      simp [List.head?] at hheadA
      subst hheadA
      refine ⟨t.map (fun u => 1 + 2 * u), ?_⟩
      simp [Q, Odd]
  have hFmem : ∀ z ∈ F, z ∈ Q := by
    intro z hz
    have hzodd := hF z hz
    have hxH : (z - 1) / 2 ∈ H :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have hxA : (z - 1) / 2 ∈ A := (hmemA _).2 hxH
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(z - 1) / 2, hxA, recover_half hzodd⟩)
  have heven : ∀ z ∈ Q, z % 2 = 0 → z = 0 := fun z hz he => only_even_is_zero hz he
  exact ⟨Q, hnd, hpref, hFmem, heven, exists_safe_glue_zero_odd hsafeA⟩

end Erdos195

theorem solution (F : Finset ℤ) (hF : ∀ z ∈ F, z % 2 = 1) :
    ∃ Q : List ℤ, Q.Nodup ∧ (∃ T : List ℤ, Q = 0 :: 1 :: T) ∧ (∀ z ∈ F, z ∈ Q) ∧
      (∀ z ∈ Q, z % 2 = 0 → z = 0) ∧
      ∃ θ : ℕ → ℤ → Bool, Erdos195.Safe (Erdos195.treeLt θ) Q :=
  Erdos195.zero_one_odd_finite_extension F hF
