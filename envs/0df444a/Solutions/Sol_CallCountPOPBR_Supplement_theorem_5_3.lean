-- Prove2me | solution 1 for CallCountPOPBR.Supplement.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:26:45.083647+00:00
-- url     : https://prove2.me/submissions/c911e9ef-ece5-4c7a-9197-caa5e4027eb7

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_DecSpec
import Definitions.Def_CallCountPOPBR_Supplement_sumset

set_option autoImplicit false

namespace CC53Aux
open CallCountPOPBR.Supplement

lemma count_eq (s : DecSpec) (n : ℕ) :
    s.count n = 1 + ((s.calls n).map s.count).sum := by
  rw [DecSpec.count]
  congr 2
  conv_rhs => rw [← List.attach_map_subtype_val (s.calls n), List.map_map]
  rfl

lemma calls_zero (s : DecSpec) : s.calls 0 = [] := by
  rcases h : s.calls 0 with _ | ⟨k, l⟩
  · rfl
  · exact absurd (s.dec 0 k (by rw [h]; exact List.mem_cons_self)) (Nat.not_lt_zero k)

lemma count_cast (s : DecSpec) (n : ℕ) :
    ((s.count n : ℕ) : ℤ) = 1 + ((s.calls n).map (fun k => (s.count k : ℤ))).sum := by
  rw [count_eq]; push_cast; rw [List.map_map]; rfl

lemma necessary (c : ℕ → ℤ) (s : DecSpec) (hs : ∀ n, c n = (s.count n : ℤ)) :
    c 0 = 1 ∧ ∀ n, 1 ≤ n → c n - 1 = ((s.calls n).map c).sum := by
  refine ⟨by rw [hs, count_cast, calls_zero]; rfl, fun n _ => ?_⟩
  rw [hs, count_cast, List.map_congr_left (fun k _ => (hs k).symm)]
  ring

lemma realize (c : ℕ → ℤ) (s : DecSpec) (h0 : c 0 = 1)
    (hrec : ∀ n, 1 ≤ n → c n - 1 = ((s.calls n).map c).sum) : ∀ n, c n = (s.count n : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [h0, count_cast, calls_zero]; rfl
    · rw [count_cast, List.map_congr_left (fun k hk => (ih k (s.dec n k hk)).symm)]
      have := hrec n hn
      linarith

def mkSpec (r : ℕ → List ℕ) (hr : ∀ n, 1 ≤ n → ∀ k ∈ r n, k < n) : DecSpec where
  calls n := Nat.casesOn (motive := fun _ => List ℕ) n [] (fun m => r (m + 1))
  dec n k hk := by
    cases n with
    | zero => simp at hk
    | succ m => exact hr (m + 1) (by omega) k hk

end CC53Aux

open CallCountPOPBR.Supplement in
theorem solution (b : ℕ) (c : ℕ → ℤ) :
    ((∃ s : DecSpec, (∀ n, (s.calls n).length ≤ b) ∧ ∀ n, c n = (s.count n : ℤ)) ↔
      (c 0 = 1 ∧ ∀ n, 1 ≤ n → c n - 1 ∈ ⋃ (j : ℕ) (_ : j ≤ b), sumset c n j)) ∧
    ((∃ s : DecSpec, Computable s.calls ∧ (∀ n, (s.calls n).length ≤ b) ∧
        ∀ n, c n = (s.count n : ℤ)) ↔
      (c 0 = 1 ∧ ∃ r : ℕ → List ℕ, Computable r ∧ ∀ n, 1 ≤ n →
        (r n).length ≤ b ∧ (∀ k ∈ r n, k < n) ∧ c n - 1 = ((r n).map c).sum)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨s, hb, hs⟩
    obtain ⟨h0, hrec⟩ := CC53Aux.necessary c s hs
    refine ⟨h0, fun n hn => ?_⟩
    simp only [Set.mem_iUnion]
    exact ⟨(s.calls n).length, hb n, s.calls n, rfl, s.dec n, hrec n hn⟩
  · rintro ⟨h0, hmem⟩
    have hex : ∀ n, ∃ l : List ℕ, l.length ≤ b ∧ (∀ k ∈ l, k < n) ∧
        (1 ≤ n → c n - 1 = (l.map c).sum) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ⟨[], by simp, by simp, fun h => absurd h (by omega)⟩
      · have := hmem n hn
        simp only [Set.mem_iUnion] at this
        obtain ⟨j, hj, l, hl, hlt, hsum⟩ := this
        exact ⟨l, hl ▸ hj, hlt, fun _ => hsum⟩
    choose L hL using hex
    let s : DecSpec := { calls := L, dec := fun n => (hL n).2.1 }
    exact ⟨s, fun n => (hL n).1, CC53Aux.realize c s h0 (fun n hn => (hL n).2.2 hn)⟩
  · rintro ⟨s, hcomp, hb, hs⟩
    obtain ⟨h0, hrec⟩ := CC53Aux.necessary c s hs
    exact ⟨h0, s.calls, hcomp, fun n hn => ⟨hb n, s.dec n, hrec n hn⟩⟩
  · rintro ⟨h0, r, hr, hprop⟩
    let s := CC53Aux.mkSpec r (fun n hn => (hprop n hn).2.1)
    have hcalls : ∀ n, 1 ≤ n → s.calls n = r n := by
      intro n hn
      cases n with
      | zero => omega
      | succ m => rfl
    refine ⟨s, ?_, ?_, ?_⟩
    · exact Computable.nat_casesOn Computable.id (Computable.const [])
        ((hr.comp (Computable.succ.comp Computable.snd)).to₂)
    · intro n
      cases n with
      | zero => show ([] : List ℕ).length ≤ b; simp
      | succ m => rw [hcalls (m + 1) (by omega)]; exact (hprop (m + 1) (by omega)).1
    · exact CC53Aux.realize c s h0 (fun n hn => by rw [hcalls n hn]; exact (hprop n hn).2.2)
