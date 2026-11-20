-- Prove2me | solution 1 for EditMulticoloring.Code.explicit_edit_codes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:21:57.847168+00:00
-- url     : https://prove2.me/submissions/41709524-90be-4422-a9c5-aa86fffcc4cc

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Construction
import Definitions.Def_EditMulticoloring_Code_Machine
import Theorems.Thm_EditMulticoloring_Code_ram_programs
import Theorems.Thm_EditMulticoloring_Code_encoder_redundancy
import Theorems.Thm_EditMulticoloring_Code_decoder_correctness

section
set_option autoImplicit false

namespace EditMulticoloring.Dev.ExplicitEdit
open OAI.EditDistortion EditMulticoloring.Code

theorem script_trans {Al : Type} {n m : ℕ} {x y z : List Al}
    (h1 : Script true n x y) (h2 : Script true m y z) : Script true (n + m) x z := by
  induction h1 with
  | nil => rw [Nat.zero_add]; exact h2
  | cons first rest ih =>
    rw [Nat.add_right_comm]
    exact Script.cons first (ih h2)

theorem step_symm {Al : Type} {x y : List Al} (h : Step true x y) : Step true y x := by
  cases h with
  | insert p q a => exact Step.delete p q a
  | delete p q a => exact Step.insert p q a
  | substitute hs p q a b => exact Step.substitute hs p q b a

theorem script_symm {Al : Type} {n : ℕ} {x y : List Al}
    (h : Script true n x y) : Script true n y x := by
  induction h with
  | nil => exact Script.nil _
  | cons first rest ih =>
    exact script_trans ih (Script.cons (step_symm first) (Script.nil _))

theorem script_to_nil {Al : Type} (x : List Al) : Script true x.length x [] := by
  induction x with
  | nil => exact Script.nil _
  | cons a x ih =>
    have := Step.delete (substitutions := true) [] x a
    simp only [List.nil_append] at this
    exact Script.cons this ih

theorem script_exists {Al : Type} (x y : List Al) : ∃ n, Script true n x y :=
  ⟨_, script_trans (script_to_nil x) (script_symm (script_to_nil y))⟩

theorem edit_attained {Al : Type} (x y : List Al) :
    Script true (edit x y) x y :=
  Nat.sInf_mem (s := {n | Script true n x y}) (script_exists x y)

theorem edit_le {Al : Type} {n : ℕ} {x y : List Al} (h : Script true n x y) :
    edit x y ≤ n := Nat.sInf_le h

theorem dist_symm {q : ℕ} (x y : Word q) : distance x y = distance y x := by
  unfold distance
  exact le_antisymm (edit_le (script_symm (edit_attained y x)))
    (edit_le (script_symm (edit_attained x y)))

end EditMulticoloring.Dev.ExplicitEdit

namespace EditMulticoloring.Code
open EditMulticoloring.Dev.ExplicitEdit in
theorem chk_explicit_edit_codes (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ (encoder decoder : RAM.Program) (modulus : ℕ → ℕ)
      (C CE CD : ℝ) (dE dD n₀ : ℕ),
      0 < C ∧ 0 < CE ∧ 0 < CD ∧ 3 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n →
        let P := parameters q t n
        let p := modulus n
        1 ≤ P.m ∧ P.m + P.ρ = n ∧
        ValidModulus (ceilLog 2 (P.r * P.K + 1)) p ∧
        ((P.k : ℝ) ≥ (n : ℝ) - (2 * t : ℕ) * logBase q n -
          C * Real.log (Real.log (n : ℝ))) ∧
        (∀ u : FixedWord q P.k, (encode t n p (toWord u)).length = n) ∧
        Function.Injective (fun u : FixedWord q P.k => encode t n p (toWord u)) ∧
        Corrects t (Set.range (fun u : FixedWord q P.k => encode t n p (toWord u))) ∧
        (∀ u : FixedWord q P.k,
          RAM.Executes encoder n (toWord u)
            (some ((encode t n p (toWord u)).map Fin.val))
            (softBound CE (6 * t + 2) dE n)) ∧
        (∀ y : Word q,
          RAM.Executes decoder n y ((decode t n p y).map (List.map Fin.val))
            (softBound CD (7 * t + 2) dD n)) ∧
        (∀ (u : FixedWord q P.k) (y : Word q),
          decode t n p y = some (toWord u) ↔ distance y (encode t n p (toWord u)) ≤ t) ∧
        (∀ y : Word q, decode t n p y = none ↔
          ∀ u : FixedWord q P.k, t < distance y (encode t n p (toWord u)))
    := by
  obtain ⟨enc, dec, md, CE, CD, dE, dD, n1, hCE, hCD, hn1, hR⟩ :=
    EditMulticoloring.Code.ram_programs q t hq ht
  obtain ⟨C, hC, n2, hn2, hE⟩ := EditMulticoloring.Code.encoder_redundancy q t hq ht
  refine ⟨enc, dec, md, C, CE, CD, dE, dD, max n1 n2, hC, hCE, hCD,
    le_trans hn1 (le_max_left _ _), ?_⟩
  intro n hn
  have h1 := hR n (le_trans (le_max_left _ _) hn)
  obtain ⟨hm, hmr, hall⟩ := hE n (le_trans (le_max_right _ _) hn)
  obtain ⟨hv, hEnc, hDec⟩ := h1
  obtain ⟨hlen, hinj, -, -, hbd⟩ := hall _ hv
  obtain ⟨hdec1, hdec2⟩ := EditMulticoloring.Code.decoder_correctness q t hq ht n hm _ hv
  have hlow := (abs_le.mp hbd).2
  refine ⟨hm, hmr, hv, ?_, hlen, hinj, ?_, hEnc, hDec, hdec1, hdec2⟩
  · linarith
  · rintro x ⟨u, rfl⟩ z ⟨u', rfl⟩ hne y ⟨h1, h2⟩
    have a := (hdec1 u y).2 (by rw [dist_symm]; exact h1)
    have b := (hdec1 u' y).2 (by rw [dist_symm]; exact h2)
    rw [a] at b
    exact hne (congrArg _ (Option.some.inj b))
end EditMulticoloring.Code
end

theorem solution : type_of% @EditMulticoloring.Code.chk_explicit_edit_codes := @EditMulticoloring.Code.chk_explicit_edit_codes
