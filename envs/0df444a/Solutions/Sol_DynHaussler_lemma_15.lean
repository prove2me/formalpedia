-- Prove2me | solution 1 for DynHaussler.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:24:33.829595+00:00
-- url     : https://prove2.me/submissions/99efdc78-ac6f-416e-b734-aa5f2740925f

import Mathlib
import Definitions.Def_DynHaussler_errClass
import Definitions.Def_DynHaussler_partialLdim
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

namespace DynHaussler.Aux_DH

theorem decode {η e : ℝ} {c : Bool}
    (h : (if e ≤ η then some false else if 2 * η ≤ e then some true else none) = some c) :
    (c = true → 2 * η ≤ e) ∧ (c = false → e ≤ η) := by
  split_ifs at h with h1 h2
  · have := Option.some.inj h
    subst this
    exact ⟨fun h => absurd h (by decide), fun _ => h1⟩
  · have := Option.some.inj h
    subst this
    exact ⟨fun _ => h2, fun h => absurd h (by decide)⟩

end DynHaussler.Aux_DH

open DynHaussler DynHaussler.Aux_DH in
theorem solution {X : Type*} [Nonempty X] (η : ℝ) (hη : 0 < η) (H : Set (X → ℝ))
    (hH01 : ∀ f ∈ H, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (plus : Bool) :
    partialLdim (errClass η H plus) ≤ NondualOpt.sfat H η := by
  unfold partialLdim NondualOpt.sfat
  apply iSup₂_le
  intro n ⟨z, hz⟩
  apply le_iSup₂_of_le (f := fun (n : ℕ) (_ : ∃ z : NondualOpt.Tree X n, ∃ s : NondualOpt.Tree ℝ n,
      ∀ ε : Fin n → Bool, ∃ h ∈ H, ∀ t : Fin n,
      η / 2 ≤ (if ε t then (1 : ℝ) else -1) *
        (h (z t (NondualOpt.histPrefix ε t)) - s t (NondualOpt.histPrefix ε t))) => (n : ℕ∞)) n
    _ le_rfl
  cases plus with
  | true =>
    refine ⟨fun t hs => (z t hs).1, fun t hs => (z t hs).2 + 3 / 2 * η, ?_⟩
    intro ε
    obtain ⟨φ, hφ, hall⟩ := hz ε
    obtain ⟨f, hf, rfl⟩ := hφ
    refine ⟨f, hf, fun t => ?_⟩
    have hd := decode (η := η)
      (e := f (z t (NondualOpt.histPrefix ε t)).1 - (z t (NondualOpt.histPrefix ε t)).2)
      (c := ε t) (hall t)
    show η / 2 ≤ (if ε t then (1 : ℝ) else -1) *
      (f (z t (NondualOpt.histPrefix ε t)).1 - ((z t (NondualOpt.histPrefix ε t)).2 + 3 / 2 * η))
    cases hε : ε t
    · have := hd.2 hε
      norm_num
      linarith
    · have := hd.1 hε
      norm_num
      linarith
  | false =>
    refine ⟨fun t hs => (z t (fun i => !hs i)).1,
      fun t hs => (z t (fun i => !hs i)).2 - 3 / 2 * η, ?_⟩
    intro ε
    obtain ⟨φ, hφ, hall⟩ := hz (fun t => !ε t)
    obtain ⟨f, hf, rfl⟩ := hφ
    refine ⟨f, hf, fun t => ?_⟩
    have hd := decode (η := η)
      (e := (z t (fun i => !(NondualOpt.histPrefix ε t i))).2 -
        f (z t (fun i => !(NondualOpt.histPrefix ε t i))).1)
      (c := !ε t) (hall t)
    show η / 2 ≤ (if ε t then (1 : ℝ) else -1) *
      (f (z t (fun i => !(NondualOpt.histPrefix ε t i))).1 -
        ((z t (fun i => !(NondualOpt.histPrefix ε t i))).2 - 3 / 2 * η))
    cases hε : ε t
    · have := hd.1 (by rw [hε]; rfl)
      norm_num
      linarith
    · have := hd.2 (by rw [hε]; rfl)
      norm_num
      linarith
