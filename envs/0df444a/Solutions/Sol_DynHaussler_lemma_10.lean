-- Prove2me | solution 1 for DynHaussler.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:01:12.204547+00:00
-- url     : https://prove2.me/submissions/9fb4e02c-5628-4279-89fe-13491b3183fc

import Mathlib
import Definitions.Def_NondualOpt_sfat

set_option autoImplicit false

theorem solution {X : Type*} [Nonempty X] (η : ℝ) (hη : 0 < η) (V : Set (X → ℝ))
    (hV : V.Nonempty) (hV01 : ∀ f ∈ V, ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hrank : NondualOpt.sfat V η = 0) :
    (∀ x : X, (⨆ f : V, (f : X → ℝ) x) - (⨅ f : V, (f : X → ℝ) x) ≤ η) ∧
      (∀ H : Set (X → ℝ), V ⊆ H →
        (∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ∃ x, η < |h x - h' x|) → ∃ f, V = {f}) := by
  haveI : Nonempty V := hV.to_subtype
  have hbdd : ∀ x : X, BddAbove (Set.range fun f : V => (f : X → ℝ) x) := by
    intro x; refine ⟨1, ?_⟩; rintro _ ⟨f, rfl⟩; exact (hV01 f f.2 x).2
  have hbdd' : ∀ x : X, BddBelow (Set.range fun f : V => (f : X → ℝ) x) := by
    intro x; refine ⟨0, ?_⟩; rintro _ ⟨f, rfl⟩; exact (hV01 f f.2 x).1
  have part1 : ∀ x : X, (⨆ f : V, (f : X → ℝ) x) - (⨅ f : V, (f : X → ℝ) x) ≤ η := by
    intro x
    by_contra hcon
    push_neg at hcon
    set a := ⨆ f : V, (f : X → ℝ) x with ha
    set b := ⨅ f : V, (f : X → ℝ) x with hb
    set m := (a + b) / 2 with hm
    obtain ⟨f, hf⟩ := exists_lt_of_lt_ciSup (show m + η / 2 < a by linarith)
    obtain ⟨g, hg⟩ := exists_lt_of_ciInf_lt (show b < m - η / 2 by linarith)
    have hone : (1 : ℕ∞) ≤ NondualOpt.sfat V η := by
      unfold NondualOpt.sfat
      refine le_iSup₂_of_le (f := fun (n : ℕ) (_ : ∃ z : NondualOpt.Tree X n,
        ∃ s : NondualOpt.Tree ℝ n, ∀ ε : Fin n → Bool, ∃ h ∈ V, ∀ t : Fin n,
          η / 2 ≤ (if ε t then (1 : ℝ) else -1) *
            (h (z t (NondualOpt.histPrefix ε t)) - s t (NondualOpt.histPrefix ε t))) =>
          (n : ℕ∞)) 1 ⟨fun _ _ => x, fun _ _ => m, fun ε => ?_⟩ (by simp)
      cases hε : ε 0 with
      | true =>
        refine ⟨f, f.2, fun t => ?_⟩
        obtain rfl : t = 0 := Subsingleton.elim _ _
        rw [hε, if_pos rfl]
        linarith
      | false =>
        refine ⟨g, g.2, fun t => ?_⟩
        obtain rfl : t = 0 := Subsingleton.elim _ _
        rw [hε]
        simp only [Bool.false_eq_true, if_false]
        linarith
    rw [hrank] at hone
    exact absurd hone (by simp)
  refine ⟨part1, fun H hVH hsep => ?_⟩
  obtain ⟨f, hf⟩ := hV
  refine ⟨f, ?_⟩
  ext g
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hg
    by_contra hne
    obtain ⟨x, hx⟩ := hsep g (hVH hg) f (hVH hf) hne
    have h1 : g x ≤ ⨆ f : V, (f : X → ℝ) x := le_ciSup (hbdd x) ⟨g, hg⟩
    have h2 : ⨅ f : V, (f : X → ℝ) x ≤ g x := ciInf_le (hbdd' x) ⟨g, hg⟩
    have h3 : f x ≤ ⨆ f : V, (f : X → ℝ) x := le_ciSup (hbdd x) ⟨f, hf⟩
    have h4 : ⨅ f : V, (f : X → ℝ) x ≤ f x := ciInf_le (hbdd' x) ⟨f, hf⟩
    have h5 := part1 x
    have : |g x - f x| ≤ η := by
      rw [abs_le]; constructor <;> linarith
    linarith
  · rintro rfl; exact hf
