-- Prove2me | solution 1 for DenardoDP.NStage.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:13:55.877067+00:00
-- url     : https://prove2.me/submissions/41441f94-9fdc-43c3-be46-4e8cf6fd628a

import Mathlib
import Definitions.Def_DenardoDP_NStage_Model

set_option autoImplicit false

theorem solution {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → DenardoDP.Contraction.BFun Ω → ℝ) (H : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (A : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (hH : DenardoDP.Contraction.IsPolicyOperator h H) (hA : DenardoDP.Contraction.IsMaxOperator h A)
    (hmono : DenardoDP.Contraction.MonotonicityAssumption H) :
    (∀ u w, DenardoDP.Contraction.PLe w u → DenardoDP.Contraction.PLe (A w) (A u)) ∧
    (∀ w, DenardoDP.Contraction.PLe w (A w) → ∀ n : ℕ, DenardoDP.Contraction.PLe (A^[n] w) (A^[n + 1] w)) ∧
    (∀ δ w, DenardoDP.Contraction.PLe w (H δ w) → ∀ n : ℕ, DenardoDP.Contraction.PLe ((H δ)^[n] w) ((H δ)^[n + 1] w)) := by
  classical
  have hne : ∀ y, Nonempty (D y) := by
    intro y
    by_contra hc
    rw [not_nonempty_iff] at hc
    have hl := hA 0 y
    have hr : (Set.range fun d : D y => h y d 0) = ∅ := Set.range_eq_empty _
    rw [hr] at hl
    have := hl.2 (show (A 0 y - 1) ∈ upperBounds (∅ : Set ℝ) by simp)
    linarith
  have hAmono : ∀ u w, DenardoDP.Contraction.PLe w u →
      DenardoDP.Contraction.PLe (A w) (A u) := by
    intro u w hwu x
    refine (hA w x).2 ?_
    rintro _ ⟨d, rfl⟩
    let δ0 : (y : Ω) → D y := fun y => Classical.choice (hne y)
    let δ : (y : Ω) → D y := Function.update δ0 x d
    have hδ : δ x = d := Function.update_self x d δ0
    have h1 : h x d w = H δ w x := by rw [hH, hδ]
    have h2 : h x d u = H δ u x := by rw [hH, hδ]
    have h3 : H δ w x ≤ H δ u x := hmono δ u w hwu x
    have h4 : h x d u ≤ A u x := (hA u x).1 ⟨d, rfl⟩
    simp only
    linarith
  refine ⟨hAmono, ?_, ?_⟩
  · intro w hw n
    induction n with
    | zero => simpa using hw
    | succ n ih =>
      have := hAmono _ _ ih
      rw [← Function.iterate_succ_apply' A n w, ← Function.iterate_succ_apply' A (n + 1) w] at this
      exact this
  · intro δ w hw n
    induction n with
    | zero => simpa using hw
    | succ n ih =>
      have := hmono δ _ _ ih
      rw [← Function.iterate_succ_apply' (H δ) n w, ← Function.iterate_succ_apply' (H δ) (n + 1) w] at this
      exact this
