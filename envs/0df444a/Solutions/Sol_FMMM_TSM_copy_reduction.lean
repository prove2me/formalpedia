-- Prove2me | solution 1 for FMMM.TSM.copy_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T15:19:27.485755+00:00
-- url     : https://prove2.me/submissions/1f4f2b98-2721-456d-baef-95fa73260eb8

import Mathlib
import Definitions.Def_FMMM_TSM_unifProb
import Definitions.Def_FMMM_TSM_realOPT
import Definitions.Def_FMMM_TSM_Copy
import Definitions.Def_FMMM_TSM_copyEdges

open FMMM.TSM in
theorem solution {A I : Type} [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (E : Finset (A × I)) (e : I → ℕ) :
    (∀ ω : Fin (∑ i, e i) → Copy e,
      realOPT (copyEdges E e) ω = realOPT E (fun t => (ω t).1)) ∧
    ∀ τ : Fin (∑ i, e i) → I,
      unifProb (Copy e) (∑ i, e i) (fun ω => (fun t => (ω t).1) = τ) =
        ∏ t, (e (τ t) : ℝ) / ((∑ i, e i : ℕ) : ℝ) := by
  refine ⟨fun ω => ?_, fun τ => ?_⟩
  · unfold realOPT copyEdges
    congr 1
    ext M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · have hfibre : ∀ i0 : I, (Finset.univ.filter (fun x : Copy e => x.1 = i0)).card = e i0 := by
      intro i0
      rw [Finset.card_filter, Fintype.sum_sigma, Finset.sum_eq_single i0]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    have key : ∀ inst : DecidablePred (fun ω : Fin (∑ i, e i) → Copy e => (fun t => (ω t).1) = τ),
        (@Finset.filter _ (fun ω : Fin (∑ i, e i) → Copy e => (fun t => (ω t).1) = τ) inst
          Finset.univ).card = ∏ t, e (τ t) := by
      intro inst
      have hset : @Finset.filter _ (fun ω : Fin (∑ i, e i) → Copy e => (fun t => (ω t).1) = τ) inst
          Finset.univ =
          Fintype.piFinset (fun t => Finset.univ.filter (fun x : Copy e => x.1 = τ t)) := by
        ext ω
        simp [Fintype.mem_piFinset, funext_iff]
      rw [hset, Fintype.card_piFinset]
      simp only [hfibre]
    have hcard : Fintype.card (Copy e) = ∑ i, e i := by
      simp [Copy, Fintype.card_sigma]
    unfold unifProb
    rw [key, hcard]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rfl
