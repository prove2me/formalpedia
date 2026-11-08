-- Prove2me | solution 1 for ConvexRMDP.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:40:58.373902+00:00
-- url     : https://prove2.me/submissions/9b8f5e72-0e32-4ef0-9e62-7e3132c69ea0

import Mathlib

namespace Aux_CRMDP

lemma below {S : Type*} [Fintype S] (F : (S → ℝ) → (S → ℝ)) (K : NNReal)
    (hF_mono : Monotone F) (hF_contr : ContractingWith K F) (vs : S → ℝ) (hvs : F vs = vs)
    (v : S → ℝ) (hv : F v ≤ v) : vs ≤ v := by
  have hit : ∀ n, F^[n] v ≤ v := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => rw [Function.iterate_succ_apply]; exact le_trans (hF_mono.iterate n hv) ih
  have ht := hF_contr.tendsto_iterate_fixedPoint v
  rw [← hF_contr.fixedPoint_unique hvs] at ht
  exact le_of_tendsto' ht hit

lemma above {S : Type*} [Fintype S] (F : (S → ℝ) → (S → ℝ)) (K : NNReal)
    (hF_mono : Monotone F) (hF_contr : ContractingWith K F) (vs : S → ℝ) (hvs : F vs = vs)
    (v : S → ℝ) (hv : v ≤ F v) : v ≤ vs := by
  have hit : ∀ n, v ≤ F^[n] v := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => rw [Function.iterate_succ_apply]; exact le_trans ih (hF_mono.iterate n hv)
  have ht := hF_contr.tendsto_iterate_fixedPoint v
  rw [← hF_contr.fixedPoint_unique hvs] at ht
  exact ge_of_tendsto' ht hit

end Aux_CRMDP

theorem solution {S : Type*} [Fintype S] (F : (S → ℝ) → (S → ℝ)) (K : NNReal)
    (hF_mono : Monotone F) (hF_contr : ContractingWith K F)
    (g : (S → ℝ) → ℝ) (hg : Monotone g) (vs : S → ℝ) (hvs : F vs = vs) :
    IsLeast (g '' {v | F v ≤ v}) (g vs) ∧ IsGreatest (g '' {v | v ≤ F v}) (g vs) ∧
      (StrictMono g →
        (∀ v, F v ≤ v → g v = g vs → v = vs) ∧ (∀ v, v ≤ F v → g v = g vs → v = vs)) := by
  refine ⟨⟨⟨vs, hvs.le, rfl⟩, ?_⟩, ⟨⟨vs, hvs.ge, rfl⟩, ?_⟩, fun hsm => ⟨?_, ?_⟩⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hg (Aux_CRMDP.below F K hF_mono hF_contr vs hvs v hv)
  · rintro _ ⟨v, hv, rfl⟩
    exact hg (Aux_CRMDP.above F K hF_mono hF_contr vs hvs v hv)
  · intro v hv heq
    by_contra hne
    have hlt : vs < v := lt_of_le_of_ne (Aux_CRMDP.below F K hF_mono hF_contr vs hvs v hv)
      (Ne.symm hne)
    exact (ne_of_gt (hsm hlt)) heq
  · intro v hv heq
    by_contra hne
    have hlt : v < vs := lt_of_le_of_ne (Aux_CRMDP.above F K hF_mono hF_contr vs hvs v hv) hne
    exact (ne_of_lt (hsm hlt)) heq
