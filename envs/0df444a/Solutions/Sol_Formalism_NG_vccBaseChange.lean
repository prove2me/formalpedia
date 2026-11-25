-- Prove2me | solution 1 for Formalism.NG.vccBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:19:29.213806+00:00
-- url     : https://prove2.me/submissions/b350c0da-3687-4bf5-81e3-c6d435488194

import Definitions.Def_Formalism_CharacterColumnKernels_StatementBC
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_MemCcIdealIffForall
import Theorems.Thm_Formalism_NG_mem_ccIdeal_iff_forall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatVccBaseChange := by
  intro O O' _ _ _ _ _ _ _ _ _ e he X T T' hT' Z x
  classical
  set b := Module.Free.chooseBasis O O' with hb
  set φ : (X → O) → (X → O') := fun f => algebraMap O O' ∘ f with hφ
  have hdec : ∀ f ∈ Submodule.span O' (φ '' (T : Set (X → O))),
      ∃ g : Module.Free.ChooseBasisIndex O O' → (X → O), (∀ j, g j ∈ T) ∧ f = ∑ j, b j • φ (g j) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨t, ht, rfl⟩ := hf
      refine ⟨fun j => b.repr 1 j • t, fun j => T.smul_mem ht _, ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      calc algebraMap O O' (t x') = algebraMap O O' (t x') * ∑ j, b.repr 1 j • b j := by
            rw [b.sum_repr, mul_one]
        _ = ∑ j, b j * algebraMap O O' (b.repr 1 j * t x') := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Algebra.smul_def, map_mul]
            ring
    | zero =>
      refine ⟨0, fun j => T.zero_mem, ?_⟩
      funext x'
      simp [hφ]
    | add f f' _ _ hf hf' =>
      obtain ⟨g, hg, rfl⟩ := hf
      obtain ⟨g', hg', rfl⟩ := hf'
      refine ⟨g + g', fun j => T.add_mem (hg j) (hg' j), ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        map_add, mul_add, Finset.sum_add_distrib]
    | smul o f _ hf =>
      obtain ⟨g, hg, rfl⟩ := hf
      refine ⟨fun k => ∑ j, b.repr (o * b j) k • g j, fun k => T.sum_mem fun j _ => T.smul_mem (hg j) _, ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_sum, map_mul]
      calc o * ∑ j, b j * algebraMap O O' (g j x') = ∑ j, (o * b j) * algebraMap O O' (g j x') := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, (∑ k, b.repr (o * b j) k • b k) * algebraMap O O' (g j x') := by
            simp_rw [b.sum_repr]
        _ = ∑ k, b k * ∑ j, algebraMap O O' (b.repr (o * b j) k) * algebraMap O O' (g j x') := by
            simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_def]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hvan : ∀ (g : Module.Free.ChooseBasisIndex O O' → X → O) (x' : X),
      ∑ j, b j * algebraMap O O' (g j x') = 0 → ∀ j, g j x' = 0 := by
    intro g x' h
    have h2 : ∑ j, g j x' • b j = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ h2
  apply le_antisymm
  · have hne : ((fun c : T => IsDiscreteValuationRing.addVal O ((c : X → O) x)) ''
        (ccIdeal T Z : Set T)).Nonempty := ⟨_, 0, (ccIdeal T Z).zero_mem, rfl⟩
    obtain ⟨c0, hc0, hc0eq⟩ := csInf_mem hne
    have hvcc : vcc T Z x = IsDiscreteValuationRing.addVal O ((c0 : X → O) x) := by
      rw [show IsDiscreteValuationRing.addVal O ((c0 : X → O) x) = _ from hc0eq, sInf_image]
      rfl
    rw [hvcc, ← he]
    have hmem : φ (c0 : X → O) ∈ T' := by
      have h1 : φ (c0 : X → O) ∈ (T' : Set (X → O')) := by
        rw [hT']
        exact Submodule.subset_span ⟨c0, c0.2, rfl⟩
      exact h1
    have hc0' : (⟨φ (c0 : X → O), hmem⟩ : T') ∈ ccIdeal T' Z := by
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T Z c0).mp hc0 x' hx'
      simp [hφ, h0]
    exact iInf₂_le _ hc0'
  · unfold vcc
    refine le_iInf₂ fun c' hc' => ?_
    have hc'span : (c' : X → O') ∈ Submodule.span O' (φ '' (T : Set (X → O))) := by
      have h1 : (c' : X → O') ∈ (T' : Set (X → O')) := c'.2
      rw [hT'] at h1
      exact h1
    obtain ⟨g, hg, hgeq⟩ := hdec _ hc'span
    have hgZ : ∀ j, (⟨g j, hg j⟩ : T) ∈ ccIdeal T Z := by
      intro j
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T' Z c').mp hc' x' hx'
      rw [hgeq] at h0
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at h0
      exact hvan g x' h0 j
    rw [hgeq]
    simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    refine AddValuation.map_le_sum _ fun j _ => ?_
    rw [AddValuation.map_mul, he]
    refine le_trans ?_ le_add_self
    exact mul_le_mul_of_nonneg_left (iInf₂_le (⟨g j, hg j⟩ : T) (hgZ j)) (zero_le)
end Formalism.NG
