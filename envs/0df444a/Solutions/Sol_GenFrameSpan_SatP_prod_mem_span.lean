-- Prove2me | solution 1 for GenFrameSpan.SatP.prod_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:31.853204+00:00
-- url     : https://prove2.me/submissions/78fbf901-c9b8-45ad-bb24-65a9b35cdcac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
import Theorems.Thm_GenFrameSpan_SatP_nablaX_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
open GenFrameSpan.SatP
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}
namespace GenFrameSpan.SatP
theorem _root_.solution (nu : Lt → YoungDiagram) (g : Lt → MvPolynomial (ℕ × Fin N0) ℤ)
    (hg : ∀ s, g s ∈ nablaSpan ℤ N0 (nu s)) :
    ∏ s, rename (emb s) (g s) ∈ Submodule.span ℤ (Set.range (nablaX N0 nu)) := by
  by_cases hne : Nonempty (ColChoice N0 nu)
  · obtain ⟨J0⟩ := hne
    suffices H : ∀ F : Finset Lt, ∏ s ∈ F, rename (emb s) (g s) ∈ Submodule.span ℤ
        (Set.range fun J : ColChoice N0 nu =>
          ∏ s ∈ F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c))) by
      have H1 := H Finset.univ
      have hf : (fun J : ColChoice N0 nu =>
          ∏ s, rename (emb s) (∏ c : Fin ((nu s).rowLen 0), minorX ℤ N0 ((nu s).colLen c) (J s c))) = nablaX N0 nu :=
        funext fun J => (nablaX_eq nu J).symm
      rw [hf] at H1
      exact H1
    intro F
    induction F using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact Submodule.subset_span ⟨J0, rfl⟩
    | insert a F haF ih =>
      rw [Finset.prod_insert haF]
      have ha : rename (emb a) (g a) ∈ Submodule.span ℤ (Set.range fun
          j : (∀ c : Fin ((nu a).rowLen 0), Fin ((nu a).colLen c) ↪o Fin N0) =>
            rename (emb a) (∏ c : Fin ((nu a).rowLen 0), minorX ℤ N0 ((nu a).colLen c) (j c))) := by
        have := Submodule.mem_map_of_mem (f := (rename (emb a)).toLinearMap) (hg a)
        rw [nablaSpan, Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hm := Submodule.mul_mem_mul ha ih
      rw [Submodule.span_mul_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨J, rfl⟩, rfl⟩
      change (∀ s, ∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N0) at J
      refine ⟨Function.update J a j, ?_⟩
      show ∏ s ∈ insert a F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0),
          minorX ℤ N0 ((nu s).colLen c) (Function.update J a j s c)) =
        rename (emb a) (∏ c : Fin ((nu a).rowLen 0), minorX ℤ N0 ((nu a).colLen c) (j c)) *
          ∏ s ∈ F, rename (emb s) (∏ c : Fin ((nu s).rowLen 0),
            minorX ℤ N0 ((nu s).colLen c) (J s c))
      rw [Finset.prod_insert haF, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun s hs => ?_
      have hsa : s ≠ a := fun h => haF (h ▸ hs)
      rw [Function.update_of_ne hsa]
  · have hex : ∃ s, IsEmpty (∀ c : Fin ((nu s).rowLen 0), Fin ((nu s).colLen c) ↪o Fin N0) := by
      by_contra hcon
      push Not at hcon
      exact hne ⟨fun s => (hcon s).some⟩
    obtain ⟨s, hs⟩ := hex
    have h0 : g s = 0 := by
      have := hg s
      rw [nablaSpan, Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
      exact this
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (by rw [h0, map_zero])]
    exact Submodule.zero_mem _
end GenFrameSpan.SatP
