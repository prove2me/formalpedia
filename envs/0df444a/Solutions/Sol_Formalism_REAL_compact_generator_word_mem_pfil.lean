-- Prove2me | solution 1 for Formalism.REAL.compact_generator_word_mem_pfil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:54.384194+00:00
-- url     : https://prove2.me/submissions/63b4b060-c904-4b6d-b191-1d0b294bbfea

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_compact_span_compact_stable
import Theorems.Thm_Formalism_REAL_ew_cons
import Theorems.Thm_Formalism_REAL_ew_nil
import Theorems.Thm_Formalism_REAL_word_action_mem_pfil
import Theorems.Thm_Formalism_REAL_noncompact_generator_raises_pfil
import Theorems.Thm_Formalism_REAL_gl_commutator_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution (hE : GlRel E) (a b : Fin n) (hab : ε a = ε b) (y : V) (hy : y ∈ kSpan ε E u) :
    ∀ w : List (Fin n × Fin n), (∀ p ∈ w, ε p.1 ≠ ε p.2) →
      E a b (ew E w y) ∈ pfil ε E u w.length := by
  intro w
  induction w with
  | nil =>
    intro _
    have hy' : E a b y ∈ kSpan ε E u := compact_span_compact_stable ε E u a b hab y hy
    have h0 := word_action_mem_pfil ε E u 0 [] (le_refl _) (by intro p hp; cases hp) (E a b y) hy'
    rw [ew_nil] at h0
    rw [ew_nil]
    exact h0
  | cons p w ih =>
    intro hnc
    have hnc' : ∀ q ∈ w, ε q.1 ≠ ε q.2 := fun q hq => hnc q (List.mem_cons.mpr (Or.inr hq))
    have hp : ε p.1 ≠ ε p.2 := hnc p (List.mem_cons.mpr (Or.inl rfl))
    have hih := ih hnc'
    rw [ew_cons, gl_commutator_apply E hE a b p.1 p.2]
    simp only [List.length_cons]
    refine add_mem (noncompact_generator_raises_pfil ε E u _ p.1 p.2 hp _ hih) (sub_mem ?_ ?_)
    · split_ifs with h1
      · have hne : ε a ≠ ε p.2 := by rw [hab, h1]; exact hp
        have hnc2 : ∀ q ∈ (a, p.2) :: w, ε q.1 ≠ ε q.2 := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hne
          · exact hnc' q hq
        have h3 := word_action_mem_pfil ε E u (w.length + 1) ((a, p.2) :: w) (by simp) hnc2 y hy
        rw [ew_cons] at h3
        exact h3
      · exact Submodule.zero_mem _
    · split_ifs with h2
      · have hne : ε p.1 ≠ ε b := by rw [← hab, ← h2]; exact hp
        have hnc2 : ∀ q ∈ (p.1, b) :: w, ε q.1 ≠ ε q.2 := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hne
          · exact hnc' q hq
        have h3 := word_action_mem_pfil ε E u (w.length + 1) ((p.1, b) :: w) (by simp) hnc2 y hy
        rw [ew_cons] at h3
        exact h3
      · exact Submodule.zero_mem _
end Formalism.REAL
