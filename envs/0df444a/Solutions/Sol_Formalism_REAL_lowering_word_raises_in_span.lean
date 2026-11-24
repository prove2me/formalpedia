-- Prove2me | solution 1 for Formalism.REAL.lowering_word_raises_in_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:06.774356+00:00
-- url     : https://prove2.me/submissions/ed461dca-975f-4c72-9043-a777a0d63a9d

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_compact_lie_commutator
import Theorems.Thm_Formalism_REAL_word_action_nil
import Theorems.Thm_Formalism_REAL_word_action_cons
import Theorems.Thm_Formalism_REAL_word_action_weight
import Theorems.Thm_Formalism_REAL_lowering_word_mem_span
import Theorems.Thm_Formalism_REAL_self_mem_lowering_span
import Theorems.Thm_Formalism_REAL_lowering_operator_mem_span

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x)
    (w : List (Fin n × Fin n)) (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    ∀ a b, ε a = ε b → F a b (ew F w x) ∈ lowSpan ε F x := by
  induction w with
  | nil =>
    intro a b hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · rw [word_action_nil, hx.2 a b hlt hab]; exact zero_mem _
    · subst heq; rw [word_action_nil, hx.1 a]; exact Submodule.smul_mem _ _ (self_mem_lowering_span x)
    · refine lowering_word_mem_span x [(a, b)] ?_
      simp [hab, hgt]
  | cons p w ih =>
    have hw' : ∀ q ∈ w, ε q.1 = ε q.2 ∧ q.2 < q.1 := fun q hq => hw q (List.mem_cons_of_mem _ hq)
    have hp := hw p List.mem_cons_self
    intro a b hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · rw [word_action_cons]
      have hc := compact_lie_commutator h hab hp.1 (ew F w x)
      rw [sub_eq_iff_eq_add] at hc
      rw [hc]
      refine add_mem (sub_mem ?_ ?_) (lowering_operator_mem_span hp.1 hp.2 (ih hw' a b hab))
      · split_ifs with h1
        · exact ih hw' a p.2 (by rw [hab, h1, hp.1])
        · exact zero_mem _
      · split_ifs with h1
        · exact ih hw' p.1 b (by rw [hp.1, h1, hab])
        · exact zero_mem _
    · subst heq
      have hwt := word_action_weight h hx.1 (p :: w) (fun q hq => (hw q hq).1)
      rw [hwt a]; exact Submodule.smul_mem _ _ (lowering_word_mem_span x _ hw)
    · refine lowering_word_mem_span x ((a, b) :: p :: w) ?_
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hab, hgt⟩
      · exact hw q hq
end Formalism.REAL
