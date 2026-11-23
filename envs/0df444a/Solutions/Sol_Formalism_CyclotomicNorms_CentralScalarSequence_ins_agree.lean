-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.ins_agree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:26.258519+00:00
-- url     : https://prove2.me/submissions/1da0495a-5111-4aa0-957a-4d3a5976e783

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central

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
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.CentralScalarSequence
variable {G : Type} [Group G]
namespace Formalism.CyclotomicNorms.CentralScalarSequence
theorem _root_.solution {m : ℕ} (i : Fin (m + 1)) (a : G) (x : Fin m → G) (y : ℕ → G)
    (hx : ∀ k : Fin m, x k = y k) :
    ∀ k : Fin (m + 1), Fin.insertNth (α := fun _ => G) i a x k = insN i a y k := by
  intro k
  rcases lt_trichotomy k i with h | h | h
  · rw [Fin.insertNth_apply_below h, eq_rec_constant, hx]
    have h' : (k : ℕ) < i := h
    simp [insN, h']
  · subst h; simp [insN]
  · rw [Fin.insertNth_apply_above h, eq_rec_constant, hx]
    have h' : (i : ℕ) < k := h
    simp [insN, not_lt.mpr h'.le, h'.ne']
end Formalism.CyclotomicNorms.CentralScalarSequence
