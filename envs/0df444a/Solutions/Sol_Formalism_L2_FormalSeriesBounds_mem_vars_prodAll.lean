-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.mem_vars_prodAll
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:25.633371+00:00
-- url     : https://prove2.me/submissions/4134ee77-448d-4c76-a213-b9206ea59efc

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} {P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C}
    {ρ : Fin N} {w : WV I} (h : (ρ, w) ∈ (prodAll pl P).vars) :
    ∃ s : Σ i : Fin K, Fin (what₂ i), pl s = ρ ∧ (s.2, w) ∈ (P s.1).vars := by
  unfold prodAll at h
  have h1 := MvPolynomial.vars_prod _ h
  rw [Finset.mem_biUnion] at h1
  obtain ⟨i, -, hi⟩ := h1
  have h2 := MvPolynomial.vars_rename _ _ hi
  rw [Finset.mem_image] at h2
  obtain ⟨⟨r, w'⟩, hw', heq⟩ := h2
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨⟨i, r⟩, rfl, hw'⟩
end Formalism.L2.FormalSeriesBounds
