-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rowsOK_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:57:03.335809+00:00
-- url     : https://prove2.me/submissions/21439684-04e1-4605-8097-e8c89f5fb5c2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
section Place
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}
end Place
section Rows
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  {N K : ℕ} {what₂ : Fin K → ℕ}
private lemma forall_support_ne_zero_iff_forall_mem_vars {R0 : Type} [Field R0] {α β : Type} (Q : MvPolynomial (α × β) R0)
    (ρ : α) (T : β → Prop) :
    (∀ μ ∈ Q.support, ∀ w, μ (ρ, w) ≠ 0 → T w) ↔ (∀ w, (ρ, w) ∈ Q.vars → T w) := by
  constructor
  · intro H w hw
    obtain ⟨μ, hμ, hx⟩ := (MvPolynomial.mem_vars _).1 hw
    exact H μ hμ w (Finsupp.mem_support_iff.1 hx)
  · intro H μ hμ w hx
    exact H w ((MvPolynomial.mem_vars _).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hx⟩)
end Rows
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  {N K : ℕ} {what₂ : Fin K → ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop) {N : ℕ} (P : MvPolynomial (Fin N × WV I) C)
    (kind : Fin N → Knd d) : RowsOK G alt P kind ↔
      (∀ ρ g a a', kind ρ = some (g, a, a') → alt ∧ Odd (a' - a).val ∧
        ∀ w, (ρ, w) ∈ P.vars → OnLeafV G g a a' w) ∧
      (∀ ρ, kind ρ = none → ∃ g : Fin 2, ∀ w : WV I, (ρ, w) ∈ P.vars → w.1 = g) := by
  unfold RowsOK
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
    · obtain ⟨h1a, h1b, h1c⟩ := h1 ρ g a a' hk
      exact ⟨h1a, h1b, (forall_support_ne_zero_iff_forall_mem_vars P ρ (OnLeafV G g a a')).1 h1c⟩
    · obtain ⟨g, hg⟩ := h2 ρ hk
      exact ⟨g, (forall_support_ne_zero_iff_forall_mem_vars P ρ (fun w => w.1 = g)).1 hg⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
    · obtain ⟨h1a, h1b, h1c⟩ := h1 ρ g a a' hk
      exact ⟨h1a, h1b, (forall_support_ne_zero_iff_forall_mem_vars P ρ (OnLeafV G g a a')).2 h1c⟩
    · obtain ⟨g, hg⟩ := h2 ρ hk
      exact ⟨g, (forall_support_ne_zero_iff_forall_mem_vars P ρ (fun w => w.1 = g)).2 hg⟩
end Formalism.L2.FormalSeriesBounds
