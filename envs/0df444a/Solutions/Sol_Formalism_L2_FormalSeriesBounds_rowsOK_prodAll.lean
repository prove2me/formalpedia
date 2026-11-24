-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rowsOK_prodAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:05.571026+00:00
-- url     : https://prove2.me/submissions/6e9cc237-2716-4eeb-8070-aec8fb2834f9

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_kindAll_pl
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_mem_vars_prodAll
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowsOK_iff

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
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  {N K : ℕ} {what₂ : Fin K → ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (G : ∀ g, Cart V d (I g) (J g)) (alt : Prop)
    {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C) (kind : ∀ i, Fin (what₂ i) → Knd d)
    (h : ∀ i, RowsOK G alt (P i) (kind i)) : RowsOK G alt (prodAll pl P) (kindAll pl kind) := by
  rw [rowsOK_iff]
  have h' := fun i => (rowsOK_iff G alt (P i) (kind i)).1 (h i)
  refine ⟨fun ρ g a a' hk => ?_, fun ρ hk => ?_⟩
  · by_cases hex : ∃ s, pl s = ρ
    · obtain ⟨s, rfl⟩ := hex
      rw [kindAll_pl hpl] at hk
      obtain ⟨h1, h2, h3⟩ := (h' s.1).1 s.2 g a a' hk
      refine ⟨h1, h2, fun w hw => ?_⟩
      obtain ⟨s', hs', hw'⟩ := mem_vars_prodAll hw
      have hss := hpl hs'
      subst hss
      exact h3 w hw'
    · exfalso
      unfold kindAll at hk
      rw [dif_neg hex] at hk
      cases hk
  · by_cases hex : ∃ s, pl s = ρ
    · obtain ⟨s, rfl⟩ := hex
      rw [kindAll_pl hpl] at hk
      obtain ⟨g, hg⟩ := (h' s.1).2 s.2 hk
      refine ⟨g, fun w hw => ?_⟩
      obtain ⟨s', hs', hw'⟩ := mem_vars_prodAll hw
      have hss := hpl hs'
      subst hss
      exact hg w hw'
    · refine ⟨0, fun w hw => ?_⟩
      obtain ⟨s', hs', -⟩ := mem_vars_prodAll hw
      exact absurd ⟨s', hs'⟩ hex
end Formalism.L2.FormalSeriesBounds
