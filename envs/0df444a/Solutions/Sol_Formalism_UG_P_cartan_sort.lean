-- Prove2me | solution 1 for Formalism.UG.P.cartan_sort
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:50:12.282246+00:00
-- url     : https://prove2.me/submissions/1af96395-b066-4c09-9040-4ce4cedd3c95

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_Formalism_UG_P_cartan_perm_glint
import Theorems.Thm_Formalism_UG_P_cartan_diag_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
namespace Formalism.UG.P
theorem _root_.solution (ϖ : L) {m : ℕ} (a : Fin m → ℤ) :
    ∃ a' : Fin m → ℤ, Antitone a' ∧ ∃ S₁ ∈ GLint (Fin m) O, ∃ S₂ ∈ GLint (Fin m) O,
      Matrix.diagonal (fun i => ϖ ^ a i) = (S₁ : Matrix (Fin m) (Fin m) L) *
        Matrix.diagonal (fun i => ϖ ^ a' i) * (S₂ : Matrix (Fin m) (Fin m) L) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin m), Monotone ((fun i => -a i) ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  obtain ⟨S₁, h₁, e₁⟩ := cartan_perm_glint (L := L) O σ.symm
  obtain ⟨S₂, h₂, e₂⟩ := cartan_perm_glint (L := L) O σ
  refine ⟨a ∘ σ, fun i j hij => ?_, S₁, h₁, S₂, h₂, ?_⟩
  · have := hσ hij
    simp only [Function.comp_apply] at this ⊢
    omega
  · rw [e₁, e₂]
    exact cartan_diag_perm (fun i => ϖ ^ a i) σ
end Formalism.UG.P
