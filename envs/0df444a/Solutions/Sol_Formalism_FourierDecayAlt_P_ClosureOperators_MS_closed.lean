-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.MS_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:53:48.88281+00:00
-- url     : https://prove2.me/submissions/84b84945-a607-4761-8569-64a243a5ff19

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_mul_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution {n : ℕ} (f : Fin n → Module.End ℂ V) (hf : ∀ a b, f a * f b = f b * f a) (v : V) (x : Fin n) :
    ∀ p ∈ MS f v, f x p ∈ MS f v := by
  intro p hp
  have hle : MS f v ≤ (MS f v).comap (f x) := by
    unfold MS
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨a', ha'⟩ := mul_mono f hf a x
    show f x (mono f a v) ∈ Submodule.span ℂ (Set.range fun a : Fin n → ℕ => mono f a v)
    rw [show f x (mono f a v) = (f x * mono f a) v from rfl, ha']
    exact Submodule.subset_span ⟨a', rfl⟩
  exact hle hp
end Formalism.FourierDecayAlt.P.ClosureOperators
