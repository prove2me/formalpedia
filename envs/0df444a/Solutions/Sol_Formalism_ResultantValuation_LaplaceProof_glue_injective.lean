-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.glue_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:44.424309+00:00
-- url     : https://prove2.me/submissions/41f5cc53-ef7a-41bd-b39e-8368b29b62b3

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_image_glue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd

set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
variable {a b : ℕ}
namespace Formalism.ResultantValuation.LaplaceProof
theorem _root_.solution : Function.Injective (glue (a := a) (b := b)) := by
  rintro ⟨⟨J, hJ⟩, σ, τ⟩ ⟨⟨J', hJ'⟩, σ', τ'⟩ heq
  have hJJ : J = J' := by
    have h1 := image_glue (⟨⟨J, hJ⟩, σ, τ⟩ : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
      Perm (Fin a) × Perm (Fin b))
    have h2 := image_glue (⟨⟨J', hJ'⟩, σ', τ'⟩ : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
      Perm (Fin a) × Perm (Fin b))
    rw [heq] at h1
    exact h1.symm.trans h2
  subst hJJ
  have hσ : σ = σ' := by
    refine Equiv.ext fun i => ?_
    have hi := congrArg (fun g : Perm (Fin (a + b)) => g (Fin.castAdd b i)) heq
    simp only [glue_castAdd] at hi
    exact (J.orderEmbOfFin hJ).injective hi
  have hτ : τ = τ' := by
    refine Equiv.ext fun j => ?_
    have hj := congrArg (fun g : Perm (Fin (a + b)) => g (Fin.natAdd a j)) heq
    simp only [glue_natAdd] at hj
    exact (Jᶜ.orderEmbOfFin (compl_card ⟨J, hJ⟩)).injective hj
  subst hσ
  subst hτ
  rfl
end Formalism.ResultantValuation.LaplaceProof
