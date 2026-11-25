-- Prove2me | solution 1 for CompanionTheory.CapEig.capelli_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:57.301248+00:00
-- url     : https://prove2.me/submissions/55c1d84b-1fd5-413a-a656-99dc06c99c4c

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Theorems.Thm_CompanionTheory_CapEig_algHom_qdet
import Theorems.Thm_CompanionTheory_CapEig_actU_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_qminor_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.DSInfCharCap
noncomputable section
open CompanionTheory CompanionTheory.CapEig
variable {n : ℕ} {ε : Fin n → Bool} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)}
namespace CompanionTheory.CapEig
theorem _root_.solution (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs}
    (hv : SmoothOnGV ε fun x => σ x v) (u : ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    capelli ε u (fun x => σ x v) g = σ g (actU ε σ (qdet (Egl n) u) v) := by
  obtain ⟨x, hx⟩ := io_rep_mk hv
  have h1 := io_qminor_rep id id u hx g hg
  have h2 := actU_rep hm hx (qdet (Egl n) u) g hg
  rw [algHom_qdet] at h2
  simp only [Egl, FreeAlgebra.lift_ι_apply] at h2
  unfold capelli qdetOp
  rw [h1]
  exact h2.symm
end CompanionTheory.CapEig
