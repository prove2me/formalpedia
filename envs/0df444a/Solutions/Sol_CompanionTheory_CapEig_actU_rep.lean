-- Prove2me | solution 1 for CompanionTheory.CapEig.actU_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:30.427949+00:00
-- url     : https://prove2.me/submissions/a4d6a9ea-16f9-428c-8808-95baaea9e2fa

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Theorems.Thm_CompanionTheory_CapEig_lift_eq_sum
import Theorems.Thm_CompanionTheory_CapEig_word_rep

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
theorem _root_.solution (hm : ∀ a b, inUJ ε a → inUJ ε b → σ (a * b) = (σ a).comp (σ b)) {v : Hs} {x : ioS ε Hs}
    (hx : IORep (fun y => σ y v) x.1) (p : FreeAlgebra ℂ (Fin n × Fin n)) :
    IORep (fun y => σ y (actU ε σ p v)) (FreeAlgebra.lift ℂ (fun ab : Fin n × Fin n => ioE ε Hs ab.1 ab.2) p x).1 := by
  intro g hg
  rw [lift_eq_sum]
  unfold actU Finsupp.sum
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← word_rep hm hx w.toList g hg]
end CompanionTheory.CapEig
