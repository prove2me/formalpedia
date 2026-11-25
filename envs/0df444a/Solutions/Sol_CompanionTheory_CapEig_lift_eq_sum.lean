-- Prove2me | solution 1 for CompanionTheory.CapEig.lift_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:58:18.152667+00:00
-- url     : https://prove2.me/submissions/bac0363e-6bda-48f8-ad74-72318f1e3778

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct

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
namespace CompanionTheory.CapEig
theorem _root_.solution {X A : Type} [Ring A] [Algebra ℂ A] (f : X → A) (p : FreeAlgebra ℂ X) :
    FreeAlgebra.lift ℂ f p = (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff.sum
      fun w c => c • (w.toList.map f).prod := by
  have e : FreeAlgebra.lift ℂ f = (MonoidAlgebra.lift ℂ A (FreeMonoid X) (FreeMonoid.lift f)).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := X)).toAlgHom := by
    ext x
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [e]
  show MonoidAlgebra.lift ℂ A (FreeMonoid X) (FreeMonoid.lift f) (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) = _
  rw [MonoidAlgebra.lift_apply]
  simp only [FreeMonoid.lift_apply]
end CompanionTheory.CapEig
