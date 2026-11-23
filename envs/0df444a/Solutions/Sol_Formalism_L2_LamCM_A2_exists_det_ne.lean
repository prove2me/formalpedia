-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.exists_det_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:56.922581+00:00
-- url     : https://prove2.me/submissions/8dd49bfb-47cf-409d-8410-824521fcb022

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {m : ℕ} (M : Submodule (𝓞 K) (Fin m → K))
    (hM : Submodule.span K (M : Set (Fin m → K)) = ⊤) :
    ∃ x : Fin m → Fin m → K, (∀ i, x i ∈ M) ∧ (Matrix.of x).det ≠ 0 := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (M : Set (Fin m → K))
  let B := Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hspan, hM]))
  let e := B.indexEquiv (Pi.basisFun K (Fin m))
  refine ⟨fun i => (e.symm i : Fin m → K), fun i => hs (e.symm i).2, ?_⟩
  have hli' : LinearIndependent K (fun i => (e.symm i : Fin m → K)) := hli.comp _ e.symm.injective
  have : IsUnit (Matrix.of fun i => (e.symm i : Fin m → K)) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
end Formalism.L2.LamCM.A2
