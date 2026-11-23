-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.isInteger_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:56.961019+00:00
-- url     : https://prove2.me/submissions/124c1d7f-3920-4f05-bda7-6462d09a129a

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
theorem _root_.solution {m : ℕ} (x : Fin m → Fin m → K) (hx : ∀ i j, IsLocalization.IsInteger (𝓞 K) (x i j)) :
    IsLocalization.IsInteger (𝓞 K) (Matrix.of x).det := by
  have hx' : ∀ i j, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x i j := fun i j => hx i j
  choose y hy using hx'
  refine ⟨(Matrix.of y).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [hy]
end Formalism.L2.LamCM.A2
