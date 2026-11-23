-- Prove2me | solution 1 for Formalism.ELL.unit_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:45.621638+00:00
-- url     : https://prove2.me/submissions/57867c1e-07a7-4512-aa94-a2f74ba5cdf1

import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_UnitCancel
import Theorems.Thm_Formalism_ELL_N_padic_integer_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.G
namespace Formalism.ELL
theorem _root_.solution : Formalism.ELL.UnitCancel.{u} := by
  intro p _ K _ _ _ _ σ G b hb h
  obtain ⟨u, rfl⟩ := hb
  have := Formalism.ELL.N_padic_integer_smul p K σ _ h ((u⁻¹ : (ℤ_[p])ˣ) : ℤ_[p])
  convert this using 1
  rw [smul_smul, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, inv_mul_cancel]
  simp
end Formalism.ELL
