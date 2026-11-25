-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsGA.central_of_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:27.883066+00:00
-- url     : https://prove2.me/submissions/1b54e10f-6975-4825-8085-9c93a59a4cc0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_coeff_mul_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MonoidAlgebra
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.AllRowsGA
variable {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.SG.Pf.AllRowsGA
theorem _root_.solution (a : MonoidAlgebra ℂ G) (h : ∀ g P : G, a.coeff (P⁻¹ * g * P) = a.coeff g)
    (y : MonoidAlgebra ℂ G) : a * y = y * a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [coeff_mul_fin, coeff_mul_fin]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight g)) _ _ fun k => ?_
  have e1 : (k⁻¹ * g)⁻¹ * g = g⁻¹ * k * g := by group
  show a.coeff k * y.coeff (k⁻¹ * g) = y.coeff (k⁻¹ * g) * a.coeff ((k⁻¹ * g)⁻¹ * g)
  rw [e1, h k g]
  exact mul_comm _ _
end Formalism.L2.SG.Pf.AllRowsGA
