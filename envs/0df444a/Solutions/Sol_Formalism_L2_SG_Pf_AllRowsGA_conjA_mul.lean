-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsGA.conjA_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:21.890333+00:00
-- url     : https://prove2.me/submissions/93dd2c5b-3515-4f8f-ac40-0c97d7d10ee9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_coeff_mul_fin
import Theorems.Thm_Formalism_L2_SG_Pf_AllRowsGA_conjA_coeff

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
theorem _root_.solution (a b : MonoidAlgebra ℂ G) : conjA (a * b) = conjA b * conjA a := by
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [conjA_coeff, coeff_mul_fin, coeff_mul_fin, star_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
  have e1 : ((g * h)⁻¹ * g)⁻¹ = h := by group
  have e2 : (g * h)⁻¹ = h⁻¹ * g⁻¹ := mul_inv_rev g h
  show star (a.coeff h * b.coeff (h⁻¹ * g⁻¹)) =
    (conjA b).coeff (g * h) * (conjA a).coeff ((g * h)⁻¹ * g)
  rw [conjA_coeff, conjA_coeff, e1, e2, star_mul']
  exact mul_comm _ _
end Formalism.L2.SG.Pf.AllRowsGA
