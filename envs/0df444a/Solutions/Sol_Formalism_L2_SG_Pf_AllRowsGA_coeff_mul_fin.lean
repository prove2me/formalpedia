-- Prove2me | solution 1 for Formalism.L2.SG.Pf.AllRowsGA.coeff_mul_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:46:28.477115+00:00
-- url     : https://prove2.me/submissions/143b075b-9e1f-47a6-bf19-2e41b30419ff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_AllRowsGA

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
theorem _root_.solution (a b : MonoidAlgebra ℂ G) (g : G) :
    (a * b).coeff g = ∑ h : G, a.coeff h * b.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
end Formalism.L2.SG.Pf.AllRowsGA
