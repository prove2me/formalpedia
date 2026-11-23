-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.coeff_ofNat_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:15.867548+00:00
-- url     : https://prove2.me/submissions/5f80a47f-34bf-420c-8ff3-9fc8e23676e7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution (a : ℕ) [a.AtLeastTwo] (f : K⟦X⟧) (n : ℕ) :
    coeff n ((OfNat.ofNat a : K⟦X⟧) * f) = (OfNat.ofNat a : K) * coeff n f := by
  have e : (OfNat.ofNat a : K⟦X⟧) = C (OfNat.ofNat a : K) := (map_ofNat C a).symm
  rw [e, coeff_C_mul]
end Formalism.L2.Th1.A.WpSh
