-- Prove2me | solution 1 for Formalism.L2.Pj.ex_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:32.171368+00:00
-- url     : https://prove2.me/submissions/a845475e-dbd7-4b4d-a6e1-fc82a28d2fdf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace Formalism.L2.Pj
theorem _root_.solution (Dw : Datum H) (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) :
    ex Dw (a + a') (n + n') = ex Dw a n + ex Dw a' n' := by
  funext i; cases i <;> rfl
end Formalism.L2.Pj
