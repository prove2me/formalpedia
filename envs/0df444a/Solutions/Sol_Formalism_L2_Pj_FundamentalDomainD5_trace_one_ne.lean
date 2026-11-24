-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.trace_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:47.997572+00:00
-- url     : https://prove2.me/submissions/4ecc7e7e-bd19-49e2-bbf3-37ccae4fa130

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinrankCmType
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ThetaDotSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution : Algebra.trace ℚ K 1 ≠ 0 := by
  rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap]
  simp only [nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero]
  exact Module.finrank_pos.ne'
end Formalism.L2.Pj.FundamentalDomainD5
