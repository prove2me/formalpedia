-- Prove2me | solution 1 for Formalism.L2.G.sq_OO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:44.259411+00:00
-- url     : https://prove2.me/submissions/5a52b468-4d3b-4ec8-af33-05afd6c19590

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_AlgebraMapFinite
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_JOInjective
import Theorems.Thm_Formalism_L2_G_wU_sq
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_L2_G_exists_sq_eq_intCast_of_not_dvd_of_ne_two
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
open QuadraticAlgebra Formalism.BasicNotions.Examples₂ Formalism.MainNotions.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
namespace Formalism.L2.G
theorem _root_.solution [NeZero n] (hp2 : p ≠ 2) (z : ℤ) : ∃ y : OO p n, y ^ 2 = (z : OO p n) := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hfin : FiniteMultiplicity (p : ℤ) z :=
    Int.finiteMultiplicity_iff.2 ⟨by simpa using hp.out.one_lt.ne', hz⟩
  obtain ⟨c, hc, hpc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  obtain ⟨y, hy⟩ := exists_sq_eq_intCast_of_not_dvd_of_ne_two p n hp2 c hpc
  refine ⟨wU p n ^ multiplicity (p : ℤ) z * algebraMap (W2 p n) (OO p n) y, ?_⟩
  rw [mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, wU_sq, ← map_pow, hy, map_intCast]
  conv_rhs => rw [hc]
  push_cast
  rfl
end Formalism.L2.G
