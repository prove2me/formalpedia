-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.eq_zero_of_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:39.781287+00:00
-- url     : https://prove2.me/submissions/1a46f4ce-d0f6-4fb1-930e-4565fdc66284

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_Ij_pow_eq_bot

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
theorem _root_.solution {κ : Type} {m k : ℕ} (hk : m + 1 ≤ k) {p : Jet R κ m} (hp : p ∈ Ij R κ m ^ k) :
    p = 0 := by
  have h := Ideal.pow_le_pow_right hk hp
  rw [Ij_pow_eq_bot] at h
  exact (Submodule.mem_bot _).1 h
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
