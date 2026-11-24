-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.sub_kill_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:54.412845+00:00
-- url     : https://prove2.me/submissions/886d11b3-1e1c-4c35-9b33-de347e0a0580

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_poly_sub_kill_mem

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
variable {n : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
theorem _root_.solution (m : ℕ) (i : Fin 2) (e : Jet R (Fin 2 × Fin n) m) : e - kill m i e ∈ Kp m i := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective e
  have h1 : kill m i (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (aeval (killS i) P) := by
    simp only [kill, jetMap, liftJet, Ideal.Quotient.liftₐ_apply]
    erw [Ideal.Quotient.lift_mk]
  rw [h1, ← map_sub]
  have h2 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (orig R (Fin 2 × Fin n) ^ (m + 1)))
    (poly_sub_kill_mem i P)
  rw [Ideal.map_span, ← Set.range_comp] at h2
  exact h2
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
