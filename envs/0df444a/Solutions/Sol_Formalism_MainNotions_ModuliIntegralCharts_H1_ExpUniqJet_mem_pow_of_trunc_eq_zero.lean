-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.mem_pow_of_trunc_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:47:59.204511+00:00
-- url     : https://prove2.me/submissions/d8edda5f-20d9-4078-b820-66f602d34cc7

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqJet_Ij_eq_map

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
theorem _root_.solution {κ : Type} {m : ℕ} (p : Jet R κ (m + 1))
    (h : (jetTrunc : Jet R κ (m + 1) →ₐ[R] Jet R κ m) p = 0) : p ∈ Ij R κ (m + 1) ^ (m + 1) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
  have hP : P ∈ orig R κ ^ (m + 1) := by
    have e : (jetTrunc : Jet R κ (m + 1) →ₐ[R] Jet R κ m) (Ideal.Quotient.mk _ P) =
        Ideal.Quotient.mk _ P := by
      first
      | rfl
      | simp [jetTrunc]
    rw [e, Ideal.Quotient.eq_zero_iff_mem] at h
    exact h
  rw [Ij_eq_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hP
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
