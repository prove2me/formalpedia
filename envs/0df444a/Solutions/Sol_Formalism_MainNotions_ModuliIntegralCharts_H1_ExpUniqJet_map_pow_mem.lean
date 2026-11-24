-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.map_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:40.994519+00:00
-- url     : https://prove2.me/submissions/3a152999-9dfd-4298-876d-91c4cc3a262e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet

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
theorem _root_.solution {κ κ' : Type} {m m' : ℕ} (f : Jet R κ m →ₐ[R] Jet R κ' m')
    (hf : ∀ j, f (zz m j) ∈ Ij R κ' m') (k : ℕ) {p : Jet R κ m} (hp : p ∈ Ij R κ m ^ k) :
    f p ∈ Ij R κ' m' ^ k := by
  have h1 : Ideal.map f (Ij R κ m) ≤ Ij R κ' m' := by
    rw [Ij, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hf j
  have h2 : Ideal.map f (Ij R κ m ^ k) ≤ Ij R κ' m' ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h1 k
  exact h2 (Ideal.mem_map_of_mem f hp)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
