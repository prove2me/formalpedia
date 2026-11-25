-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.dmon_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:58:25.344852+00:00
-- url     : https://prove2.me/submissions/718f340f-5441-4c06-a29a-e54fe4ca43ca

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_fold_mul

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
variable {R : Type} [CommRing R] {d n : ℕ}
variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
theorem _root_.solution (S : Finset (Fin n)) (m₁ m₂ : ι →₀ ℕ) (hm1 : ∀ l, m₁ l ≠ 0 → cp l ∈ S)
    (hm2 : ∀ l, m₂ l ≠ 0 → cp l ∈ Sᶜ) (A B : PS R n d)
    (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DmonN F cp u (m₁ + m₂) (A * B) = DmonN F cp u m₁ A * DmonN F cp u m₂ B := by
  unfold DmonN
  exact fold_mul F cp u S m₁ m₂ hm1 hm2 _ A B hA hB
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
