-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.fold_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:39:03.606209+00:00
-- url     : https://prove2.me/submissions/3dd9107e-9ed3-4309-ac5f-f77425d0d18e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dofN_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_it_mem

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
theorem _root_.solution (T : Finset (Fin n)) (mm : ι →₀ ℕ) (hm : ∀ l, mm l ≠ 0 → cp l ∈ T) (L : List ι)
    (A : PS R n d) (hA : A ∈ subV R (Vc d T)) :
    L.foldr (fun l g => (DofN F (cp l) (u l))^[mm l] g) A ∈ subV R (Vc d T) := by
  induction L with
  | nil => exact hA
  | cons l L ih =>
    rw [List.foldr_cons]
    by_cases hl : mm l = 0
    · rw [hl, Function.iterate_zero_apply]
      exact ih
    · exact it_mem (DofN F (cp l) (u l)) (subV R (Vc d T))
        (fun g hg => dofN_mem F T (hm l hl) (u l) g hg) (mm l) _ ih
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
