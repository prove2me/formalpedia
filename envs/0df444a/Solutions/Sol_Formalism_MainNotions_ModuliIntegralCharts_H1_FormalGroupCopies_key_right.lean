-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.key_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:43:15.897381+00:00
-- url     : https://prove2.me/submissions/b050fa6a-6af5-4ea5-b185-aa1dc2d1998c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dpoly_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dpoly_mul

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
theorem _root_.solution (S : Finset (Fin n)) (P₂ : MvPolynomial ι R) (h2 : ∀ l ∈ P₂.vars, cp l ∉ S)
    (A B : PS R n d) (hA : A ∈ subV R (Vc d S)) (hB : B ∈ subV R (Vc d Sᶜ)) :
    DpolyN F cp u P₂ (A * B) = A * DpolyN F cp u P₂ B := by
  have h := dpoly_mul F cp u S 1 P₂ (by intro l hl; simp [MvPolynomial.vars_one] at hl) h2 A B hA hB
  rwa [one_mul, dpoly_one] at h
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
