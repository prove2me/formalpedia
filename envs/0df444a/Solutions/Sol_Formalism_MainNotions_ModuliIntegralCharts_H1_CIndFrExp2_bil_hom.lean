-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.bil_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:42:50.064945+00:00
-- url     : https://prove2.me/submissions/ec2ba031-be56-49a8-8426-3fa4969c1695

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
variable {S : Type} [CommRing S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
theorem _root_.solution (M : Fin d → Fin d → S) : (bil M).IsHomogeneous 2 := by
  unfold bil
  refine IsHomogeneous.sum _ _ _ fun i _ => IsHomogeneous.sum _ _ _ fun l _ => ?_
  have h0 : (C (M i l) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 0 := by
    first
      | exact isHomogeneous_C _ _
      | exact isHomogeneous_C _
  have h1 : (X ((0 : Fin 2), i) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 1 := by
    first
      | exact isHomogeneous_X _ _
      | exact isHomogeneous_X _
  have h2 : (X ((1 : Fin 2), l) : MvPolynomial (Fin 2 × Fin d) S).IsHomogeneous 1 := by
    first
      | exact isHomogeneous_X _ _
      | exact isHomogeneous_X _
  simpa using h0.mul (h1.mul h2)
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
