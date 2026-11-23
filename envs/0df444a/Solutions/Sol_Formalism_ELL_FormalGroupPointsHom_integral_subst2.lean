-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.integral_subst2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:50.262343+00:00
-- url     : https://prove2.me/submissions/24e9942c-9126-4f63-839d-9e6d894d76c4

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_coeff_subst_two
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_coeff_mono_eq_zero
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_mul
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_pow
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_mem_unitBall


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {G s t : MvPowerSeries (Fin 2) K} (hG : IntegralMv G) (hs : IntegralMv s)
    (ht : IntegralMv t) (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) : IntegralMv (G.subst ![s, t]) := by
  intro e
  rw [coeff_subst_two G s t hs0 ht0 e]
  have hfin : (Function.support fun d => MvPowerSeries.coeff d G *
      MvPowerSeries.coeff e (s ^ (d 0) * t ^ (d 1))).Finite := by
    refine (finite_degree_lt (e.degree + 1)).subset ?_
    intro d hd
    simp only [Set.mem_ofPred_eq]
    by_contra hge
    apply hd
    simp only
    rw [coeff_mono_eq_zero hs0 ht0 (by omega : e.degree < d.degree), mul_zero]
  rw [finsum_eq_sum _ hfin, ← SubstitutionCoefficientCongruence.mem_unitBall]
  refine Subring.sum_mem _ fun d _ => Subring.mul_mem _ (SubstitutionCoefficientCongruence.mem_unitBall.mpr (hG d))
    (SubstitutionCoefficientCongruence.mem_unitBall.mpr ?_)
  exact SubstitutionCoefficientCongruence.integral_mul (SubstitutionCoefficientCongruence.integral_pow hs _) (SubstitutionCoefficientCongruence.integral_pow ht _) e
end Formalism.ELL.FormalGroupPointsHom
