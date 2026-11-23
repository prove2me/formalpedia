-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.coeff_subst_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:27:48.494438+00:00
-- url     : https://prove2.me/submissions/59125af4-cc20-4f3b-bacd-28c6c2eed0d9

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef

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
theorem _root_.solution (G s t : MvPowerSeries (Fin 2) K) (hs0 : MvPowerSeries.constantCoeff s = 0)
    (ht0 : MvPowerSeries.constantCoeff t = 0) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (G.subst ![s, t]) =
      ∑ᶠ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d G * MvPowerSeries.coeff e (s ^ (d 0) * t ^ (d 1)) := by
  have hst : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hs0, ht0])
  rw [MvPowerSeries.coeff_subst hst]
  congr 1; funext d
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  rfl
end Formalism.ELL.FormalGroupPointsHom
