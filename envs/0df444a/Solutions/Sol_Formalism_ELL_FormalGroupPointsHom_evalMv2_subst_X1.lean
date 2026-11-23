-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.evalMv2_subst_X1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:49.500797+00:00
-- url     : https://prove2.me/submissions/314d768b-20e7-4c8d-a732-82db36e5378b

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_Wi


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
theorem _root_.solution (w : PowerSeries K) (a b : K) :
    evalMv2 (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) a b = evalPS w b := by
  classical
  rw [evalMv2_eq, evalPS]
  have hsupp : Function.support (term (w.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) a b)
      ⊆ Set.range (Finsupp.single (1 : Fin 2)) := by
    intro e he
    have := WeierstrassChordSeries.coeff_Wi w 1 e
    unfold WeierstrassChordSeries.Wi at this
    by_cases h : e = Finsupp.single 1 (e 1)
    · exact ⟨e 1, h.symm⟩
    · exfalso; apply he; simp [term, this, h]
  rw [← (Finsupp.single_injective (1 : Fin 2)).tsum_eq hsupp]
  congr 1; funext n
  have := WeierstrassChordSeries.coeff_Wi w 1 (Finsupp.single 1 n)
  unfold WeierstrassChordSeries.Wi at this
  simp [term, this]
end Formalism.ELL.FormalGroupPointsHom
