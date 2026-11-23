-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.w_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:50.85584+00:00
-- url     : https://prove2.me/submissions/a85292be-24fe-4ab0-a46b-2dc68c5af917

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_mem_unitBall
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_coeff_mem


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
theorem _root_.solution {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W)
    (hw : WFixed W w) (n : ℕ) : ‖coeff n w‖ ≤ 1 := by
  have hsub : ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) ⊆
      (subalgebraOfSubring (unitBall K) : Set K) := by
    obtain ⟨h1, h2, h3, h4, h6⟩ := hW
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, mem_subalgebraOfSubring, SubstitutionCoefficientCongruence.mem_unitBall]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  exact SubstitutionCoefficientCongruence.mem_unitBall.mp
    (mem_subalgebraOfSubring.mp (Algebra.adjoin_le hsub (WeierstrassChordSeries.w_coeff_mem hw n)))
end Formalism.ELL.FormalGroupPointsHom
