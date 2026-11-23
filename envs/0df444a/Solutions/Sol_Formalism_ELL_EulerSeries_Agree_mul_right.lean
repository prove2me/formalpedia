-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.Agree.mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:18.852716+00:00
-- url     : https://prove2.me/submissions/1d8374a2-9e66-4c00-8d42-bf2f142b98b7

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]
namespace Formalism.ELL.EulerSeries
namespace Agree
theorem _root_.solution {N : ℕ} {F G : MvPowerSeries σ K} (h : Agree N F G)
    (H : MvPowerSeries σ K) : Agree N (F * H) (G * H) := by
  intro d hd
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg := congrArg Finsupp.degree hp
  rw [map_add] at hdeg
  rw [h p.1 (by omega)]
end Agree
end Formalism.ELL.EulerSeries
