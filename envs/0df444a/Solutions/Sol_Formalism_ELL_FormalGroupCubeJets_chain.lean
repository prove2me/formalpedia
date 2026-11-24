-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:22.080999+00:00
-- url     : https://prove2.me/submissions/375ed752-15e2-4f5e-9dfa-345a060f341a

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_pderiv_zero_subst_three_variable_law
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_step2
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_step1
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_step0

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupCubeJets
open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable (F : FormalGroup (unitBall K))
namespace Formalism.ELL.FormalGroupCubeJets
theorem _root_.solution (φ : PowerSeries K) (k : ℕ) :
    (Dj F 0)^[k] (Dj F 0 (Dj F 1 (Dj F 2 (triDiff F φ)))) = ((invD F)^[k + 3] φ).subst (F3 F) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, step2, step1, step0]
    rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pderiv_zero_subst_three_variable_law]
    rw [← Function.iterate_succ_apply' (invD F) (k + 3) φ]
end Formalism.ELL.FormalGroupCubeJets
