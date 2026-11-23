-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.Ca_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:40.509569+00:00
-- url     : https://prove2.me/submissions/89953c85-857f-44e4-af42-8ff23eaf9772

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_C_mem_TT

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
open Formalism Formalism.ELL
open Formalism.ELL.CubeThreeAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {σ : Type}
namespace Formalism.ELL.CubeThreeAlt
theorem _root_.solution : (MvPowerSeries.C W.a₁ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₂ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₃ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₄ : MvPowerSeries σ K) ∈ TT W σ ∧
    (MvPowerSeries.C W.a₆ : MvPowerSeries σ K) ∈ TT W σ :=
  ⟨C_mem_TT (Algebra.subset_adjoin (by simp)), C_mem_TT (Algebra.subset_adjoin (by simp)),
    C_mem_TT (Algebra.subset_adjoin (by simp)), C_mem_TT (Algebra.subset_adjoin (by simp)),
    C_mem_TT (Algebra.subset_adjoin (by simp))⟩
end Formalism.ELL.CubeThreeAlt
