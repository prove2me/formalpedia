-- Prove2me | solution 1 for Formalism.ELL.CubeThreeAlt.psubst_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:38.378737+00:00
-- url     : https://prove2.me/submissions/5d70ab8a-bc1b-498f-9b0a-eac2a434f28d

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_mem_TT
import Theorems.Thm_Formalism_ELL_CubeThreeAlt_subst_mem

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
theorem _root_.solution {f : PowerSeries K} (hf : ∀ n, coeff n f ∈ Sadj W)
    {a : MvPowerSeries σ K} (ha : a ∈ TT W σ) (ha0 : cc a = 0) : f.subst a ∈ TT W σ := by
  have hfU : (f : MvPowerSeries Unit K) ∈ TT W Unit := by
    rw [mem_TT]
    intro e
    have he : e = Finsupp.single () (e ()) := by
      ext
      simp
    rw [he]
    exact hf (e ())
  exact subst_mem hfU (fun _ => ha) (fun _ => ha0)
end Formalism.ELL.CubeThreeAlt
