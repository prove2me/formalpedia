-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.subst_mem_T_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:29.716392+00:00
-- url     : https://prove2.me/submissions/bfab8559-a770-4b45-8558-2b53409d8b56

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo

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
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution {W : WeierstrassCurve K} {f : MvPowerSeries (Fin 2) K} (hf : f ∈ T W)
    {a : Fin 2 → MvPowerSeries (Fin 2) K} (ha : ∀ i, a i ∈ T W) (h0 : ∀ i, cc (a i) = 0) :
    f.subst a ∈ T W := by
  obtain ⟨fS, rfl⟩ := hf
  have ha' : ∀ i, ∃ y, MvPowerSeries.map (algebraMap (Sadj W) K) y = a i := fun i => ha i
  choose aS haS using ha'
  have hinj : Function.Injective (algebraMap (Sadj W) K) := fun x y h => Subtype.ext h
  have hS : MvPowerSeries.HasSubst aS := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    apply hinj
    rw [map_zero]
    have := congrArg MvPowerSeries.constantCoeff (haS i)
    rw [MvPowerSeries.constantCoeff_map, h0 i] at this
    exact this)
  refine ⟨fS.subst aS, ?_⟩
  rw [MvPowerSeries.map_subst hS]
  congr 1
  funext i
  exact haS i
end Formalism.ELL.CubeTwoAlt
