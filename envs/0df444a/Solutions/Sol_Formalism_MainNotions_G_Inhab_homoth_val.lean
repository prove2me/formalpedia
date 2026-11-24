-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.homoth_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:40:15.770187+00:00
-- url     : https://prove2.me/submissions/cca18c27-05f1-477e-bf56-20a778d902f0

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (γ : Multiplicative ℤ) :
    ((homoth h γ : GL (Fin 1) Qq) : Matrix (Fin 1) (Fin 1) Qq) =
      Matrix.scalar (Fin 1) ((p : Qq) ^ (Multiplicative.toAdd γ)) := by
  show (Matrix.scalar (Fin 1)) ((((zpowersHom Qqˣ (Units.mk0 (p : Qq) (p_ne h))) γ : Qqˣ)) : Qq) = _
  rw [zpowersHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]
end Formalism.MainNotions.G.Inhab
