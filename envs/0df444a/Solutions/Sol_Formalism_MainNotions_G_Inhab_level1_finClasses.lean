-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.level1_finClasses
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:30:31.026397+00:00
-- url     : https://prove2.me/submissions/31d5a55c-a940-479e-8a79-4cd6e4637c6a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_MainNotions_G_Inhab_lat1
import Theorems.Thm_Formalism_MainNotions_G_Inhab_line_isLattice
import Theorems.Thm_Formalism_MainNotions_G_Inhab_smul1
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) : (level1 h).FinClasses := by
  classical
  let L0 : (places1 h).Tup := fun _ => line W p 0
  refine ⟨{L0}, ?_, ?_⟩
  · intro L hL v
    rw [Finset.mem_singleton] at hL
    rw [hL]
    exact line_isLattice h 0
  · intro L hL
    obtain ⟨n, hn⟩ := lat1 h (L (0 : Fin 1)) (hL (0 : Fin 1))
    refine ⟨L0, Finset.mem_singleton_self _, Multiplicative.ofAdd n, ?_⟩
    funext v
    have hv : v = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) v 0
    subst hv
    have h1 := smul1 h (Multiplicative.ofAdd n) L0 0 rfl
    refine hn.trans (Eq.trans ?_ h1.symm)
    simp
end Formalism.MainNotions.G.Inhab
