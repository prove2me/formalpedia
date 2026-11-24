-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.lat1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:00:12.896149+00:00
-- url     : https://prove2.me/submissions/5087d556-9623-486e-b93b-d6deaa7046e6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_MainNotions_G_Inhab_decomp
import Theorems.Thm_Formalism_MainNotions_G_Inhab_colSpan_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


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
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (L : Submodule W (Fin 1 → Qq)) (hL : IsLattice W L) :
    ∃ n : ℤ, L = line W p n := by
  obtain ⟨g, hg, rfl⟩ := hL
  rw [Matrix.det_fin_one] at hg
  obtain ⟨n, u, hx⟩ := decomp h (g 0 0) hg.ne_zero
  refine ⟨n, ?_⟩
  rw [colSpan_one, hx, line]
  have : (fun _ : Fin 1 => algebraMap W Qq (u : W) * (p : Qq) ^ n) = (u : W) • (fun _ : Fin 1 => (p : Qq) ^ n) := by
    funext i
    rw [Pi.smul_apply, Algebra.smul_def]
  rw [this]
  exact Submodule.span_singleton_smul_eq u.isUnit _
end Formalism.MainNotions.G.Inhab
