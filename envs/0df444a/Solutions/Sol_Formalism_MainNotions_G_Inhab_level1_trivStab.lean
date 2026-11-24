-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.level1_trivStab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:30:33.804803+00:00
-- url     : https://prove2.me/submissions/77f6c098-eae2-4c60-aeca-6e0aa6b1d4f5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_MainNotions_G_Inhab_lat1
import Theorems.Thm_Formalism_MainNotions_G_Inhab_line_inj
import Theorems.Thm_Formalism_MainNotions_G_Inhab_smul1

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
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) : (level1 h).TrivStab := by
  intro γ' L hL hγ
  obtain ⟨γ, rfl⟩ : ∃ γ : Multiplicative ℤ, γ = γ' := ⟨γ', rfl⟩
  obtain ⟨n, hn⟩ := lat1 h (L (0 : Fin 1)) (hL (0 : Fin 1))
  have h1 := smul1 h γ L n hn
  have h1' : line W (Qq := Qq) p n = line W p (Multiplicative.toAdd γ + n) := by
    rw [← h1, ← hn]; exact (congrFun hγ (0 : Fin 1)).symm
  have h2 : n = Multiplicative.toAdd γ + n := line_inj h h1'
  have h3 : Multiplicative.toAdd γ = 0 := by omega
  exact (Multiplicative.toAdd.injective h3 : γ = 1)
end Formalism.MainNotions.G.Inhab
