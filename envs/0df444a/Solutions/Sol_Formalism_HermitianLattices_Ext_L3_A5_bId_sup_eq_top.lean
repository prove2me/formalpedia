-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.bId_sup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:52.517116+00:00
-- url     : https://prove2.me/submissions/98dd267f-0b43-4e87-a206-a4966a7cda6d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution {v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ}
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}} (h𝔭 : 𝔭 ∉ v.support) : bId v ⊔ 𝔭.1 = ⊤ := by
  by_contra hne
  have hle : bId v ≤ 𝔭.1 := by
    have h1 : 𝔭.1 ≤ bId v ⊔ 𝔭.1 := le_sup_right
    have h2 := 𝔭.2.eq_of_le hne h1
    rw [h2]
    exact le_sup_left
  unfold bId Finsupp.prod at hle
  obtain ⟨𝔮, h𝔮, hle'⟩ := (Ideal.IsPrime.prod_le 𝔭.2.isPrime).mp hle
  have := 𝔭.2.isPrime
  have h3 : 𝔮.1 ≤ 𝔭.1 := Ideal.IsPrime.le_of_pow_le hle'
  have h4 : 𝔮.1 = 𝔭.1 := 𝔮.2.eq_of_le 𝔭.2.ne_top h3
  exact h𝔭 (Subtype.ext h4 ▸ h𝔮)
end Formalism.HermitianLattices.Ext.L3.A5
