-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cntI_add_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.731259+00:00
-- url     : https://prove2.me/submissions/2af185b8-92c7-40ea-b7e1-932440d1bf5c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mulW_injective
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_inQ_iff_range
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_norm_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_card_red

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {ϖ : 𝓞 F} (h1 : ϖ ∈ 𝔭) (h2 : ϖ ∉ 𝔭 ^ 2) (j M : ℕ) {n n' : 𝓞 K}
    (hn : n - ι ϖ ^ 2 * n' ∈ extP K 𝔭 ^ (j + 2)) :
    cntI hF 𝔭 (j + 2) M n = Ideal.absNorm 𝔭 ^ (2 * M) * cnt hF 𝔭 j M n' := by
  unfold cntI cnt
  rw [← card_red hK hF h𝔭 j M
    (fun y => ∑ i, sg hF 𝔭 j (y i) * y i = Ideal.Quotient.mk _ n')]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨fun i => mulW 𝔭 (map_mem h1) j (y.1 i),
    fun i => (inQ_iff_range h𝔭 h1 h2 j _).2 ⟨_, rfl⟩,
    (norm_iff hF h𝔭 h1 h2 j hn y.1).2 y.2⟩) ⟨?_, ?_⟩)
  · intro y y' h
    apply Subtype.ext
    funext i
    exact mulW_injective h𝔭 h1 h2 j (congrFun (congrArg Subtype.val h) i)
  · rintro ⟨x, hx1, hx2⟩
    choose y hy using fun i => (inQ_iff_range h𝔭 h1 h2 j _).1 (hx1 i)
    obtain rfl : (fun i => mulW 𝔭 (map_mem h1) j (y i)) = x := funext hy
    exact ⟨⟨y, (norm_iff hF h𝔭 h1 h2 j hn y).1 hx2⟩, rfl⟩
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
