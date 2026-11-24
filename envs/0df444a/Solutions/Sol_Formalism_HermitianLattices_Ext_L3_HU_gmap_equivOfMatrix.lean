-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.gmap_equivOfMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:51:03.393282+00:00
-- url     : https://prove2.me/submissions/dfd56130-f7a3-4b2b-845d-d0fd72dca378

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mem_locF_iff_repr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_equivFun_equivOfMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_equivFun_equivOfMatrix_symm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_mulVec_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (G G' : Matrix κ κ K)
    (hG : G * G' = 1) (h1 : Ent (SP K 𝔭) G) (h2 : Ent (SP K 𝔭) G') :
    Formalism.HermitianLatticesTheory.gmap (equivOfMatrix b G G' hG) (locF 𝔭 (spanO b)) = locF 𝔭 (spanO b) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_locF_iff_repr]
    intro i
    have : b.equivFun (equivOfMatrix b G G' hG x) = G *ᵥ b.equivFun x := equivFun_equivOfMatrix b G G' hG x
    show b.equivFun (equivOfMatrix b G G' hG x) i ∈ _
    rw [this]
    exact mulVec_mem h1 ((mem_locF_iff_repr b x).1 hx) i
  · intro x hx
    refine ⟨(equivOfMatrix b G G' hG).symm x, ?_, (equivOfMatrix b G G' hG).apply_symm_apply x⟩
    show _ ∈ locF 𝔭 (spanO b)
    rw [mem_locF_iff_repr]
    intro i
    rw [equivFun_equivOfMatrix_symm]
    exact mulVec_mem h2 ((mem_locF_iff_repr b x).1 hx) i
end Formalism.HermitianLattices.Ext.L3.HU
