-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.alphaN_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:59:18.997782+00:00
-- url     : https://prove2.me/submissions/eee96f4c-ea59-4f57-a745-475bc79a8762

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_firstFamilyOperatorEnd_limUnder_of_step
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_firstFamilyOperatorEnd_nkCount_succ_fine
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_absNorm_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms localValuationFiltration hermitianFormColumns vectorCountBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} {v : ℕ} (hn : n ∉ 𝔭 ^ (v + 1)) {k : ℕ}
    (hk : vd h L 𝔭 + v + 1 ≤ k) :
    alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  unfold alphaN
  exact limUnder_of_step (absNorm_pos h𝔭)
    (fun j hj => nkCount_succ_fine hK hF hs hd hL hLi h𝔭 hn hj) hk
end Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
