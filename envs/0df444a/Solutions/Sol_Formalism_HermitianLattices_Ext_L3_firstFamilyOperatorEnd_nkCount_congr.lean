-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.nkCount_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:27.177654+00:00
-- url     : https://prove2.me/submissions/85dce3be-73ed-4fd5-b032-776e9fa28127

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_mem_pow_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_nkCount_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_exists_local_data


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
theorem _root_.solution (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n n' : 𝓞 F} {k : ℕ} (hc : n - n' ∈ 𝔭 ^ k) :
    nkCount h L 𝔭 k n = nkCount h L 𝔭 k n' := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, nkCount_eq h h𝔭 b hb hH]
  have e : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι n) = Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι n') := by
    rw [Ideal.Quotient.eq, ← map_sub]
    exact (mem_pow_iff 𝔭 k _).mpr hc
  rw [e]
end Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
