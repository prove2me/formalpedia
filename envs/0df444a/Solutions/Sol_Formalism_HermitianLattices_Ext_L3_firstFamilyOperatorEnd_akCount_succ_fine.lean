-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.akCount_succ_fine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:42:55.964203+00:00
-- url     : https://prove2.me/submissions/1fbcde68-10c1-4613-a4a6-bfe930d0e2b3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_akCount_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_akM_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_exists_local_data
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF


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
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 2 * vd h L 𝔭 + 1 ≤ k) :
    akCount h L 𝔭 (k + 1) = Ideal.absNorm 𝔭 ^ (finrank K V ^ 2) * akCount h L 𝔭 k := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [akCount_eq h h𝔭 b hb hH, akCount_eq h h𝔭 b hb hH]
  rw [hv] at hk
  have key := akM_succ hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) hk
  rw [Fintype.card_fin, ← sq] at key
  exact key
end Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
