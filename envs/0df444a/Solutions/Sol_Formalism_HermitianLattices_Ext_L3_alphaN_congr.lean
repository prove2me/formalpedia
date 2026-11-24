-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.alphaN_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:29.445795+00:00
-- url     : https://prove2.me/submissions/506d3c56-e1a0-4e8a-b711-4a0f49ac16f3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_firstFamilyOperatorEnd_alphaN_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_firstFamilyOperatorEnd_nkCount_congr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n n' : 𝓞 F} (hn : n ≠ 0)
    {k : ℕ} (hk : vF 𝔭 n + 2 * vd h L 𝔭 + 2 ≤ k) (hc : n - n' ∈ 𝔭 ^ k) :
    alphaN h L 𝔭 n = alphaN h L 𝔭 n' := by
  have hn1 := localValuationFiltration.notMem_pow_vF h𝔭 hn
  have hn1' : n' ∉ 𝔭 ^ (vF 𝔭 n + 1) := by
    intro h'
    apply hn1
    have hk' : 𝔭 ^ k ≤ 𝔭 ^ (vF 𝔭 n + 1) := Ideal.pow_le_pow_right (by omega)
    have := Ideal.add_mem _ (hk' hc) h'
    simpa using this
  rw [firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 hn1 (k := k) (by omega),
    firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 hn1' (k := k) (by omega),
    firstFamilyOperatorEnd.nkCount_congr hF hs hd hL hLi h𝔭 hc]
end Formalism.HermitianLattices.Ext.L3
