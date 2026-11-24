-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.nkCount_succ_fine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:49:50.090103+00:00
-- url     : https://prove2.me/submissions/02845858-8608-4a50-a572-3712a92ce5d4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_nkM_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_nkCount_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_exists_local_data
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localValuationFiltration_notMem_pow_vF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_absNorm_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_card_sub_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_two_le_absNorm


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
    nkCount h L 𝔭 (k + 1) n = Ideal.absNorm 𝔭 ^ (2 * finrank K V - 1) * nkCount h L 𝔭 k n := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, hHh, hD, hD0, hv⟩ := exists_local_data hF hs hd hL hLi h𝔭
  rw [nkCount_eq h h𝔭 b hb hH, nkCount_eq h h𝔭 b hb hH]
  change nkM 𝔭 (k + 1) H n = _ * nkM 𝔭 k H n
  rw [hv] at hk
  have key := nkM_succ hK h𝔭 hHh hD (notMem_pow_vF h𝔭 hD0) hn hk
  rw [Fintype.card_fin] at key
  have hN := absNorm_pos h𝔭
  rcases Nat.eq_zero_or_pos (finrank K V) with h0 | hpos
  · have e0 : 2 * finrank K V = 0 := by omega
    have e1 : 2 * finrank K V - 1 = 0 := by omega
    rw [e0, pow_zero, one_mul] at key
    rw [e1, pow_zero, one_mul]
    have h2 := two_le_absNorm h𝔭
    have hB : nkM 𝔭 k H n ≤ 1 :=
      (card_sub_le hK h𝔭 k _).trans (by rw [Fintype.card_fin, e0, mul_zero, pow_zero])
    have hAN : 2 * nkM 𝔭 (k + 1) H n ≤ nkM 𝔭 (k + 1) H n * Ideal.absNorm 𝔭 := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ h2
    have hA0 : nkM 𝔭 (k + 1) H n = 0 := by
      rw [key] at hAN
      omega
    rw [hA0, zero_mul] at key
    omega
  · have e : 2 * finrank K V = (2 * finrank K V - 1) + 1 := by omega
    rw [e, pow_succ] at key
    apply Nat.eq_of_mul_eq_mul_right hN
    rw [key]
    ring
end Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
