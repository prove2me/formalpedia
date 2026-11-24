-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localValuationFiltration.bddAbove_vF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:00.118794+00:00
-- url     : https://prove2.me/submissions/3204e25a-e6a4-4f4c-b060-5cf24dfe4591

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_ne_bot


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localValuationFiltration
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.localValuationFiltration
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := by
  refine ⟨Ideal.absNorm (Ideal.span {n}), fun e he => ?_⟩
  have h1 : 𝔭 ^ e ∣ Ideal.span {n} := Ideal.dvd_span_singleton.mpr he
  have h2 : Ideal.absNorm (𝔭 ^ e) ∣ Ideal.absNorm (Ideal.span {n}) := map_dvd Ideal.absNorm h1
  have h3 : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hn
  have h4 := Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2
  rw [map_pow] at h4
  have h5 : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact idealPowerSpanBounds.ne_bot h𝔭
  have h6 : Ideal.absNorm 𝔭 ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact h𝔭.ne_top
  have h7 : 2 ≤ Ideal.absNorm 𝔭 := by omega
  have h8 : e < 2 ^ e := by
    first
    | exact Nat.lt_two_pow_self
    | exact Nat.lt_two_pow e
    | exact Nat.lt_pow_self (by norm_num) e
    | exact Nat.lt_pow_self (by norm_num)
  calc e ≤ 2 ^ e := h8.le
    _ ≤ Ideal.absNorm 𝔭 ^ e := Nat.pow_le_pow_left h7 e
    _ ≤ _ := h4
end Formalism.HermitianLattices.Ext.L3.localValuationFiltration
