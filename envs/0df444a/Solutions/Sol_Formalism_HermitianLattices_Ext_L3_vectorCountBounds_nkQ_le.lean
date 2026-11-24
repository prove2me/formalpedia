-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.vectorCountBounds.nkQ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:56.467656+00:00
-- url     : https://prove2.me/submissions/fefb2be6-d3a7-4c23-82d6-79fa4e576eff

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_card_sub_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_nkQ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_absNorm_pos


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) (n : 𝓞 F) (c : ℕ) (hm : 1 ≤ Fintype.card m) (k : ℕ) :
    nkQ 𝔭 k c H n ≤ Ideal.absNorm 𝔭 ^ (2 * c + 1) * Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1)) := by
  have hq := absNorm_pos h𝔭
  have small : ∀ k, k ≤ 2 * c + 1 → nkQ 𝔭 k c H n ≤
      Ideal.absNorm 𝔭 ^ (2 * c + 1) * Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1)) := by
    intro k hk
    refine (card_sub_le hK h𝔭 k _).trans ?_
    rw [← pow_add]
    apply Nat.pow_le_pow_right hq
    have : k * (2 * Fintype.card m) = k + k * (2 * Fintype.card m - 1) := by
      obtain ⟨M, hM⟩ : ∃ M, Fintype.card m = M + 1 := ⟨Fintype.card m - 1, by omega⟩
      rw [hM]
      have : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
      rw [this]; ring
    omega
  rcases le_total k (2 * c + 1) with hk | hk
  · exact small k hk
  · induction k, hk using Nat.le_induction with
    | base => exact small _ le_rfl
    | succ k hk ih =>
      have h1 := nkQ_succ hK h𝔭 hH n hk
      apply Nat.le_of_mul_le_mul_right _ hq
      rw [h1]
      calc Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkQ 𝔭 k c H n
          ≤ Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * (Ideal.absNorm 𝔭 ^ (2 * c + 1) *
            Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1))) := Nat.mul_le_mul_left _ ih
        _ = _ := by
          obtain ⟨M, hM⟩ : ∃ M, Fintype.card m = M + 1 := ⟨Fintype.card m - 1, by omega⟩
          rw [hM]
          have : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
          rw [this]
          ring
end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
