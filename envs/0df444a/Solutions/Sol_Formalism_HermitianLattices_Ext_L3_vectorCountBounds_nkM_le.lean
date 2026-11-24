-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.vectorCountBounds.nkM_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:50:24.019541+00:00
-- url     : https://prove2.me/submissions/92104253-81a2-471e-a46f-c4427e645d35

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_card_sub_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_two_le_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_nkQ_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_nkM_eq_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_nkB_le
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
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {d : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (hm : 2 ≤ Fintype.card m) (k : ℕ) : ∀ n : 𝓞 F,
    nkM 𝔭 k H n ≤ 2 * Ideal.absNorm 𝔭 ^ (2 * d + 1) *
      Ideal.absNorm 𝔭 ^ (k * (2 * Fintype.card m - 1)) := by
  have hq := absNorm_pos h𝔭
  have hq2 := two_le_absNorm h𝔭
  obtain ⟨M, hM⟩ : ∃ M, Fintype.card m = M + 2 := ⟨Fintype.card m - 2, by omega⟩
  have hM' : 2 * (M + 2) - 1 = 2 * M + 3 := by omega
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n
    rcases le_or_gt k (2 * d + 1) with hk | hk
    · refine (card_sub_le hK h𝔭 k _).trans ?_
      rw [hM, hM', mul_assoc, ← pow_add]
      refine le_trans ?_ (Nat.le_mul_of_pos_left _ (by norm_num))
      apply Nat.pow_le_pow_right hq
      have : k * (2 * (M + 2)) = k + k * (2 * M + 3) := by ring
      omega
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      obtain ⟨n', hn'⟩ := nkB_le hK h𝔭 hH hD hDd n k' (by omega)
      have h1 := nkQ_le hK h𝔭 hH n d (by omega) (k' + 2)
      have h2 := ih k' (by omega) n'
      rw [nkM_eq_add h𝔭 (k' + 2) d H n]
      rw [hM, hM'] at *
      have h3 : nkB 𝔭 (k' + 2) d H n ≤ Ideal.absNorm 𝔭 ^ (2 * d + 1) *
          Ideal.absNorm 𝔭 ^ ((k' + 2) * (2 * M + 3)) := by
        refine hn'.trans ((Nat.mul_le_mul_left _ h2).trans ?_)
        have e1 : Ideal.absNorm 𝔭 ^ ((k' + 2) * (2 * M + 3)) = Ideal.absNorm 𝔭 ^ (2 * (M + 2)) *
            Ideal.absNorm 𝔭 * Ideal.absNorm 𝔭 ^ (2 * M + 1) * Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3)) := by
          rw [← pow_succ, ← pow_add, ← pow_add]
          congr 1
          ring
        rw [e1]
        have h4 : 1 ≤ Ideal.absNorm 𝔭 ^ (2 * M + 1) := Nat.one_le_pow _ _ hq
        calc Ideal.absNorm 𝔭 ^ (2 * (M + 2)) * (2 * Ideal.absNorm 𝔭 ^ (2 * d + 1) *
              Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3)))
            = Ideal.absNorm 𝔭 ^ (2 * d + 1) * (Ideal.absNorm 𝔭 ^ (2 * (M + 2)) * 2 * 1 *
              Ideal.absNorm 𝔭 ^ (k' * (2 * M + 3))) := by ring
          _ ≤ _ := by gcongr
      calc nkQ 𝔭 (k' + 2) d H n + nkB 𝔭 (k' + 2) d H n ≤ _ := Nat.add_le_add h1 h3
        _ = _ := by ring
end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
