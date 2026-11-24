-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.pair_induction_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:54:50.585925+00:00
-- url     : https://prove2.me/submissions/5bc6370d-4988-40dc-bae0-0fdf9c561e62

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PstScalMem
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_tieP_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_pst_scal_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_decomp
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_harmonicProjection_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : PairStep := by
  intro p _ σ r w e zv sv hr hz o n z L u Λ h1 h2 hu l hl x hx
  constructor
  · rw [decomp w e zv sv hr hz (o - l) (n - l) z x (h1 l x hx), Finset.mul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    simp only [mem_range] at hm
    refine Submodule.subset_span ⟨l + m, by omega,
      ((1 : ℚ_[p]) * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) *
        (((o - l + (n - l) + r + z - m).choose m : ℕ) : ℚ_[p]))⁻¹) • (tieF w e ^ m) x, ?_, ?_⟩
    · refine pst_scal_mem (Λ (l + m)) (r * L) u m _ m (by omega) ?_ 1 (by simp) _ (h2 l m (by omega) x hx)
      exact le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu
    · rw [Nat.sub_sub, Nat.sub_sub, one_mul, mul_smul, tieP_smul w e zv sv _ _ _ ((p : ℚ_[p]) ^ u),
        mul_smul_comm, pow_add, mul_assoc]
  · rw [harmonicProjection_expand w e zv sv hz, Finset.mul_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    by_cases hmm : min (o - l) (n - l) < m
    · rw [h1 l x hx m hmm]
      simp
    · refine Submodule.subset_span ⟨l + m, by omega,
        ((-1 : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ u * (((m.factorial : ℚ_[p]) ^ 2) *
          (((o - l + (n - l) + r + z - 1).choose m : ℕ) : ℚ_[p]))⁻¹) • (tieF w e ^ m) x, ?_, ?_⟩
      · refine pst_scal_mem (Λ (l + m)) (r * L) u m _ m (by omega) ?_ _ (by simp) _ (h2 l m (by omega) x hx)
        exact le_trans (Nat.add_le_add_left (Nat.log_mono_right (by omega)) _) hu
      · simp only [smul_eq_C_mul, div_eq_mul_inv, map_mul]
        ring
end Formalism.InvariantFactorPaths.KP.LL
