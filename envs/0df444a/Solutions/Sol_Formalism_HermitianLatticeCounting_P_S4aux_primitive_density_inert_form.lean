-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.primitive_density_inert_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:11.642051+00:00
-- url     : https://prove2.me/submissions/cbd80a64-6c7b-4b88-9eed-d61bff067201

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_cnt_bounds
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : PrimDensityInertForm := by
  intro K L _ _ _ _ _ h2 n m Ph Gm hn hPh hherm hG
  classical
  have hq2 : (2 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hb := cnt_bounds Ph h2 hPh hherm m hn Gm hG
  have hset : {X : Fin m → Fin n → L | LinearIndependent L X ∧
      ∀ i j, ∑ k, ∑ l, X i k * Ph k l * X j l ^ Fintype.card K = Gm i j}
      = ↑(univ.filter fun X : Fin m → Fin n → L => LinearIndependent L X ∧
        ∀ a b, hB K Ph (X a) (X b) = Gm a b) := by
    ext X
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    rfl
  rw [hset, Set.ncard_coe_finset]
  set q : ℝ := (Fintype.card K : ℝ) with hq
  have hq0 : 0 < q := by linarith
  have hd : (q ^ 2) ^ m / q ^ n ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have h8 : (8 : ℝ) ≤ q ^ 3 := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := by gcongr
    have e : q ^ n = (q ^ 2) ^ m * q ^ (n - 2 * m) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have h3 : q ^ 3 ≤ q ^ (n - 2 * m) := pow_le_pow_right₀ (by linarith) (by omega)
    rw [e]
    have : 0 < (q ^ 2) ^ m := by positivity
    nlinarith
  have hd0 : 0 ≤ (q ^ 2) ^ m / q ^ n := by positivity
  have hQ : 0 ≤ q ^ (2 * n * m) / q ^ (m ^ 2) := by positivity
  constructor
  · refine le_trans ?_ hb.1
    nlinarith
  · refine le_trans hb.2 ?_
    nlinarith
end Formalism.HermitianLatticeCounting.P.S4aux
