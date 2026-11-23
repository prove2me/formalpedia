-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.side_condition_of_windows
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:35.728428+00:00
-- url     : https://prove2.me/submissions/efcc44cf-b4f4-4e99-bba1-ddc913d6ab21

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_x1__a3dada
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_X1
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_Xpos__19fb6e
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_sb1
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_bpos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_sb_le_b
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_npos
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_n1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : SideConditionsOfWindows := by
  intro P e K hW hL
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hx := F.hx
  have hvpos : 0 < v := by
    have h : 0 < v * X := by rw [F.hvX]; exact F.bpos
    exact (pos_iff_pos_of_mul_pos h).2 F.Xpos
  have hx2 : P.x ≤ P.x ^ 2 := by
    calc P.x = P.x ^ 1 := (pow_one _).symm
      _ ≤ P.x ^ 2 := pow_le_pow_right₀ F.x1 (by norm_num)
  have hx4 : P.x ≤ P.x ^ 4 := by
    calc P.x = P.x ^ 1 := (pow_one _).symm
      _ ≤ P.x ^ 4 := pow_le_pow_right₀ F.x1 (by norm_num)
  have hw0 : 0 < P.wpp := by rw [F.hwpp]; exact div_pos hvpos F.npos
  have hb1 : 1 ≤ P.b := F.sb1.trans F.sb_le_b
  have hw8 : 0 < w8 := by linarith [F.w81]
  have hbp0 : 0 ≤ P.bp := by rw [F.hbp]; exact mul_nonneg F.xpos.le F.v0
  refine ⟨hw0, F.th0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, F.C0, ?_, ?_, ?_, ?_, F.lx0, F.La0, ?_, ?_, by rw [F.hXp]; exact F.hXpp⟩
  · have h1 : P.x⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hx
    have := F.thx
    norm_num at h1
    linarith
  · rw [F.hXpp]
    have h1 : 1 ≤ P.n * X := one_le_mul_of_one_le_of_one_le F.n1 F.X1
    have h2 : P.x * 1 ≤ P.x * (P.n * X) := mul_le_mul_of_nonneg_left h1 F.xpos.le
    have h3 : P.x * P.n * X = P.x * (P.n * X) := by ring
    linarith
  · rw [F.hXpp, F.hwpp, F.ha, ← F.hvX]
    have := F.npos.ne'
    field_simp
  · rw [F.ha]; exact one_le_mul_of_one_le_of_one_le F.x1 hb1
  · rw [F.hXp]; exact F.X1
  · have h1 : (3 : ℝ) ≤ (P.p₀ : ℝ) := by linarith [F.px]
    exact_mod_cast h1
  · have h1 : (4 : ℝ) ≤ (P.d : ℝ) := by linarith [F.dx]
    exact_mod_cast h1
  · unfold Par.f; linarith [F.npos]
  · unfold Par.Sk; linarith [F.Sc0, F.η0, F.kx]
  · unfold Par.Q₁
    have := F.C0; have := F.r0; have := F.lx0
    positivity
  · unfold Par.Q₂
    rw [F.hδ, div_inv_eq_mul]
    have := F.C0; have := F.lx0; have := F.η0; have := F.Sc0; have := F.t0; have := F.bo0
    have := F.xpos
    positivity
  · linarith [F.kx]
  · linarith [F.x_sq_le_threshold]
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
