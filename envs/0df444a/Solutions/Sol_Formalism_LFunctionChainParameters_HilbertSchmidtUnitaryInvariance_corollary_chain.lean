-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.corollary_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:00:12.81781+00:00
-- url     : https://prove2.me/submissions/9d087b3b-cf5d-4e9a-bb67-86987e13a28d

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_dim
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_corollary_transport
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_wordCount_valid
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_compressDiagDefectBound
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_compressTraceSquareBound
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
theorem _root_.solution : CorChain := by
  intro ι _ Dall D D1 d r Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam h
  obtain ⟨hga, hDs, hs, hs20, hC, hG, hcard, hd, a1, a2, a3, a4, a5, hS, hVr, hde0, hde, hcor, hc,
    hV, hU, hJ, hdel, hD, -, -, hMI⟩ := h
  have hR := wordCount_valid ι d C0 Gam sg Dstar hC hG hs hDs.le hcard hd
  have f1 := compressTraceSquareBound ι Dall d r Pf Vr ga Dstar sg η0 η1 e0 de hVr (fun u => (hga u).le) hDs hs
    hs20 hR a1 a2 a3 a4 a5 hde0 hde hcor hS
  obtain ⟨fR, f2⟩ := compressDiagDefectBound ι Dall d r Pf Vr ga de e0 hVr (by linarith) a4 hS.2.1 hcor
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := corollary_transport ι Dall D D1 r (Bram Pf Vr) ga c V U J J1 A
    Y' Y _ _ del hga hc hV hU hJ hdel hD hMI f1 f2
  have he : 2 * e0 ≤ 1 / 4 := by
    have hsq : Real.sqrt e0 ^ 2 = e0 := Real.sq_sqrt a4
    have h0 := Real.sqrt_nonneg e0
    nlinarith
  have hRd : 0 < Rs d := lt_of_lt_of_le (div_pos hDs hs) hR
  have hDall : 0 < Dall := by
    rcases Nat.eq_zero_or_pos Dall with h0 | h0
    · exfalso
      subst h0
      have hz : ∀ u, (d u : ℝ) ≤ 0 := by
        intro u
        have hK : Kd Pf ga u = 0 := by
          unfold Kd Kp
          have : (Pf u)ᴴ * Pf u = 0 := by ext i j; simp [Matrix.mul_apply]
          rw [this, smul_zero]
        have h1 := hS.2.1 u
        have h2 : hsSq (0 - 1 : Matrix (Fin (d u)) (Fin (d u)) ℂ) = (d u : ℝ) := by
          rw [← hsSq_one (d u)]; simp [hsSq]
        rw [hK, h2] at h1
        have h3 : (0 : ℝ) ≤ (d u : ℝ) := Nat.cast_nonneg _
        nlinarith
      have : Rs d ≤ 0 := by
        unfold Rs; exact Finset.sum_nonpos fun u _ => hz u
      linarith
    · exact h0
  refine ⟨c1, c2, c3, c4, he, c5, c6, ?_, ?_, by linarith, hDall, ?_⟩
  · have h3 : 0 < (1 - de) * Rs d := mul_pos (by linarith) hRd
    linarith
  · have := Real.sqrt_nonneg de
    linarith
  · have h1 : (D : ℝ) ≤ (Dall : ℝ) := by
      rw [frame_dim J J1 hJ]; push_cast
      have : (0 : ℝ) ≤ (D1 : ℝ) := Nat.cast_nonneg _
      linarith
    have h2 : (0 : ℝ) < (Dall : ℝ) := by exact_mod_cast hDall
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
