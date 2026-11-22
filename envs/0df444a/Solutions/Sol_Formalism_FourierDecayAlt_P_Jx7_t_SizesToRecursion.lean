-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_SizesToRecursion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:32.135506+00:00
-- url     : https://prove2.me/submissions/4ce26985-bc45-470d-99ba-d732f6dcb402

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : SizesToRecursion := by
  intro hS CA C0 CG CDel cT Cb C C' hCA hC0 hCG hCDel hcT hCb hcTb hC hCCA
  obtain ⟨k0, hk0⟩ := hS CA C0 CG CDel cT Cb hCA hC0 hCG hCDel hcT hCb hcTb
  have hc : 0 < Sz.cExp CDel cT Cb := by
    unfold Sz.cExp
    have : 0 < min ((CDel - 4) / 2) ((cT * Cb - 1) / 4) := lt_min (by linarith) (by linarith)
    positivity
  have hMpos : 0 < max C' 5 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨max k0 (⌈(max C' 5) ^ (1 / Sz.cExp CDel cT Cb)⌉₊), ?_⟩
  intro ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16', h17, h18, h19⟩ := hyp
  have hmain := hk0 ι G bb Cp Cf Th de de' T T' du du' l (le_trans (le_max_left _ _) hk) h1 h2 h3 h4 h5
    h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16' h17 h18 h19
  obtain ⟨hTh, hrest⟩ := hmain
  obtain ⟨hr1, hr2⟩ := hrest h16 hCf
  have hkM : (max C' 5) ^ (1 / Sz.cExp CDel cT Cb) ≤ (G.k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)
  have hMle : max C' 5 ≤ (G.k : ℝ) ^ Sz.cExp CDel cT Cb := by
    calc max C' 5 = ((max C' 5) ^ (1 / Sz.cExp CDel cT Cb)) ^ Sz.cExp CDel cT Cb := by
          rw [← Real.rpow_mul hMpos.le, one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hkM hc.le
  have hMTh : max C' 5 ≤ Th := le_trans hMle hTh
  have hpow : (C / Th) ^ G.f ≤ (CA / Th) ^ G.f :=
    pow_le_pow_left₀ (div_nonneg hC h18.le) (div_le_div_of_nonneg_right hCCA h18.le) _
  have hpn : 0 ≤ (C / Th) ^ G.f := pow_nonneg (div_nonneg hC h18.le) _
  have hbb : (bb ^ 7)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1.hbb.le)
  have hr0 : (0 : ℝ) ≤ G.r := Nat.cast_nonneg _
  have hA1 : ((G.r : ℝ) + 1) * (CA / Th) ^ G.f ≤ CA * ((G.r : ℝ) + 1) * (CA / Th) ^ G.f := by
    have : 0 ≤ ((G.r : ℝ) + 1) * (CA / Th) ^ G.f :=
      mul_nonneg (by linarith) (le_trans hpn hpow)
    nlinarith
  refine ⟨le_trans (le_max_left _ _) hMTh, lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hMTh),
    le_trans (mul_le_mul_of_nonneg_left hpow hr0) hr1, ?_, ?_⟩
  · calc ((G.r : ℝ) + 1) * (C / Th) ^ G.f ≤ ((G.r : ℝ) + 1) * (CA / Th) ^ G.f :=
          mul_le_mul_of_nonneg_left hpow (by linarith)
      _ ≤ _ := hA1
      _ ≤ _ := hr2
      _ ≤ 1 := hbb
  · calc C * ((G.r : ℝ) + 1) * (C / Th) ^ G.f ≤ CA * ((G.r : ℝ) + 1) * (CA / Th) ^ G.f := by
          apply mul_le_mul _ hpow hpn (by positivity)
          exact mul_le_mul_of_nonneg_right hCCA (by linarith)
      _ ≤ _ := hr2
end Formalism.FourierDecayAlt.P.Jx7
