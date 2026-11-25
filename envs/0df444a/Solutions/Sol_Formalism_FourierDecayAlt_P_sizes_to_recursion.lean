-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.sizes_to_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:49:32.565898+00:00
-- url     : https://prove2.me/submissions/eb76afd8-6309-4f6d-a008-f10588d26d70

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : SizesToRecursion := by
  intro hS CA C0 CG CDel cT Cb C C' hCA hC0 hCG hCDel hcT hCb hcTb hC hCCA
  obtain ⟨k0, H⟩ := hS CA C0 CG CDel cT Cb hCA hC0 hCG hCDel hcT hCb hcTb
  have hc : 0 < Sz.cExp CDel cT Cb := by
    unfold Sz.cExp
    have : 0 < min ((CDel - 4) / 2) ((cT * Cb - 1) / 4) := lt_min (by linarith) (by linarith)
    positivity
  obtain ⟨k1, hk1⟩ := Filter.eventually_atTop.1
    (((tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (max C' 5))
  refine ⟨max k0 k1, ?_⟩
  intro ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := hyp
  obtain ⟨hTh, hrest⟩ := H ι G bb Cp Cf Th de de' T T' du du' l (le_trans (le_max_left _ _) hk)
    a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
  obtain ⟨ha, hb⟩ := hrest h16 hCf
  have hbig : max C' 5 ≤ Th := le_trans (hk1 G.k (le_trans (le_max_right _ _) hk)) hTh
  have hpow : (C / Th) ^ G.f ≤ (CA / Th) ^ G.f :=
    pow_le_pow_left₀ (div_nonneg hC a18.le) (div_le_div_of_nonneg_right hCCA a18.le) _
  have hp0 : 0 ≤ (C / Th) ^ G.f := pow_nonneg (div_nonneg hC a18.le) _
  have hr : (0:ℝ) ≤ G.r := Nat.cast_nonneg _
  have hb1 : (bb ^ 7)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ a1.hbb.le)
  have hx : ((G.r : ℝ) + 1) * (C / Th) ^ G.f ≤ ((G.r : ℝ) + 1) * (CA / Th) ^ G.f :=
    mul_le_mul_of_nonneg_left hpow (by linarith)
  have hx0 : 0 ≤ ((G.r : ℝ) + 1) * (C / Th) ^ G.f := mul_nonneg (by linarith) hp0
  have hb' : CA * (((G.r : ℝ) + 1) * (CA / Th) ^ G.f) ≤ (bb ^ 7)⁻¹ := by rw [← mul_assoc]; exact hb
  refine ⟨le_trans (le_max_left _ _) hbig, lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hbig), ?_, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_left hpow hr) ha
  · nlinarith
  · rw [mul_assoc]
    calc C * (((G.r : ℝ) + 1) * (C / Th) ^ G.f) ≤ CA * (((G.r : ℝ) + 1) * (CA / Th) ^ G.f) :=
          mul_le_mul hCCA hx hx0 (by linarith)
      _ ≤ _ := hb'
end Formalism.FourierDecayAlt.P
