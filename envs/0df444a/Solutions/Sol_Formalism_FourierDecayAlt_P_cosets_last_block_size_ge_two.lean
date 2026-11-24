-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cosets_last_block_size_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:29.401406+00:00
-- url     : https://prove2.me/submissions/26a77b16-c628-4196-a2d3-8a664ec926f4

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramConjugationNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_isPt_PT
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_gram_dom
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramConjugationNorm_avg_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt.TA Formalism.FourierDecayAlt.P.GramConjugationNorm
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TA.CosetsS := by
  intro E _ _ H _ _ W _ len Kl Nw D Sg Φ bd4 i s w R hNZ hs hsi hir hK hA hE hb hEst hw hR
  classical
  obtain ⟨th, hth, hest⟩ := hEst w hw
  obtain ⟨hA1, -, -, hA4⟩ := hA i s (by omega) hsi hir
  have hHd : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h := isPt_PT Sg hNZ _
  have he : 0 ≤ 1 + D.e i := by have := (hE i (by omega) hir).1; linarith
  have step1 : Cosets D Sg Φ w i s R ≤
      ∑ t0 ∈ R, bd4 * ∑ w', th w' * (gram (D.Th i s t0) (Φ w') (PT Sg (i - s))).re := by
    unfold Cosets
    refine Finset.sum_le_sum fun t0 _ => ?_
    exact hest _ _ hHd (hA1 t0 _ hHd) t0 _ (fun t ht => by
      rw [Finset.mem_filter] at ht; exact ⟨hNZ _ _ t ht.1, ht.2⟩)
  have step2 := avg_le R len (len w + (s + 1) * Kl) th hth
    (fun t0 w' => (gram (D.Th i s t0) (Φ w') (PT Sg (i - s))).re)
    (fun w' => Slev D Sg Φ w' (i - s)) (1 + D.e i) he
    (fun w' => gram_dom R (1 + D.e i) (D.K (i - s)) (D.Th i s) (Φ w') _ (hA4 R _ hR hHd))
  calc Cosets D Sg Φ w i s R
      ≤ ∑ t0 ∈ R, bd4 * ∑ w', th w' * (gram (D.Th i s t0) (Φ w') (PT Sg (i - s))).re := step1
    _ = bd4 * ∑ t0 ∈ R, ∑ w', th w' * (gram (D.Th i s t0) (Φ w') (PT Sg (i - s))).re := by
        rw [Finset.mul_sum]
    _ ≤ bd4 * ((1 + D.e i) * wsup len (len w + (s + 1) * Kl) (fun w' => Slev D Sg Φ w' (i - s))) :=
        mul_le_mul_of_nonneg_left step2 hb
    _ = _ := by ring
end Formalism.FourierDecayAlt.P
