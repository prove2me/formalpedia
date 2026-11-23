-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.t_MeanAmpJoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:26.474218+00:00
-- url     : https://prove2.me/submissions/f37efc96-c501-4f23-86ac-ab7e1893b8df

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_two_le_H
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_mean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
theorem _root_.solution : Formalism.FourierDecayAlt.PN.MeanAmpJoint := by
  intro hS4 _ Cl Nu L C1 C0 r k hb hN hM hU S
  unfold e7
  have hH : ∀ p, 1 ≤ L.H p := hb.2.1
  have hnn : ∀ p, 0 ≤ L.nn p := hb.2.2.2.2.1
  refine mean hS4 L C0 r (k - 2 * r - 5) _ (fun p => L.H p ^ (C1 * (r + 1) ^ 2))
    (fun p => if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)
    (fun p => one_le_pow₀ (hH p)) ?_ hb hM hU hN.1 hN.2 ?_ ?_ S
  · intro p
    show (1 : ℝ) ≤ if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1
    split_ifs
    · have : 1 ≤ L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := one_le_pow₀ (hH p)
      linarith
    · exact le_refl _
  · intro p
    show L.nn p ≤ (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1) * L.ngen p
    split_ifs with hp
    · exact hM.2 p hp
    · rw [one_mul, hM.1 p hp]
  · intro p
    show (if p ∈ L.Om then (4 : ℝ) else 1) * (L.H p ^ (C1 * (r + 1) ^ 2) *
      (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)) ≤
      L.H p ^ (C1 * (r + 1) ^ 2 + C0 * (r + 1) ^ 2 + 2 * (2 * r + 2) + 5)
    have e : L.H p ^ (C1 * (r + 1) ^ 2 + C0 * (r + 1) ^ 2 + 2 * (2 * r + 2) + 5) =
        L.H p ^ 5 * (L.H p ^ (C1 * (r + 1) ^ 2) * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    have hA : 1 ≤ L.H p ^ (C1 * (r + 1) ^ 2) := one_le_pow₀ (hH p)
    have hB : 1 ≤ L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := one_le_pow₀ (hH p)
    rw [e]
    split_ifs with hp
    · have h2 := two_le_H L hb p hp
      have h32 : (32 : ℝ) ≤ L.H p ^ 5 := by
        calc (32 : ℝ) = 2 ^ 5 := by norm_num
          _ ≤ L.H p ^ 5 := pow_le_pow_left₀ (by norm_num) h2 5
      have hpos : 0 ≤ L.H p ^ (C1 * (r + 1) ^ 2) * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by
        positivity
      calc 4 * (L.H p ^ (C1 * (r + 1) ^ 2) * (8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))))
          = 32 * (L.H p ^ (C1 * (r + 1) ^ 2) * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h32 hpos
    · have h5 : 1 ≤ L.H p ^ 5 := one_le_pow₀ (hH p)
      rw [one_mul, mul_one]
      nlinarith [mul_le_mul h5 hB zero_le_one (le_trans zero_le_one h5)]
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
