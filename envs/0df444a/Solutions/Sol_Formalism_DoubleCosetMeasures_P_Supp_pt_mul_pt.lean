-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.pt_mul_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:52.066302+00:00
-- url     : https://prove2.me/submissions/3dbd6f5c-682f-4274-a56f-3acedf182264

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_revIn_lt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_revIn_revIn
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_blk_revIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp
namespace Formalism.DoubleCosetMeasures.P.Supp
theorem _root_.solution {K : Type} [CommRing K] (s : List ℕ) (t t' : ℕ → Kˣ)
    (htt : ∀ b, ((t b : Kˣ) : K) * ((t' b : Kˣ) : K) = 1) : pt s t * pt s t' = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have ha := revIn_lt s a a.isLt
  have hrr : revIn s (revIn s a) = a := revIn_revIn s a a.isLt
  have hbb : blk s (revIn s a) = blk s a := blk_revIn s a a.isLt
  rw [Finset.sum_eq_single ⟨revIn s a, ha⟩]
  · simp only [pt, hrr, hbb, if_true]
    by_cases hab : a = b
    · subst hab; simp [htt]
    · have hne : (b : ℕ) ≠ a := fun e => hab (Fin.ext e.symm)
      simp [hab, hne]
  · intro c _ hc
    simp only [pt]
    rw [if_neg (fun e => hc (Fin.ext e)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.DoubleCosetMeasures.P.Supp
