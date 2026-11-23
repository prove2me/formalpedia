-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.supp_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:27.355796+00:00
-- url     : https://prove2.me/submissions/4f40eace-bba5-4e23-aedb-a7feb6aa3ea6

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_blk_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_revIn_app
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_blk_app_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_revIn_app_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_blk_lt_length
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_minor_lemma
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.A5x7
section Supp
variable {K : Type} [CommRing K] (R : Subring K)
private theorem revIn_lt_sum_of_lt_sum : ∀ (l : List ℕ) (j : ℕ), j < l.sum → revIn l j < l.sum := by
  intro l
  induction l with
  | nil => intro j hj; simp at hj
  | cons a l ih =>
    intro j hj
    rw [List.sum_cons] at hj ⊢
    simp only [revIn]
    split_ifs with h
    · omega
    · have := ih (j - a) (by omega)
      omega
end Supp
end Formalism.FourierDecayAlt.P.A5x7
namespace Formalism.FourierDecayAlt.P.A5x7
section Ones
variable {K : Type} [CommRing K] (R : Subring K)
end Ones
end Formalism.FourierDecayAlt.P.A5x7
namespace Formalism.FourierDecayAlt.P.A5x7
section Padic
variable (p : ℕ) [hp : Fact p.Prime]
end Padic
end Formalism.FourierDecayAlt.P.A5x7
end

set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution (h : Point K) (s : ℕ) (hs : 1 ≤ s) (t : Kˣ)
    (p : lowW K (addBlock h s t).1 (addBlock h s t).2 × upUniG K (addBlock h s t).1.sum)
    (hI : IsInt R (orbZ (addBlock h s t) p)) : (pt h.1 h.2).det * (t : K) ∈ R := by
  obtain ⟨hv, _⟩ := p.1.2
  have hu := p.2.2
  have hsum : (h.1 ++ [s]).sum = h.1.sum + s := by simp
  have hmn : h.1.sum < (addBlock h s t).1.sum := by
    show h.1.sum < (h.1 ++ [s]).sum
    omega
  refine minor_lemma R hmn _ (pt (addBlock h s t).1 (addBlock h s t).2) _ (pt h.1 h.2) (t : K)
    hv hu ?_ ?_ hI
  · intro a b ha
    have hrev := revIn_lt_sum_of_lt_sum h.1 a.val ha
    show (if (b : ℕ) = revIn (h.1 ++ [s]) a then
        ((Function.update h.2 h.1.length t (blk (h.1 ++ [s]) a) : Kˣ) : K) else 0) = _
    rw [revIn_app_lt s h.1 a.val ha, blk_app_lt s h.1 a.val ha, Function.update_apply,
      if_neg (ne_of_lt (blk_lt_length h.1 a.val ha))]
    by_cases hb : b.val < h.1.sum
    · rw [dif_pos hb]
      rfl
    · have hne : ¬ ((b : ℕ) = revIn h.1 a) := fun hc => hb (by rw [hc]; exact hrev)
      rw [dif_neg hb, if_neg hne]
  · intro a b ha
    show (if (b : ℕ) = revIn (h.1 ++ [s]) a then
        ((Function.update h.2 h.1.length t (blk (h.1 ++ [s]) a) : Kˣ) : K) else 0) =
      if (b : ℕ) + 1 = (h.1 ++ [s]).sum then (t : K) else 0
    rw [ha, revIn_app h.1 s hs, blk_app h.1 s hs, Function.update_apply, if_pos rfl]
    split_ifs <;> first | rfl | omega
end Formalism.FourierDecayAlt.P.A5x7
