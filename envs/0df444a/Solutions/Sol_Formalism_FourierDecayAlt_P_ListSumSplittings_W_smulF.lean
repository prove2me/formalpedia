-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.W_smulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:12:41.728573+00:00
-- url     : https://prove2.me/submissions/09a86f2b-3238-4462-8430-417eb72f1084

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_splits_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_ckOn_mulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_op_smulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumSplittings_op_listSumF
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_flatMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution : ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ (f : Mat k r → ℂ) (H : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((w.length : ℕ) : ℕ∞) (GV k r) H → ∀ g ∈ GV k r,
      W w (fun g => f g • H g) g = ((splits w).map fun p => W p.1 f g • W p.2 H g).sum := by
  intro w
  induction w with
  | nil => intro _ f H _ _ g _; simp [splits, W_nil]
  | cons x w ih =>
    intro hw f H hf hH g hg
    have hw' : AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hx : inLie k r x.2 := hw x List.mem_cons_self
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f := ckOn_mono (by simp) hf
    have hH' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) H := ckOn_mono (by simp) hH
    rw [W_cons, op_congr x.1 hx (ih hw' f H hf' hH') g hg]
    have hCf : ∀ l : List (Bool × Mat k r), l.Sublist w → CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W l f) :=
      fun l hl => smooth_on_of_word_derivatives l (fun y hy => hw' y (hl.subset hy)) 1
        (ckOn_mono (by have := hl.length_le; simp; omega) hf)
    have hCH : ∀ l : List (Bool × Mat k r), l.Sublist w → CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W l H) :=
      fun l hl => smooth_on_of_word_derivatives l (fun y hy => hw' y (hl.subset hy)) 1
        (ckOn_mono (by have := hl.length_le; simp; omega) hH)
    rw [op_listSumF hx (fun p g' => W p.1 f g' • W p.2 H g') (splits w)
      (fun p hp => ckOn_mulF (hCf p.1 (splits_mem w p hp).1) (hCH p.2 (splits_mem w p hp).2)) g hg]
    rw [splits, list_sum_flatMap]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [op_smulF x.1 hx (hCf p.1 (splits_mem w p hp).1) (hCH p.2 (splits_mem w p hp).2) hg]
    simp [W_cons]
end Formalism.FourierDecayAlt.P.ListSumSplittings
