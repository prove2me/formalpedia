-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.W_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:33.70475+00:00
-- url     : https://prove2.me/submissions/ca9d1a73-8e33-420d-851e-4d45e7316e1f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_flatMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_op_listSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_op_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_expW_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_Lt_unit


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution : ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ F : Mat k r → E,
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) F → ∀ g ∈ GV k r,
      W w F g = ((expW w).map fun p => p.1 • W p.2 F g).sum := by
  have hmono : ∀ {m n : ℕ} (F : Mat k r → E), n ≤ m → CkOn ((m : ℕ) : ℕ∞) (GV k r) F →
      CkOn ((n : ℕ) : ℕ∞) (GV k r) F := by
    intro m n F hnm hF g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', heq⟩ := hF g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast hnm), heq⟩
  have hW_ck : ∀ w : List (Bool × Mat k r), AllLie w → ∀ (n : ℕ) (F : Mat k r → E),
      CkOn ((n + w.length : ℕ) : ℕ∞) (GV k r) F → CkOn ((n : ℕ) : ℕ∞) (GV k r) (W w F) := by
    intro w
    induction w with
    | nil =>
      intro _ n F hF
      simpa [W] using hF
    | cons x w ih =>
      intro hw n F hF
      have hw' : AllLie w := fun y hy => hw y (by simp [hy])
      have hlen : n + (x :: w).length = (n + 1) + w.length := by simp; omega
      rw [hlen] at hF
      exact ckOn_op n x.1 (ih hw' (n + 1) F hF) (hw x (by simp))
  have op_congr : ∀ (b : Bool) (Y : Mat k r) (H H' : Mat k r → E) (g : Mat k r), inLie k r Y →
      g ∈ GV k r → (∀ g' ∈ GV k r, H g' = H' g') → op b Y H g = op b Y H' g := by
    intro b Y H H' g hY hg h
    show deriv (fun t : ℝ => H (cv b Y t g)) 0 = deriv (fun t : ℝ => H' (cv b Y t g)) 0
    congr 1
    funext t
    exact h _ (cv_mem hY hg t)
  have swap : ∀ (L : List (ℝ × List (Bool × Mat k r))) (f : J k r → ℝ × List (Bool × Mat k r) → E),
      ∑ i, (L.map (f i)).sum = (L.map fun p => ∑ i, f i p).sum := by
    intro L f
    induction L with
    | nil => simp
    | cons p L ih => simp [Finset.sum_add_distrib, ih]
  intro w
  induction w with
  | nil =>
    intro _ F _ g _
    simp [W, expW]
  | cons x w ih =>
    intro hw F hF g hg
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : AllLie w := fun y hy => hw y (by simp [hy])
    have hlen : (x :: w).length = 1 + w.length := by simp [add_comm]
    rw [hlen] at hF
    have hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) (W w F) := hW_ck w hw' 1 F hF
    have hFw : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) F := hmono F (by omega) hF
    have hterm : ∀ i, op x.1 (Lt i) (W w F) g =
        ((expW w).map fun p => p.1 • op x.1 (Lt i) (W p.2 F) g).sum := by
      intro i
      rw [op_congr x.1 (Lt i) (W w F) (fun g' => ((expW w).map fun p => p.1 • W p.2 F g').sum) g
        (Lt_unit i).1 hg (fun g' hg' => ih hw' F hFw g' hg')]
      have hL := op_listSum (b := x.1) (Lt_unit i).1 ((expW w).map fun p => (p.1, W p.2 F)) ?_ g hg
      · simpa [List.map_map, Function.comp_def] using hL
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        obtain ⟨hplen, hunit⟩ := expW_mem w p hp
        exact hW_ck p.2 (fun y hy => (hunit y hy).1) 1 F (by rw [hplen]; exact hF)
    show op x.1 x.2 (W w F) g = _
    rw [op_expand x.1 hx hH hg, Finset.sum_congr rfl (fun i _ => by rw [hterm i])]
    have e1 : ∀ i, kc i x.2 • ((expW w).map fun p => p.1 • op x.1 (Lt i) (W p.2 F) g).sum =
        ((expW w).map fun p => kc i x.2 • p.1 • op x.1 (Lt i) (W p.2 F) g).sum := fun i => by
      rw [List.smul_sum, List.map_map]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => e1 i), swap, expW, list_sum_flatMap]
    congr 1
    apply List.map_congr_left
    intro p _
    rw [List.map_map, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = (kc i x.2 * p.1) • op x.1 (Lt i) (W p.2 F) g
    rw [mul_smul]
end Formalism.FourierDecayAlt.P.ListSumInequalities
