-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.telescope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:43:32.978946+00:00
-- url     : https://prove2.me/submissions/b21bd3b0-781c-4338-a717-f707e30f2157

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_inLie_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_rpow_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_append
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_pn_le_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_bound_scaled
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_mid_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_unit_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {F : Mat k r → E} {A c K ε : ℝ} {m : ℕ} (h : CCle A m F c) (hc : 0 ≤ c) (hK : 1 ≤ K)
    (φ : Bool × Mat k r → Bool × Mat k r) (hφ1 : ∀ x, (φ x).1 = x.1)
    (hφL : ∀ x, unitLie k r x.2 → inLie k r (φ x).2)
    (hφK : ∀ x, unitLie k r x.2 → ‖(φ x).2‖ ≤ K)
    (hφε : ∀ x, unitLie k r x.2 → ‖(φ x).2 - x.2‖ ≤ ε) :
    ∀ (w p : List (Bool × Mat k r)), (∀ x ∈ p, unitLie k r x.2) → (∀ x ∈ w, unitLie k r x.2) →
      LRt ((p ++ w).map Prod.fst) → (p ++ w).length ≤ m → ∀ g ∈ GV k r,
      gN g ^ A * ‖W (p ++ w.map φ) F g - W (p ++ w) F g‖ ≤ w.length * (K ^ m * ε * c) := by
  intro w
  induction w with
  | nil => intro p _ _ _ _ g _; simp
  | cons x w ih =>
    intro p hp hw ht hl g hg
    have hx : unitLie k r x.2 := hw x List.mem_cons_self
    have hw' : ∀ y ∈ w, unitLie k r y.2 := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hε : 0 ≤ ε := le_trans (norm_nonneg _) (hφε x hx)
    have hpL : AllLie p := fun y hy => (hp y hy).1
    have hqL : AllLie (w.map φ) := by
      intro y hy
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      exact hφL y' (hw' y' hy')
    have hlen : p.length + 1 + w.length ≤ m := by
      simp only [List.length_append, List.length_cons] at hl; omega
    have hδL : inLie k r ((φ x).2 - x.2) := inLie_sub (hφL x hx) hx.1

    have e1 : W (p ++ φ x :: w.map φ) F g =
        W (p ++ x :: w.map φ) F g + W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g := by
      have hφx : φ x = (x.1, x.2 + ((φ x).2 - x.2)) := by
        refine Prod.ext (hφ1 x) ?_
        simp
      have := W_mid_add p (w.map φ) x.1 hpL hqL hx.1 hδL
        (ckOn_mono (by simpa using hlen) h.1) g hg
      rw [← hφx] at this
      exact this
    have tags : ((p ++ (x.1, (φ x).2 - x.2) :: w.map φ).map Prod.fst) = (p ++ x :: w).map Prod.fst := by
      simp [List.map_append, List.map_map, Function.comp_def, hφ1]
    have b1 := bound_scaled h (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) (by rw [tags]; exact ht)
      (by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hpL y hy
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact hδL
          · exact hqL y hy)
      (by simp only [List.length_append, List.length_cons, List.length_map]; omega) g hg
    have hpn : pn (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) ≤ K ^ m * ε := by
      rw [pn_append, pn_cons]
      have h1 : pn p ≤ 1 := by
        have := pn_le_pow p 1 (fun y hy => unit_norm_le (hp y hy))
        simpa using this
      have h2 : pn (w.map φ) ≤ K ^ m := by
        refine le_trans (pn_le_pow (w.map φ) K ?_) (pow_le_pow_right₀ hK (by simp; omega))
        intro y hy
        obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
        exact hφK y' (hw' y' hy')
      calc pn p * (‖(φ x).2 - x.2‖ * pn (w.map φ)) ≤ 1 * (ε * K ^ m) :=
            mul_le_mul h1 (mul_le_mul (hφε x hx) h2 (pn_nonneg _) hε)
              (mul_nonneg (norm_nonneg _) (pn_nonneg _)) zero_le_one
        _ = K ^ m * ε := by ring
    have b2 := ih (p ++ [x])
      (by
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hp y hy
        · rw [List.mem_singleton.mp hy]; exact hx)
      hw' (by simpa using ht) (by simpa using hl) g hg
    simp only [List.append_assoc, List.singleton_append] at b2
    rw [List.map_cons, e1]
    have hsplit : W (p ++ x :: w.map φ) F g + W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g -
        W (p ++ x :: w) F g = W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g +
          (W (p ++ x :: w.map φ) F g - W (p ++ x :: w) F g) := by abel
    rw [hsplit]
    calc gN g ^ A * ‖W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g +
          (W (p ++ x :: w.map φ) F g - W (p ++ x :: w) F g)‖
        ≤ gN g ^ A * (‖W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g‖ +
          ‖W (p ++ x :: w.map φ) F g - W (p ++ x :: w) F g‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (gN_rpow_nonneg g A)
      _ = gN g ^ A * ‖W (p ++ (x.1, (φ x).2 - x.2) :: w.map φ) F g‖ +
          gN g ^ A * ‖W (p ++ x :: w.map φ) F g - W (p ++ x :: w) F g‖ := by ring
      _ ≤ K ^ m * ε * c + w.length * (K ^ m * ε * c) :=
          add_le_add (le_trans b1 (mul_le_mul_of_nonneg_right hpn hc)) b2
      _ = ((x :: w).length : ℝ) * (K ^ m * ε * c) := by
          simp only [List.length_cons]; push_cast; ring
end Formalism.FourierDecayAlt.P.B4
