-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.expandM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:49:06.168953+00:00
-- url     : https://prove2.me/submissions/54826f44-022a-4097-8975-eb8624ea125c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_loc_finsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_top_finsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_conv
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_sum_fun_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_spread
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_loc
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_fold_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_loc_of_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_top_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_top_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_PI_QnCovHat2W_sum_fun_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
theorem _root_.solution (y : Mat k r) (hy : y ∈ GV k r) : ∀ (t : ℕ) (f : Fin t → ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1))
    (Φ : Mat k r → E) (x : Mat k r), x ∈ GV k r → Loc (t : ℕ∞) Φ x →
    fold (Mc y) (List.ofFn f) Φ x = ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
      (∏ j, ((y⁻¹) (c j) (f j).2.1 * y (f j).2.2 (d j))) •
        fold (Msg k r) (List.ofFn fun j => ((f j).1, c j, d j)) Φ x := by
  intro t
  induction t with
  | zero =>
    intro f Φ x _ _
    simp [FourTermExpansion.fold_nil]
  | succ t ih =>
    intro f Φ x hx hloc
    obtain ⟨U, hU, hxU, hUl⟩ := loc_spread hloc
    have hle : ((t : ℕ) : ℕ∞) ≤ ((t + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ t
    have heq : ∀ z ∈ U, z ∈ GV k r → fold (Mc y) (List.ofFn fun j : Fin t => f j.succ) Φ z =
        (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1),
          (∏ j, ((y⁻¹) (c j) (f j.succ).2.1 * y (f j.succ).2.2 (d j))) •
            fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) z :=
      fun z hz hzG => ih (fun j => f j.succ) Φ z hzG (loc_mono hle (hUl z hz))
    have e1 : 1 + t = t + 1 := by omega
    have hF : ∀ c d : Fin t → Fin (2 * r + k + 1),
        Loc 1 (fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ) x := by
      intro c d
      have := FourTermExpansion.fold_loc (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) 1 Φ x
        (by rw [List.length_ofFn, e1]; exact hloc)
      simpa using this
    have hin : ∀ (G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ)
        (c : Fin t → Fin (2 * r + k + 1)),
        Loc 1 (fun z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x :=
      fun G c => loc_finsum _ _ _ (fun d _ => hF c d)
    have hΨ : ∀ G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ,
        Loc 1 (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x := fun G =>
      loc_of_eq (by funext z; simp)
        (loc_finsum Finset.univ (fun _ => (1 : ℂ)) (fun c z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) (fun c _ => hin G c))
    have hT : ∀ (G : (Fin t → Fin (2 * r + k + 1)) → (Fin t → Fin (2 * r + k + 1)) → ℂ) (v : ℂ)
        (a b : Fin (2 * r + k + 1)),
        Top (FourTermExpansion.LT (Msg k r)) v a b (fun z => ∑ c : Fin t → Fin (2 * r + k + 1),
          ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
            fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) x =
        ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          Top (FourTermExpansion.LT (Msg k r)) v a b (fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ) x := by
      intro G v a b
      have e : (fun z => ∑ c : Fin t → Fin (2 * r + k + 1), ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
          fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) =
          fun z => ∑ c ∈ Finset.univ, (1 : ℂ) • (fun c z => ∑ d : Fin t → Fin (2 * r + k + 1), G c d •
            fold (Msg k r) (List.ofFn fun j => ((f j.succ).1, c j, d j)) Φ z) c z := by
        funext z; simp
      rw [e, top_finsum (Msg k r) Finset.univ _ _ hx (fun c _ => hin G c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [one_smul, top_finsum (Msg k r) Finset.univ _ _ hx (fun d _ => hF c d)]
    rw [List.ofFn_succ, FourTermExpansion.fold_cons, FourTermExpansion.top_congr (Mc y) hU heq _ _ _ x hxU hx, conv y hy (hΨ _) hx]
    simp only [hT, sum_fun_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, FourTermExpansion.fold_cons,
      Finset.smul_sum, smul_smul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
