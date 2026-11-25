-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftToRightConversion.twoSided
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:38:27.701802+00:00
-- url     : https://prove2.me/submissions/af1a555f-02bc-4a9f-ae6c-8715c9f57aca

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_tw_word
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_gN_rpow_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_length_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_of_tags
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_W_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_bw_tags
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_expW_coef
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_expW_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_expW_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_lr_tags
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_norm_list_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_one_le_Kc


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LeftToRightConversion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LeftToRightConversion
theorem _root_.solution : C2.TwoSided := by
  intro k r E _ _ A m F c hF hR
  have hex : ∀ w' : List (Bool × Mat k r), ∃ C : ℝ, 0 ≤ C ∧ (LRt (w'.map Prod.fst) →
      (∀ y ∈ w', unitLie k r y.2) → w'.length ≤ m →
      ∀ g ∈ GV k r, gN g ^ (A - 2 * (m : ℝ)) * ‖W w' F g‖ ≤ C) := by
    intro w'
    by_cases h : LRt (w'.map Prod.fst) ∧ (∀ y ∈ w', unitLie k r y.2) ∧ w'.length ≤ m
    · obtain ⟨a, b, hab⟩ := h.1
      obtain ⟨u, v, -, rfl⟩ := of_tags w' a b hab
      have hu : ∀ X ∈ u, unitLie k r X := fun X hX =>
        h.2.1 (true, X) (by simp only [lr, List.mem_append, List.mem_map]; exact Or.inl ⟨X, hX, rfl⟩)
      have hv : ∀ X ∈ v, unitLie k r X := fun X hX =>
        h.2.1 (false, X) (by simp only [lr, List.mem_append, List.mem_map]; exact Or.inr ⟨X, hX, rfl⟩)
      obtain ⟨C, hC0, hC⟩ := tw_word hF hR u v (fun X hX => (hu X hX).1) hv
        (by rw [← length_lr]; exact h.2.2)
      exact ⟨C, hC0, fun _ _ _ g hg => by rw [← dLR_eq]; exact hC g hg⟩
    · exact ⟨0, le_rfl, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose Cw hCw0 hCw using hex
  set K := Kc k r with hK
  have hK1 : 1 ≤ K := one_le_Kc
  let pat : ℕ → ℕ → List Bool := fun a b => List.replicate a true ++ List.replicate b false
  refine ⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
    K ^ (a + b) * ((bw (k := k) (r := r) (pat a b)).map Cw).sum, hF, ?_⟩
  intro u v hu hv hl g hg
  set w := lr u v with hwdef
  set n := u.length + v.length with hn
  have hwl : w.length = n := length_lr u v
  have hwu : ∀ y ∈ w, unitLie k r y.2 := by
    intro y hy
    simp only [hwdef, lr, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hu X hX
    · exact hv X hX
  have hwL : AllLie w := fun y hy => (hwu y hy).1
  have hexp := W_expand w hwL F (ckOn_mono (by rw [hwl]; exact hl) hF) g hg
  rw [dLR_eq, hexp]
  have hgp : 0 ≤ gN g ^ (A - 2 * (m : ℝ)) := gN_rpow_nonneg g _
  have hterm : ∀ p ∈ expW w, gN g ^ (A - 2 * (m : ℝ)) * ‖p.1 • W p.2 F g‖ ≤ K ^ n * Cw p.2 := by
    intro p hp
    obtain ⟨h1, h2⟩ := expW_mem w p hp
    have hc := expW_coef w hwu p hp
    rw [hwl] at hc
    have htag : LRt (p.2.map Prod.fst) := by
      have e := expW_snd w
      have : p.2 ∈ bw (w.map Prod.fst) := by rw [← e]; exact List.mem_map_of_mem hp
      refine ⟨u.length, v.length, ?_⟩
      rw [hwdef, lr_tags] at this
      exact bw_tags _ _ this
    have hb := hCw p.2 htag h2 (by rw [h1, hwl]; exact hl) g hg
    rw [norm_smul, Real.norm_eq_abs]
    calc gN g ^ (A - 2 * (m : ℝ)) * (|p.1| * ‖W p.2 F g‖)
        = |p.1| * (gN g ^ (A - 2 * (m : ℝ)) * ‖W p.2 F g‖) := by ring
      _ ≤ K ^ n * Cw p.2 :=
          mul_le_mul hc hb (mul_nonneg hgp (norm_nonneg _)) (pow_nonneg (by linarith) _)
  calc gN g ^ (A - 2 * (m : ℝ)) * ‖((expW w).map fun p => p.1 • W p.2 F g).sum‖
      ≤ gN g ^ (A - 2 * (m : ℝ)) * ((expW w).map fun p => ‖p.1 • W p.2 F g‖).sum :=
        mul_le_mul_of_nonneg_left (norm_list_sum_le _ _) hgp
    _ = ((expW w).map fun p => gN g ^ (A - 2 * (m : ℝ)) * ‖p.1 • W p.2 F g‖).sum :=
        (list_sum_mul_left _ _ _).symm
    _ ≤ ((expW w).map fun p => K ^ n * Cw p.2).sum := list_sum_le _ _ _ hterm
    _ = K ^ n * ((bw (pat u.length v.length)).map Cw).sum := by
        rw [list_sum_mul_left]
        congr 1
        have e := expW_snd w
        rw [hwdef, lr_tags] at e
        rw [← e, List.map_map]
        rfl
    _ ≤ ∑ b ∈ Finset.range (m + 1), K ^ (u.length + b) * ((bw (pat u.length b)).map Cw).sum := by
        refine Finset.single_le_sum (f := fun b => K ^ (u.length + b) * ((bw (pat u.length b)).map Cw).sum)
          (fun b _ => mul_nonneg (pow_nonneg (by linarith) _)
            (list_sum_nonneg _ _ fun w' _ => hCw0 w')) (Finset.mem_range.2 (by omega))
    _ ≤ _ := by
        refine Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (m + 1),
            K ^ (a + b) * ((bw (pat a b)).map Cw).sum)
          (fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (pow_nonneg (by linarith) _)
            (list_sum_nonneg _ _ fun w' _ => hCw0 w')) (Finset.mem_range.2 (by omega))
end Formalism.FourierDecayAlt.P.LeftToRightConversion
