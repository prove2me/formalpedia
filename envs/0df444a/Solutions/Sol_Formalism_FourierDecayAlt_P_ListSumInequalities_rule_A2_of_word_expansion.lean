-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumInequalities.rule_A2_of_word_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:29:13.810727+00:00
-- url     : https://prove2.me/submissions/7d912c73-d82e-4ae3-9055-fb6bd74f6be0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_norm_list_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_list_sum_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_bw_tags
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_expW_snd
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_expW_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_one_le_Kc
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_expW_coef
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_W_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_ListSumInequalities_lr_tags
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_one_le_gN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma eq_lr_take_drop_of_map_fst_eq_replicate (w' : List (Bool × Mat k r)) (a b : ℕ)
    (h : w'.map Prod.fst = List.replicate a true ++ List.replicate b false) :
    w' = lr ((w'.take a).map Prod.snd) ((w'.drop a).map Prod.snd) := by
  have hta : (w'.take a).map Prod.fst = List.replicate a true := by
    rw [List.map_take, h, List.take_left' (by simp)]
  have hdr : (w'.drop a).map Prod.fst = List.replicate b false := by
    rw [List.map_drop, h, List.drop_left' (by simp)]
  have e1 : w'.take a = ((w'.take a).map Prod.snd).map (fun X => (true, X)) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id (w'.take a)]
    apply List.map_congr_left
    intro y hy
    have hy1 : y.1 ∈ (w'.take a).map Prod.fst := List.mem_map_of_mem hy
    rw [hta] at hy1
    show y = (true, y.2)
    exact Prod.ext (List.eq_of_mem_replicate hy1) rfl
  have e2 : w'.drop a = ((w'.drop a).map Prod.snd).map (fun X => (false, X)) := by
    rw [List.map_map]
    conv_lhs => rw [← List.map_id (w'.drop a)]
    apply List.map_congr_left
    intro y hy
    have hy1 : y.1 ∈ (w'.drop a).map Prod.fst := List.mem_map_of_mem hy
    rw [hdr] at hy1
    show y = (false, y.2)
    exact Prod.ext (List.eq_of_mem_replicate hy1) rfl
  calc w' = w'.take a ++ w'.drop a := (List.take_append_drop a w').symm
    _ = lr ((w'.take a).map Prod.snd) ((w'.drop a).map Prod.snd) := by
        rw [lr, ← e1, ← e2]
end Formalism.FourierDecayAlt.P.ListSumInequalities
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumInequalities
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumInequalities
theorem _root_.solution : C2.SmoothClassInFiniteOrder := by
  intro k r E _ _ A F hF m
  obtain ⟨hsm, hbd⟩ := hF
  classical
  let Cw : List (Bool × Mat k r) → ℝ := fun w' =>
    if h : ∃ uv : List (Mat k r) × List (Mat k r), (∀ X ∈ uv.1, unitLie k r X) ∧
        (∀ X ∈ uv.2, unitLie k r X) ∧ w' = lr uv.1 uv.2
    then max (Classical.choose (hbd h.choose.1 h.choose.2 h.choose_spec.1 h.choose_spec.2.1)) 0 else 0
  have hCw0 : ∀ w', 0 ≤ Cw w' := by
    intro w'
    dsimp only [Cw]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hCw : ∀ (u v : List (Mat k r)), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → ∀ g ∈ GV k r,
      gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) * ‖W (lr u v) F g‖ ≤ Cw (lr u v) := by
    intro u v hu hv g hg
    have h : ∃ uv : List (Mat k r) × List (Mat k r), (∀ X ∈ uv.1, unitLie k r X) ∧
        (∀ X ∈ uv.2, unitLie k r X) ∧ lr u v = lr uv.1 uv.2 := ⟨(u, v), hu, hv, rfl⟩
    dsimp only [Cw]
    rw [dif_pos h]
    obtain ⟨hu0, hv0, heq⟩ := h.choose_spec
    have hlen : (u.length : ℝ) + v.length = (h.choose.1.length : ℝ) + h.choose.2.length := by
      have h1 := congrArg List.length heq
      simp only [lr, List.length_append, List.length_map] at h1
      exact_mod_cast h1
    have hW : W (lr u v) F g = dLR h.choose.1 h.choose.2 F g :=
      (congrArg (fun w => W w F g) heq).trans (congrFun (dLR_eq _ _ F) g).symm
    have hspec := Classical.choose_spec (hbd h.choose.1 h.choose.2 hu0 hv0) g hg
    rw [hlen, hW]
    exact hspec.trans (le_max_left _ _)
  have hKc : 0 ≤ Kc k r := by linarith [one_le_Kc (k := k) (r := r)]
  refine ⟨∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
    Kc k r ^ (a + b) * ((bw (k := k) (r := r) (List.replicate a true ++ List.replicate b false)).map Cw).sum,
    ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', heq⟩ := hsm g₀ hg₀
    exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast le_top), heq⟩
  · intro u v hu hv huv g hg
    have hAll : AllLie (lr u v) := by
      intro x hx
      simp only [lr, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).1
      · exact (hv X hX).1
    have hunit : ∀ y ∈ lr u v, unitLie k r y.2 := by
      intro y hy
      simp only [lr, List.mem_append, List.mem_map] at hy
      rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact hu X hX
      · exact hv X hX
    have hlenlr : (lr u v).length = u.length + v.length := by simp [lr]
    have hck : CkOn (((lr u v).length : ℕ) : ℕ∞) (GV k r) F := fun g₀ hg₀ => by
      obtain ⟨U, f', hU, hgU, hf', heq⟩ := hsm g₀ hg₀
      exact ⟨U, f', hU, hgU, hf'.of_le (by exact_mod_cast le_top), heq⟩
    have hexp := W_expand (lr u v) hAll F hck g hg
    have hgN : 1 ≤ gN g := one_le_gN hg
    have hpos : 0 ≤ gN g ^ (A - C2.B0 r * (m : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hmono : gN g ^ (A - C2.B0 r * (m : ℝ)) ≤ gN g ^ (A - C2.B0 r * ((u.length : ℝ) + v.length)) := by
      apply Real.rpow_le_rpow_of_exponent_le hgN
      have hB : 0 ≤ C2.B0 r := by unfold C2.B0; positivity
      have hle : ((u.length : ℝ) + v.length) ≤ m := by exact_mod_cast huv
      nlinarith
    have hterm : ∀ p ∈ expW (lr u v), gN g ^ (A - C2.B0 r * (m : ℝ)) * ‖p.1 • W p.2 F g‖ ≤
        Kc k r ^ (u.length + v.length) * Cw p.2 := by
      intro p hp
      obtain ⟨hplen, hpunit⟩ := expW_mem (lr u v) p hp
      have hcoef := expW_coef (lr u v) hunit p hp
      rw [hlenlr] at hcoef
      have htags : p.2.map Prod.fst = List.replicate u.length true ++ List.replicate v.length false := by
        have hm : p.2 ∈ bw ((lr u v).map Prod.fst) := by
          rw [← expW_snd]
          exact List.mem_map_of_mem hp
        rw [lr_tags] at hm
        exact bw_tags _ p.2 hm
      have hsplit := eq_lr_take_drop_of_map_fst_eq_replicate p.2 u.length v.length htags
      have hu'' : ∀ X ∈ (p.2.take u.length).map Prod.snd, unitLie k r X := by
        intro X hX
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hX
        exact hpunit y (List.mem_of_mem_take hy)
      have hv'' : ∀ X ∈ (p.2.drop u.length).map Prod.snd, unitLie k r X := by
        intro X hX
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hX
        exact hpunit y (List.mem_of_mem_drop hy)
      have hlen'' : (((p.2.take u.length).map Prod.snd).length : ℝ) + ((p.2.drop u.length).map Prod.snd).length =
          (u.length : ℝ) + v.length := by
        have h1 := congrArg List.length hsplit
        simp only [lr, List.length_append, List.length_map] at h1
        rw [hplen, hlenlr] at h1
        rw [List.length_map, List.length_map]
        exact_mod_cast h1.symm
      have hb := hCw _ _ hu'' hv'' g hg
      rw [← hsplit, hlen''] at hb
      rw [norm_smul, Real.norm_eq_abs]
      calc gN g ^ (A - C2.B0 r * (m : ℝ)) * (|p.1| * ‖W p.2 F g‖) =
            |p.1| * (gN g ^ (A - C2.B0 r * (m : ℝ)) * ‖W p.2 F g‖) := by ring
        _ ≤ Kc k r ^ (u.length + v.length) * Cw p.2 := by
          apply mul_le_mul hcoef _ (mul_nonneg hpos (norm_nonneg _)) (pow_nonneg hKc _)
          exact (mul_le_mul_of_nonneg_right hmono (norm_nonneg _)).trans hb
    rw [dLR_eq, hexp]
    have hnn : ∀ a b, 0 ≤ Kc k r ^ (a + b) *
        ((bw (k := k) (r := r) (List.replicate a true ++ List.replicate b false)).map Cw).sum :=
      fun a b => mul_nonneg (pow_nonneg hKc _) (list_sum_nonneg _ _ (fun w' _ => hCw0 w'))
    have hu' : u.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    have hv' : v.length ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
    calc gN g ^ (A - C2.B0 r * (m : ℝ)) * ‖((expW (lr u v)).map fun p => p.1 • W p.2 F g).sum‖
        ≤ gN g ^ (A - C2.B0 r * (m : ℝ)) * ((expW (lr u v)).map fun p => ‖p.1 • W p.2 F g‖).sum :=
          mul_le_mul_of_nonneg_left (norm_list_sum_le _ _) hpos
      _ = ((expW (lr u v)).map fun p => gN g ^ (A - C2.B0 r * (m : ℝ)) * ‖p.1 • W p.2 F g‖).sum :=
          (list_sum_mul_left _ _ _).symm
      _ ≤ ((expW (lr u v)).map fun p => Kc k r ^ (u.length + v.length) * Cw p.2).sum :=
          list_sum_le _ _ _ hterm
      _ = Kc k r ^ (u.length + v.length) *
            ((bw (k := k) (r := r) (List.replicate u.length true ++ List.replicate v.length false)).map Cw).sum := by
          rw [list_sum_mul_left, ← lr_tags, ← expW_snd, List.map_map]
          rfl
      _ ≤ ∑ b ∈ Finset.range (m + 1), Kc k r ^ (u.length + b) *
            ((bw (k := k) (r := r) (List.replicate u.length true ++ List.replicate b false)).map Cw).sum :=
          Finset.single_le_sum (f := fun b => Kc k r ^ (u.length + b) *
            ((bw (k := k) (r := r) (List.replicate u.length true ++ List.replicate b false)).map Cw).sum)
            (fun b _ => hnn _ _) hv'
      _ ≤ _ :=
          Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.range (m + 1), Kc k r ^ (a + b) *
            ((bw (k := k) (r := r) (List.replicate a true ++ List.replicate b false)).map Cw).sum)
            (fun a _ => Finset.sum_nonneg fun b _ => hnn a b) hu'
end Formalism.FourierDecayAlt.P.ListSumInequalities
