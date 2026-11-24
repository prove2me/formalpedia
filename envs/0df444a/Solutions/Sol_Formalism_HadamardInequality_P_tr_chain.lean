-- Prove2me | solution 1 for Formalism.HadamardInequality.P.tr_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:50:23.850661+00:00
-- url     : https://prove2.me/submissions/46510584-52d7-4970-831c-f58d1cd0e5e4

import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_NormUnitaryBounds_NormUnitary
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Theorems.Thm_Formalism_HadamardInequality_P_tr_step
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ShearCoefficients_CoeffHom_zero
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_norm_add_sq_eq_of_inner_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HadamardInequality Formalism.HadamardInequality.P
namespace Formalism.HadamardInequality.P
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) :
    ∀ k, k ≤ finrank ℝ E → ∃ (b : Fin k → E) (t : Fin k → ℝ), (∀ i, b i ∈ M) ∧
      LinearIndependent ℝ b ∧ (∀ i, 0 < t i) ∧
      (∀ i, 4 * ‖b i‖ ^ 2 ≤ 3 * t i ^ 2 + ∑ l, t l ^ 2) ∧
      (∀ i : Fin k, ∃ W : Submodule ℝ E, finrank ℝ W = i.val ∧
          ∀ m ∈ M, Wᗮ.starProjection m ≠ 0 → t i ≤ ‖Wᗮ.starProjection m‖) ∧
      (∀ w ∈ span ℝ (Set.range b), ∃ z ∈ span ℤ (Set.range b),
        4 * ‖w - z‖ ^ 2 ≤ ∑ l, t l ^ 2) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, linearIndependent_empty_type,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    intro w hw
    have hr : Set.range (Fin.elim0 : Fin 0 → E) = ∅ := Set.range_eq_empty _
    rw [hr, Submodule.span_empty, Submodule.mem_bot] at hw
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simp [hw]
  | succ k ih =>
    intro hk
    obtain ⟨b, t, hbM, hli, ht0, hbn, hWs, hcov⟩ := ih (by omega)
    set W := span ℝ (Set.range b) with hWdef
    set N := span ℤ (Set.range b) with hNdef
    have hNM : N ≤ M := span_le.2 (Set.range_subset_iff.2 hbM)
    have hNW : span ℝ (N : Set E) = W := Submodule.span_span_of_tower ℤ ℝ (Set.range b)
    have hNWle : ∀ z ∈ N, z ∈ W := fun z hz => by
      rw [← hNW]; exact Submodule.subset_span hz
    have hWrk : finrank ℝ W = k := by
      rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
    have hWtop : W ≠ ⊤ := by
      intro h
      have : finrank ℝ W = finrank ℝ E := by rw [h, finrank_top]
      omega
    obtain ⟨m, hm, hq0, hqmin⟩ := tr_step M hspan W N hNM hNW hWtop
    set q := Wᗮ.starProjection m with hqdef
    set S := ∑ l, t l ^ 2 with hSdef
    have hqW : q ∈ Wᗮ := starProjection_apply_mem _ _
    have hwW : m - q ∈ W := by
      have := sub_starProjection_mem_orthogonal (K := Wᗮ) m
      rwa [orthogonal_orthogonal] at this
    obtain ⟨z, hzN, hz⟩ := hcov (m - q) hwW
    set b' := m - z with hb'
    have hb'M : b' ∈ M := M.sub_mem hm (hNM hzN)
    have hdecomp : b' = q + (m - q - z) := by rw [hb']; abel
    have hezW : m - q - z ∈ W := W.sub_mem hwW (hNWle z hzN)
    have horth : ∀ e ∈ W, inner ℝ q e = 0 := fun e he => by
      rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal he hqW
    have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have hb'n : 4 * ‖b'‖ ^ 2 ≤ 4 * ‖q‖ ^ 2 + S := by
      rw [hdecomp, Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero (horth _ hezW)]
      have : m - q - z = m - q - z := rfl
      nlinarith
    have hb'W : b' ∉ W := by
      intro hW'
      apply hq0
      have hqW' : q ∈ W := by
        have : q = b' - (m - q - z) := by rw [hdecomp]; abel
        rw [this]; exact W.sub_mem hW' hezW
      exact inner_self_eq_zero.1 (horth q hqW')
    have hsum : ∑ l, (Fin.snoc (α := fun _ => ℝ) t ‖q‖ l) ^ 2 = S + ‖q‖ ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      simp [hSdef]
    refine ⟨Fin.snoc b b', Fin.snoc (α := fun _ => ℝ) t ‖q‖, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hb'M
      · simpa using hbM j
    · exact linearIndependent_finSnoc.2 ⟨hli, hb'W⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hqpos
      · simpa using ht0 j
    · intro i
      rw [hsum]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        linarith
      · simp only [Fin.snoc_castSucc]
        have := hbn j
        nlinarith [sq_nonneg ‖q‖]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · refine ⟨W, by simpa using hWrk, fun m' hm' h0 => ?_⟩
        simpa using hqmin m' hm' h0
      · obtain ⟨W', hW'r, hW'm⟩ := hWs j
        exact ⟨W', by simpa using hW'r, fun m' hm' h0 => by simpa using hW'm m' hm' h0⟩
    · intro w' hw'
      rw [hsum]
      rw [Fin.range_snoc, Submodule.mem_span_insert] at hw'
      obtain ⟨c0, w0, hw0, rfl⟩ := hw'
      set c : ℤ := round c0 with hc
      set s : ℝ := c0 - c with hs
      have hsabs : |s| ≤ 1 / 2 := abs_sub_round c0
      have hs2 : s ^ 2 ≤ 1 / 4 := by
        have := sq_abs s
        nlinarith [abs_nonneg s]
      set w1 := w0 + s • (m - q - z) with hw1
      have hw1W : w1 ∈ W := W.add_mem hw0 (W.smul_mem _ hezW)
      obtain ⟨z1, hz1N, hz1⟩ := hcov w1 hw1W
      refine ⟨c • b' + z1, ?_, ?_⟩
      · rw [Fin.range_snoc, Submodule.mem_span_insert]
        exact ⟨c, z1, hz1N, rfl⟩
      · have heq : c0 • b' + w0 - (c • b' + z1) = s • q + (w1 - z1) := by
          rw [← Int.cast_smul_eq_zsmul ℝ, hw1, hs]
          conv_lhs => rw [hdecomp]
          simp only [sub_smul, smul_add, smul_sub]
          abel
        have hw1z1 : w1 - z1 ∈ W := W.sub_mem hw1W (hNWle z1 hz1N)
        rw [heq, Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero (by
          rw [real_inner_smul_left, horth _ hw1z1, mul_zero]), norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs]
        have hqq : 0 ≤ ‖q‖ ^ 2 := sq_nonneg _
        nlinarith
end Formalism.HadamardInequality.P
