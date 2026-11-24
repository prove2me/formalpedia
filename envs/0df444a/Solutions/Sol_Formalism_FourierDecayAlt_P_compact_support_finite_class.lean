-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.compact_support_finite_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:24.42849+00:00
-- url     : https://prove2.me/submissions/90dee903-b01f-4c5f-baaa-fde3815ba267

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_W_local_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_mem_box
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_local_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_GV_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.JFxG
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.P.JFxG.CptInCC := by
  intro k r E _ _ F C hF hC hCF A m
  have hCG : IsCompact (C ∩ GV k r) := hC.inter_right B5.GV_closed
  have hloc : ∀ g₀ ∈ C ∩ GV k r, ∃ V, V ∈ 𝓝 g₀ ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ V, x ∈ GV k r → ∀ (j : ℕ), j ≤ m →
      ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r), (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F x‖ ≤ c := fun g₀ hg₀ => by
    obtain ⟨V, hV, c, hc0, hc⟩ := local_bound hF m hg₀.2
    exact ⟨V, hV, c, hc0, hc⟩
  choose! V hV c hc0 hc using hloc
  obtain ⟨t, htC, hcov⟩ := hCG.elim_nhds_subcover V hV
  have hcW : ∀ g ∈ C ∩ GV k r, ∀ (j : ℕ), j ≤ m → ∀ (bs : Fin j → Bool) (Xs : Fin j → Mat k r),
      (∀ i, inLie k r (Xs i)) → (∀ i, Xs i ∈ Box k r) →
        ‖W (List.ofFn fun i => (bs i, Xs i)) F g‖ ≤ ∑ x ∈ t, c x := by
    intro g hg j hj bs Xs hL hB
    obtain ⟨x, hxt, hgx⟩ := Set.mem_iUnion₂.1 (hcov hg)
    exact (hc x (htC x hxt) g hgx hg.2 j hj bs Xs hL hB).trans
      (Finset.single_le_sum (fun y hy => hc0 y (htC y hy)) hxt)
  obtain ⟨cg, hcg⟩ := hCG.exists_bound_of_continuousOn (f := fun g : Mat k r => gN g ^ A)
    fun g hg => ((B6.gN_continuous.continuousAt).rpow_const (Or.inl (B6.gN_pos hg.2).ne')).continuousWithinAt
  have hsum0 : 0 ≤ ∑ x ∈ t, c x := Finset.sum_nonneg fun y hy => hc0 y (htC y hy)
  refine ⟨|cg| * ∑ x ∈ t, c x, B5.ckOn_mono le_top hF, ?_⟩
  intro u v hu hv hl g hg
  rw [dLR_eq]
  have hmemlr : ∀ y ∈ lr u v, unitLie k r y.2 := by
    intro y hy
    simp only [lr, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hu X hX
    · exact hv X hX
  by_cases hgC : g ∈ C
  · have hw : lr u v = List.ofFn fun i : Fin (lr u v).length => ((lr u v)[i].1, (lr u v)[i].2) := by
      simp
    have hlen : (lr u v).length ≤ m := by simp [lr]; omega
    have hb := hcW g ⟨hgC, hg⟩ _ hlen (fun i => (lr u v)[i].1) (fun i => (lr u v)[i].2)
      (fun i => (hmemlr _ (List.getElem_mem _)).1) (fun i => mem_box (hmemlr _ (List.getElem_mem _)).2)
    rw [← hw] at hb
    have hg1 : gN g ^ A ≤ |cg| := by
      have := hcg g ⟨hgC, hg⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
    exact mul_le_mul hg1 hb (norm_nonneg _) (abs_nonneg _)
  · have h0 := W_local_zero hC.isClosed.isOpen_compl (fun x hx _ => hCF x hx) (lr u v)
      (fun y hy => (hmemlr y hy).1) g hgC hg
    rw [h0, norm_zero, mul_zero]
    positivity
end Formalism.FourierDecayAlt.P
