-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.weyl_measure_from_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:51:52.834086+00:00
-- url     : https://prove2.me/submissions/37c05bc7-916f-4976-a4cd-03fb838863ef

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_Jm_sg
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_uwb_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_rmulF_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.WbFromDiag := by
  intro hEmb hUni hBall hFacts k r
  have hΦc : Continuous (Φ k r) := emb_cont.comp (hEmb (k + 1) (sg k)).1.continuous
  have hΦ : Measurable (Φ k r) := hΦc.measurable
  have hU : UWb k r = embWb k r '' {μ | μᴴ * Hb k * μ = Hb k} := (hFacts k r).1
  have hmem : ∀ g : UJ (sg k), (Φ k r g : Mat k r) ∈ UWb k r := by
    intro g
    rw [hU]
    refine ⟨_, ?_, rfl⟩
    have : inUJ (sg k) ((g : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := g.2
    unfold inUJ at this
    rw [Jm_sg] at this
    exact this
  have hlift : ∀ a ∈ UWb k r, ∃ g₀ : UJ (sg k), a = embWb k r
      ((g₀ : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) := by
    intro a ha
    rw [hU] at ha
    obtain ⟨α, hα, rfl⟩ := ha
    have h1 : α ∈ {g | inUJ (sg k) g} := by
      show αᴴ * Jm (sg k) * α = Jm (sg k)
      rw [Jm_sg]; exact hα
    rw [← (hEmb (k + 1) (sg k)).2] at h1
    obtain ⟨g₀, hg₀⟩ := h1
    exact ⟨g₀, by rw [← hg₀]⟩
  refine ⟨(muG (sg k)).map (Φ k r), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hΦ (show IsOpen ((UWb k r)ᶜ : Set (Mt k r)) from uwb_closed.isOpen_compl).measurableSet]
    have : Φ k r ⁻¹' ((UWb k r)ᶜ : Set (Mt k r)) = ∅ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      exact fun h => h (hmem g)
    rw [this, measure_empty]
  · intro a ha
    obtain ⟨g₀, hg₀⟩ := hlift a ha
    rw [Measure.map_map (lmulM_cont _).measurable hΦ]
    have : (lmulM a ∘ Φ k r) = Φ k r ∘ (fun x => g₀ * x) := by
      funext x
      rw [hg₀]
      exact (emb_mul _ _).symm
    rw [this, ← Measure.map_map hΦ (continuous_const_mul g₀).measurable, map_mul_left_eq_self]
  · intro a ha
    obtain ⟨g₀, hg₀⟩ := hlift a ha
    rw [Measure.map_map (rmulF_cont _).measurable hΦ]
    have : (rmulF a ∘ Φ k r) = Φ k r ∘ (fun x => x * g₀) := by
      funext x
      rw [hg₀]
      exact (emb_mul _ _).symm
    rw [this, ← Measure.map_map hΦ (continuous_mul_const g₀).measurable, hUni (k + 1) (sg k) g₀]
  · intro K hK
    rw [Measure.map_apply hΦ hK.isClosed.measurableSet]
    have hφ : Continuous (fun x : Mt k r => ∑ i : Fin (k + 1), ∑ j : Fin (k + 1), ‖x (wI k r i) (wI k r j)‖ ^ 2) := by
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      exact ((continuous_apply_apply (wI k r i) (wI k r j)).norm).pow 2
    obtain ⟨R, hR⟩ := hK.bddAbove_image hφ.continuousOn
    refine lt_of_le_of_lt (measure_mono ?_) (hBall (k + 1) (sg k) R)
    intro g hg
    have h1 := hR ⟨_, hg, rfl⟩
    show hsG g ≤ R
    unfold hsG hs
    refine le_of_eq_of_le ?_ h1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show _ = ‖embWb k r _ (wI k r i) (wI k r j)‖ ^ 2
    rw [emb_wI]
  · intro h0
    rw [Measure.map_eq_zero_iff hΦ.aemeasurable] at h0
    have := isOpen_univ.measure_ne_zero (muG (sg k)) Set.univ_nonempty
    rw [h0] at this
    exact this rfl
end Formalism.FourierDecayAlt.P
