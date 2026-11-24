-- Prove2me | solution 1 for Formalism.HadamardInequality.P.tr_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:42.888495+00:00
-- url     : https://prove2.me/submissions/20f7ac37-ac15-45b2-bbc5-73735e12fed1

import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_NormUnitaryBounds_NormUnitary
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Theorems.Thm_Formalism_HadamardInequality_P_tr_shortest
import Theorems.Thm_Formalism_F_degree_quotient
import Theorems.Thm_Formalism_F_saturation_properties
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
    (hspan : span ℝ (M : Set E) = ⊤)
    (W : Submodule ℝ E) (N : Submodule ℤ E) (hNM : N ≤ M) (hNW : span ℝ (N : Set E) = W)
    (hW : W ≠ ⊤) :
    ∃ m ∈ M, Wᗮ.starProjection m ≠ 0 ∧
      ∀ m' ∈ M, Wᗮ.starProjection m' ≠ 0 →
        ‖Wᗮ.starProjection m‖ ≤ ‖Wᗮ.starProjection m'‖ := by
  obtain ⟨hsat, hNS, -⟩ := Formalism.F.saturation_properties E M N hMd hNM
  set S := Formalism.F.satur M N with hSdef
  have hSW : span ℝ (S : Set E) = W := by
    rw [← hNW]
    refine le_antisymm (span_le.2 fun x hx => (Submodule.mem_inf.1 hx).2) (span_mono hNS)
  have hQd : DiscreteTopology (Formalism.F.quot M S) := (Formalism.F.degree_quotient E M S hMd hsat).1
  set Q := Formalism.F.quot M S with hQdef
  have hmemQ : ∀ q, q ∈ Q ↔ ∃ m ∈ M, Wᗮ.starProjection m = q := by
    intro q
    simp [hQdef, Formalism.F.quot, hSW]
  have hsubW : ∀ x, x - Wᗮ.starProjection x ∈ W := by
    intro x
    have := sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [orthogonal_orthogonal] at this
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply hW
    rw [eq_top_iff, ← hspan, span_le]
    intro m hm
    have h0 : Wᗮ.starProjection m = 0 := by
      have : Wᗮ.starProjection m ∈ Q := (hmemQ _).2 ⟨m, hm, rfl⟩
      rw [hQ] at this
      exact (Submodule.mem_bot ℤ).1 this
    have := hsubW m
    rwa [h0, sub_zero] at this
  obtain ⟨q, hqQ, hq0, hqmin⟩ := tr_shortest Q hQne
  obtain ⟨m, hm, rfl⟩ := (hmemQ q).1 hqQ
  exact ⟨m, hm, hq0, fun m' hm' h0 => hqmin _ ((hmemQ _).2 ⟨m', hm', rfl⟩) h0⟩
end Formalism.HadamardInequality.P
