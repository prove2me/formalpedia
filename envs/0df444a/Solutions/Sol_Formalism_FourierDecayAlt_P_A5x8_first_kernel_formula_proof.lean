-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.first_kernel_formula_proof
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:59.732886+00:00
-- url     : https://prove2.me/submissions/2dd0d829-bb37-48a5-9f90-9f4690be1bbb

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_section_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_Kp_eq_section
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_tTerm_mk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_inner_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_tTerm_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_tTerm_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_orbZ_unit
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_section_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_addBlock_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_points_finite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution : SingleBlockFormula := by
  intro K _ _ _ R ψ hD h h' c _
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => A5x3.psi_of_mem hD.selfDual hr
  have hNs : Ns R ψ 1 h h' c c = Kp R ψ (addBlock h 1 c) (addBlock h' 1 c) := by simp [Ns]
  rw [hNs]
  obtain ⟨σ, hσb, hσ⟩ := section_exists R h c
  obtain ⟨σ', hσb', hσ'⟩ := section_exists R h' c
  rw [Kp_eq_section R ψ hψ _ _ _ _ σ σ' hσb hσb']
  let F : (Cos R h × Cos R h') × (((Fin h.1.sum → KR R) × (Fin h.1.sum → KR R)) ×
      ((Fin h'.1.sum → KR R) × (Fin h'.1.sum → KR R))) → ℂ := fun z =>
    tTerm R ψ (addBlock_sum h c) (addBlock_sum h' c) (orbZ h (rep R z.1.1)) (orbZ h' (rep R z.1.2))
      (c : K) z.2 * (phase ψ (rep R z.1.1) * conj (phase ψ (rep R z.1.2)))
  have hG : ∀ x : Par R h × Par R h', Gterm R ψ _ _ (σ x.1) (σ' x.2) =
      F (Equiv.prodProdProdComm _ _ _ _ x) := by
    rintro ⟨⟨q, x, y⟩, ⟨q', x', y'⟩⟩
    simp only [F, Equiv.prodProdProdComm_apply]
    rw [tTerm_mk]
    unfold Gterm
    rw [(hσ (q, x, y)).1, (hσ' (q', x', y')).1, (hσ (q, x, y)).2 ψ, (hσ' (q', x', y')).2 ψ, map_mul]
    ring
  rw [finsum_congr hG, finsum_comp_equiv]
  have hI := Formalism.FourierDecayAlt.P.integral_points_finite K R ψ hD h
  have hI' := Formalism.FourierDecayAlt.P.integral_points_finite K R ψ hD h'
  have hfin : (Function.support F).Finite := by
    refine ((hI.prod hI').biUnion (t := fun q => (Prod.mk q) ''
      Function.support (tTerm R ψ (addBlock_sum h c) (addBlock_sum h' c) (orbZ h (rep R q.1))
        (orbZ h' (rep R q.2)) (c : K))) fun q _ => (tTerm_fin R ψ hD _ _ _ _ _
        (orbZ_unit _ _) (orbZ_unit _ _)).image _).subset ?_
    rintro ⟨q, y⟩ hz
    have h1 : tTerm R ψ (addBlock_sum h c) (addBlock_sum h' c) (orbZ h (rep R q.1))
        (orbZ h' (rep R q.2)) (c : K) y ≠ 0 := fun h0 => hz (by simp [F, h0])
    have h2 : IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2)) := by
      by_contra hn
      exact h1 (tTerm_zero R ψ _ _ _ _ _ hn y)
    exact Set.mem_biUnion (x := q) ⟨h2.1, h2.2⟩ ⟨y, h1, rfl⟩
  rw [finsum_curry F hfin]
  refine finsum_congr fun q => ?_
  simp only [F]
  rw [← finsum_mul]
  by_cases hq : IsInt R (orbZ h (rep R q.1)) ∧ IsInt R (orbZ h' (rep R q.2))
  · rw [if_pos hq, inner_sum R ψ hD _ _ _ _ c hq.1 hq.2 (orbZ_unit _ _) (orbZ_unit _ _)]
    ring
  · rw [if_neg hq, finsum_congr (tTerm_zero R ψ _ _ _ _ _ hq)]
    simp
end Formalism.FourierDecayAlt.P.A5x8
