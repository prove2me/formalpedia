-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.DD_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:19.2658+00:00
-- url     : https://prove2.me/submissions/e5fb98d0-54e3-4028-aa7a-61f762495eee

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_natDegree_sub_le_of_next
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pa_monic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pa_natDegree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pa_nextCoeff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_DD_dvd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1)
    (hq1 : q1.Monic) (hdeg : q1.natDegree = 2 * s.card + 2) (e : ℂ)
    (he : e = q1.nextCoeff - ∑ i ∈ s, ρ i - ∑ i ∈ s, (ρ i + 1)) :
    ∃ r : ℂ, DD s ρ c q1 N M = pa s ρ * pa s (fun i => ρ i + 1) *
      (C c * ((X + C 0) * (X + C e)) + C r) := by
  have hdv := DD_dvd s ρ hinj c q1 N M H1 H2 H3
  generalize hX12 : pa s ρ * pa s (fun i => ρ i + 1) = coord_mul_inv_coord_eq_one at hdv ⊢
  have hXm : coord_mul_inv_coord_eq_one.Monic := by rw [← hX12]; exact (pa_monic _ _).mul (pa_monic _ _)
  have hXd : coord_mul_inv_coord_eq_one.natDegree = 2 * s.card := by
    rw [← hX12, Monic.natDegree_mul (pa_monic _ _) (pa_monic _ _), pa_natDegree, pa_natDegree]; ring
  have hXn : coord_mul_inv_coord_eq_one.nextCoeff = ∑ i ∈ s, ρ i + ∑ i ∈ s, (ρ i + 1) := by
    rw [← hX12, Monic.nextCoeff_mul (pa_monic _ _) (pa_monic _ _), pa_nextCoeff, pa_nextCoeff]
  generalize hg : ((X + C 0) * (X + C e) : ℂ[X]) = g
  have hgm : g.Monic := by rw [← hg]; exact (monic_X_add_C _).mul (monic_X_add_C _)
  have hgd : g.natDegree = 2 := by
    rw [← hg, Monic.natDegree_mul (monic_X_add_C _) (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
  have hgn : g.nextCoeff = e := by
    rw [← hg, Monic.nextCoeff_mul (monic_X_add_C _) (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]; ring
  have h1 : (q1 - coord_mul_inv_coord_eq_one * g).natDegree ≤ 2 * s.card := by
    apply natDegree_sub_le_of_next _ _ _ hq1 (hXm.mul hgm) hdeg
    · rw [Monic.natDegree_mul hXm hgm, hXd, hgd]
    · rw [Monic.nextCoeff_mul hXm hgm, hXn, hgn, he]; ring
  have hR : (DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g)).natDegree ≤ 2 * s.card := by
    have : DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g) = C c * (q1 - coord_mul_inv_coord_eq_one * g) +
        ((∑ l ∈ s, C (M l) * (pa (s.erase l) ρ * pa s (fun i => ρ i + 1))) -
          (∑ l ∈ s, C (N l) * (pa s ρ * pa (s.erase l) (fun i => ρ i + 1)))) := by
      unfold DD; ring
    rw [this]
    refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans h1) ((natDegree_sub_le_of_le ?_ ?_).trans (le_of_eq (max_self _)))
    · apply natDegree_sum_le_of_forall_le
      intro l hl
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      rw [pa_natDegree, pa_natDegree, Finset.card_erase_of_mem hl]; omega
    · apply natDegree_sum_le_of_forall_le
      intro l hl
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      rw [pa_natDegree, pa_natDegree, Finset.card_erase_of_mem hl]; omega
  obtain ⟨S, hS⟩ : coord_mul_inv_coord_eq_one ∣ DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g) :=
    dvd_sub hdv (Dvd.dvd.mul_left (dvd_mul_right _ _) _)
  have hS0 : S.natDegree = 0 := by
    by_cases h0 : S = 0
    · rw [h0]; simp
    · rw [hS, Monic.natDegree_mul' hXm h0, hXd] at hR; omega
  refine ⟨S.coeff 0, ?_⟩
  rw [← eq_C_of_natDegree_eq_zero hS0]
  linear_combination hS
end Formalism.FourierDecayAlt.P.Mx7
