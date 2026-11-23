-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:36.120015+00:00
-- url     : https://prove2.me/submissions/b83817b0-0f6f-4aa2-a65e-b6d2ad59266b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_pX_monic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_pX_natDegree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_pX_nextCoeff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_add_low
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_pX_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution {I : Finset ℕ} {ρ : ℕ → ℂ} (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {q1 w : ℂ[X]} (hq1 : q1.Monic)
    (hdeg : q1.natDegree = 2 * I.card + 2) {c : ℂ} (hc : c ≠ 0) {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ (C c * q1) w N)
    (hroot : ∀ l ∈ I, w.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l)) :
    ∃ c0 : ℂ, ∀ u : ℂ, w.eval u = (∏ i ∈ I, (u + ρ i)) *
      (c * (u ^ 2 + (q1.nextCoeff - ∑ i ∈ I, (ρ i + 1) - ∑ i ∈ I, ρ i) * u) + c0) +
      ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) := by
  set ρ1 : ℕ → ℂ := fun i => ρ i + 1 with hρ1
  set S1 : ℂ[X] := ∑ l ∈ I, C (N l) * (pX (I.erase l) ρ * pX (I.erase l) ρ1) with hS1
  set S2 : ℂ[X] := ∑ l ∈ I, C (N l - Nd l) * pX (I.erase l) ρ with hS2
  have hcc : (C c⁻¹ * C c : ℂ[X]) = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have dS1 : (C c⁻¹ * S1).natDegree ≤ I.card + I.card := by
    refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun l _ => ?_)
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    rw [pX_natDegree, pX_natDegree]
    exact add_le_add (Finset.card_erase_le) (Finset.card_erase_le)
  have dS2 : (-(C c⁻¹ * S2)).natDegree ≤ I.card := by
    rw [natDegree_neg]
    refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun l _ => ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [pX_natDegree]
    exact Finset.card_erase_le
  have hM : (C c⁻¹ * w) * pX I ρ1 = q1 + C c⁻¹ * S1 := by
    have := h
    unfold W1 at this
    calc (C c⁻¹ * w) * pX I ρ1 = C c⁻¹ * (w * pX I ρ1) := by ring
      _ = C c⁻¹ * (C c * q1 + S1) := by rw [this]
      _ = (C c⁻¹ * C c) * q1 + C c⁻¹ * S1 := by ring
      _ = q1 + C c⁻¹ * S1 := by rw [hcc, one_mul]
  obtain ⟨m1, m2, m3⟩ := add_low (p := q1) (r := C c⁻¹ * S1) hq1 (by omega)
  rw [← hM] at m1 m2 m3
  have hw1 : (C c⁻¹ * w).Monic := Monic.of_mul_monic_right (pX_monic I ρ1) m1
  rw [hw1.natDegree_mul (pX_monic I ρ1), pX_natDegree] at m2
  rw [hw1.nextCoeff_mul (pX_monic I ρ1), pX_nextCoeff] at m3
  obtain ⟨r1, r2, r3⟩ := add_low (p := C c⁻¹ * w) (r := -(C c⁻¹ * S2)) hw1 (by omega)
  have hdvd : pX I ρ ∣ C c⁻¹ * w + -(C c⁻¹ * S2) := by
    apply pX_dvd hinj
    intro l hl
    have : S2.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l) := by
      rw [hS2, eval_finsetSum, Finset.sum_eq_single l]
      · rw [eval_mul, eval_C, pX_eval]
        congr 1
        exact Finset.prod_congr rfl (fun j _ => by ring)
      · intro m _ hml
        rw [eval_mul, eval_C, pX_eval, Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)]
        simp
      · intro h; exact absurd hl h
    simp only [eval_add, eval_neg, eval_mul, eval_C, this, hroot l hl]
    ring
  obtain ⟨Q, hQ⟩ := hdvd
  rw [hQ] at r1 r2 r3
  have hQm : Q.Monic := Monic.of_mul_monic_left (pX_monic I ρ) r1
  rw [(pX_monic I ρ).natDegree_mul hQm, pX_natDegree] at r2
  rw [(pX_monic I ρ).nextCoeff_mul hQm, pX_nextCoeff] at r3
  have hQd : Q.natDegree = 2 := by omega
  have hQ2 : Q.coeff 2 = 1 := by rw [← hQd]; exact hQm
  have hQ1 : Q.coeff 1 = Q.nextCoeff := by rw [nextCoeff_of_natDegree_pos (by omega), hQd]
  refine ⟨c * Q.coeff 0, fun u => ?_⟩
  have hQe : Q.eval u = Q.coeff 0 + Q.nextCoeff * u + u ^ 2 := by
    rw [eval_eq_sum_range, hQd]
    simp [Finset.sum_range_succ, hQ2, hQ1]
  have hS2e : S2.eval u = ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) := by
    rw [hS2, eval_finsetSum]
    exact Finset.sum_congr rfl (fun l _ => by rw [eval_mul, eval_C, pX_eval])
  have h5 := congrArg (Polynomial.eval u) hQ
  simp only [eval_add, eval_neg, eval_mul, eval_C, pX_eval, hQe, hS2e] at h5
  rw [← hS2e] at h5 ⊢
  have hn : Q.nextCoeff = q1.nextCoeff - ∑ i ∈ I, (ρ i + 1) - ∑ i ∈ I, ρ i := by
    have : ∑ i ∈ I, ρ1 i = ∑ i ∈ I, (ρ i + 1) := rfl
    rw [this] at m3
    linear_combination r3 + m3
  rw [← hn]
  have : w.eval u = c * (c⁻¹ * w.eval u) := by field_simp
  rw [this]
  have h6 : c⁻¹ * w.eval u = (∏ i ∈ I, (u + ρ i)) * (Q.coeff 0 + Q.nextCoeff * u + u ^ 2) + c⁻¹ * S2.eval u := by
    linear_combination h5
  rw [h6]
  field_simp
  ring
end Formalism.FourierDecayAlt.P.Mx6.WB
