-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.rootB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:36.170843+00:00
-- url     : https://prove2.me/submissions/5ab7d488-ea4a-4722-80e9-e33607c2c9c9

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_pX_erase

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
theorem _root_.solution {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (h : W1 I ρ q w N)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {l j0 : ℕ} (hl : l ∈ I) (hj0 : j0 ∈ I) (hne : j0 ≠ l)
    (hρ : ρ j0 + 1 = ρ l) (hq : (X + C (ρ l)) ^ 2 ∣ q) (hN0 : N j0 = 0) :
    w.eval (-ρ l) = N l * ∏ j ∈ I.erase l, (ρ j - ρ l) := by
  set ρ1 : ℕ → ℂ := fun i => ρ i + 1 with hρ1
  have hx1 : pX I ρ1 = (X + C (ρ l)) * pX (I.erase j0) ρ1 := by
    rw [pX_erase I ρ1 hj0, hρ1]; simp only [hρ]
  have hF : pX (I.erase j0) ρ1 = (X + C (ρ l + 1)) * pX ((I.erase j0).erase l) ρ1 :=
    pX_erase _ _ (Finset.mem_erase.2 ⟨hne.symm, hl⟩)
  have hE : pX (I.erase l) ρ1 = (X + C (ρ l)) * pX ((I.erase j0).erase l) ρ1 := by
    rw [pX_erase (I.erase l) ρ1 (Finset.mem_erase.2 ⟨hne, hj0⟩), Finset.erase_right_comm, hρ1]; simp only [hρ]
  have hdiv : (X + C (ρ l)) ^ 2 ∣ q + ∑ m ∈ I.erase l, C (N m) * (pX (I.erase m) ρ * pX (I.erase m) ρ1) := by
    refine dvd_add hq (Finset.dvd_sum fun m hm => ?_)
    by_cases hm0 : m = j0
    · rw [hm0, hN0]; simp
    · have hm' := Finset.mem_erase.1 hm
      rw [pX_erase (I.erase m) ρ (Finset.mem_erase.2 ⟨fun e => hm'.1 e.symm, hl⟩),
        pX_erase (I.erase m) ρ1 (Finset.mem_erase.2 ⟨fun e => hm0 e.symm, hj0⟩)]
      have : (ρ1 j0) = ρ l := hρ
      rw [this]
      exact ⟨C (N m) * (pX ((I.erase m).erase l) ρ * pX ((I.erase m).erase j0) ρ1), by ring⟩
  obtain ⟨Aq, hA⟩ := hdiv
  have h2 : w * pX I ρ1 = (q + ∑ m ∈ I.erase l, C (N m) * (pX (I.erase m) ρ * pX (I.erase m) ρ1)) +
      C (N l) * (pX (I.erase l) ρ * pX (I.erase l) ρ1) := by
    have := h
    unfold W1 at this
    rw [this, ← Finset.add_sum_erase I _ hl]; ring
  rw [hA, hx1, hE] at h2
  have h3 : w * pX (I.erase j0) ρ1 = (X + C (ρ l)) * Aq + C (N l) * (pX (I.erase l) ρ * pX ((I.erase j0).erase l) ρ1) := by
    apply mul_left_cancel₀ (monic_X_add_C (ρ l)).ne_zero
    linear_combination h2
  rw [hF] at h3
  have h4 := congrArg (Polynomial.eval (-ρ l)) h3
  simp only [eval_mul, eval_add, eval_X, eval_C, pX_eval] at h4
  have hG : ∏ j ∈ (I.erase j0).erase l, (-ρ l + ρ1 j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj h0
    have hj' := Finset.mem_erase.1 hj
    have hj'' := Finset.mem_erase.1 hj'.2
    apply hj''.1
    apply hinj j hj''.2 j0 hj0
    have : ρ1 j = ρ j + 1 := rfl
    rw [this] at h0
    linear_combination h0 - hρ
  have e2 : ∏ j ∈ I.erase l, (-ρ l + ρ j) = ∏ j ∈ I.erase l, (ρ j - ρ l) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [e2] at h4
  apply mul_right_cancel₀ hG
  linear_combination h4
end Formalism.FourierDecayAlt.P.Mx6.WB
