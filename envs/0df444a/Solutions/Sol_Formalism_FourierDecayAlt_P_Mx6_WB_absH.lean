-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.absH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:39.764805+00:00
-- url     : https://prove2.me/submissions/b0a19efa-ef07-4051-bb0c-6c62328cd4ad

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt

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
theorem _root_.solution {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) (Qf : ℂ → ℂ)
    (hw : ∀ u, w.eval u = (∏ i ∈ I, (u + ρ i)) * Qf u + ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j))
    (u : ℂ) (h0 : ∀ i ∈ I, u + ρ i ≠ 0) (h1 : ∀ i ∈ I, u + ρ i + 1 ≠ 0) :
    q.eval u / ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) =
      Qf u + ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) := by
  have hx0 : ∏ i ∈ I, (u + ρ i) ≠ 0 := Finset.prod_ne_zero_iff.2 h0
  have hx1 : ∏ i ∈ I, (u + (ρ i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun i hi => by rw [← add_assoc]; exact h1 i hi)
  have s1 : ∑ l ∈ I, N l * ((∏ j ∈ I.erase l, (u + ρ j)) * ∏ j ∈ I.erase l, (u + (ρ j + 1))) =
      ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) * ∑ l ∈ I, N l / ((u + ρ l) * (u + ρ l + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [← Finset.mul_prod_erase I (fun i => u + ρ i) hl, ← Finset.mul_prod_erase I (fun i => u + (ρ i + 1)) hl]
    have a0 := h0 l hl
    have a1 := h1 l hl
    have a2 : u + (ρ l + 1) = u + ρ l + 1 := by ring
    rw [a2]
    field_simp
  have s2 : ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) =
      (∏ i ∈ I, (u + ρ i)) * ∑ l ∈ I, (N l - Nd l) / (u + ρ l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [← Finset.mul_prod_erase I (fun i => u + ρ i) hl]
    have a0 := h0 l hl
    field_simp
  have s3 : ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) =
      ∑ l ∈ I, (N l - Nd l) / (u + ρ l) - ∑ l ∈ I, N l / ((u + ρ l) * (u + ρ l + 1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have a0 := h0 l hl
    have a1 := h1 l hl
    field_simp
    ring
  have e1 := h.eval u
  rw [s1, hw u, s2] at e1
  rw [div_eq_iff (mul_ne_zero hx0 hx1), s3]
  linear_combination -e1
end Formalism.FourierDecayAlt.P.Mx6.WB
