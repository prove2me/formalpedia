-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.rootA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:41.78757+00:00
-- url     : https://prove2.me/submissions/a9df931b-b3fb-47f1-bd87-2ac4819a57aa

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
theorem _root_.solution {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) {l : ℕ} (hl : l ∈ I)
    (hE1 : ∏ j ∈ I.erase l, (ρ j - ρ l + 1) ≠ 0)
    (hNd : Nd l * ((∏ j ∈ I.erase l, (ρ j - ρ l + 1)) * ∏ j ∈ I.erase l, (ρ j - ρ l)) = -(q.eval (-ρ l))) :
    w.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l) := by
  have h1 := h.eval (-ρ l)
  rw [← Finset.mul_prod_erase I _ hl, Finset.sum_eq_single l] at h1
  · have e1 : ∏ j ∈ I.erase l, (-ρ l + (ρ j + 1)) = ∏ j ∈ I.erase l, (ρ j - ρ l + 1) :=
      Finset.prod_congr rfl (fun j _ => by ring)
    have e2 : ∏ j ∈ I.erase l, (-ρ l + ρ j) = ∏ j ∈ I.erase l, (ρ j - ρ l) :=
      Finset.prod_congr rfl (fun j _ => by ring)
    rw [e1, e2] at h1
    apply mul_right_cancel₀ hE1
    linear_combination h1 + hNd
  · intro m _ hml
    have : ∏ j ∈ I.erase m, (-ρ l + ρ j) = 0 :=
      Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)
    rw [this]; simp
  · intro h; exact absurd hl h
end Formalism.FourierDecayAlt.P.Mx6.WB
