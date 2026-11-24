-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.la_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:22:07.337664+00:00
-- url     : https://prove2.me/submissions/40aea61e-ed23-4a8f-bf57-a4f80036ce31

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] {k r : ℕ}
    {z' : Fin (2 * r + k + 1) → ℂ} {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {La : A →ₗ[ℂ] M}
    (hR : RightRuleFn k r z' E La) {x : A} (hx : x ∈ Ideal.span (rgen k r z' E)) : La x = 0 := by
  have key : ∀ y ∈ Ideal.span (rgen k r z' E), ∀ a : A, La (a * y) = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, q, hpq, rfl⟩ := hy
      intro a
      rw [mul_sub, map_sub, hR a p q hpq, ← Algebra.commutes, ← Algebra.smul_def, map_smul, sub_self]
    | zero => intro a; simp
    | add x y _ _ hx hy => intro a; rw [mul_add, map_add, hx, hy, add_zero]
    | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx (a * b)
  simpa using key x hx 1
end Formalism.FourierDecayAlt.P.SignAntidiagonal
