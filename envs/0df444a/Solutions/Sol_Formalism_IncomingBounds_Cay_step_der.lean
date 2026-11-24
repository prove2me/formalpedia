-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.step_der
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:06.102274+00:00
-- url     : https://prove2.me/submissions/54bc1998-bbb6-473c-9899-53cefa5d1ee9

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {R' A' : Type*} [CommRing R'] [CommRing A'] [Algebra R' A'] (D : Derivation R' A' A')
    (d α Dm F W CP : A') (k s : ℕ) (hCP : D CP = 0) (hd : D d = α)
    (IH : d ^ k * F = CP * (d ^ s * Dm)) (E3 : d * D Dm = α * ((k : A') + 1) * Dm - W) :
    d ^ (k+1) * D F = CP * d ^ s * (((s : A') + 1) * α * Dm - W) := by
  have hpow : ∀ m : ℕ, d * D (d ^ m) = (m : A') * d ^ m * α := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hd]
      push_cast
      linear_combination d * ih
  have h1 := congrArg D IH
  rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz, hCP, smul_zero, add_zero] at h1
  simp only [smul_eq_mul] at h1
  linear_combination d * h1 - F * hpow k + CP * Dm * hpow s - (k : A') * α * IH + CP * d ^ s * E3
end Formalism.IncomingBounds.Cay
