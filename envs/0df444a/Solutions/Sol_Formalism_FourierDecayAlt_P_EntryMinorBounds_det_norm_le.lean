-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EntryMinorBounds.det_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:32.204797+00:00
-- url     : https://prove2.me/submissions/df3fcc30-a57b-47a0-8f0b-37362ebc74c9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.EntryMinorBounds
namespace Formalism.FourierDecayAlt.P.EntryMinorBounds
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (R : Fin n → ℝ) (hR : ∀ i j, ‖A i j‖ ≤ R i) :
    ‖A.det‖ ≤ (Nat.factorial n : ℝ) * ∏ i, R i := by
  have hR0 : ∀ i, 0 ≤ R i := fun i => le_trans (norm_nonneg _) (hR i i)
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ ∏ i, R i := by
    intro σ
    rw [Units.smul_def, zsmul_eq_mul, norm_mul]
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
    rw [hs, one_mul, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ i, R (σ i) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hR _ _)
      _ = ∏ i, R i := Equiv.prod_comp σ R
  calc ∑ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ i, R i := Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (Nat.factorial n : ℝ) * ∏ i, R i := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
end Formalism.FourierDecayAlt.P.EntryMinorBounds
