-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ffa_nlev_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:35:04.967787+00:00
-- url     : https://prove2.me/submissions/64be9f72-ea46-410d-bd91-59628df8c69a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_herm_esI
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_herm_UH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section SlopeTestRemainingChoices
variable {k r : ℕ}
private theorem hpk_eI_apply (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)
private theorem herm_bvec_eI_quadratic_form_two_two (x : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) x (bvec (eI k r a)) = x (esI k r a) := by
  have hs : star (bvec (eI k r a)) = bvec (eI k r a) := by
    funext j
    by_cases h : j = eI k r a <;> simp [bvec, h]
  unfold herm
  rw [hs]
  simp [bvec, mulVec, dotProduct, Pi.single_apply, hpk_eI_apply]
end SlopeTestRemainingChoices
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {D : Set (Mx k r)}
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {n : Mx k r} (hn : n ∈ Nlev k r (Fin.last r)) {w : Fin (2 * r + k + 1) → ℂ}
    (hw : inWb k r w) : n *ᵥ w = w := by
  rcases hn with ⟨⟨hU, -, h3⟩, -, hG⟩
  have hlast : ∀ a : Fin r, a.val < (Fin.last r).val := fun a => by simp
  funext i
  have hi := i.isLt
  by_cases hlo : i.val < r
  · have hi' : i = eI k r ⟨i.val, hlo⟩ := Fin.ext (by simp [eI])
    rw [hi', ← ffa_herm_esI (n *ᵥ w), ← ffa_herm_esI w]
    conv_lhs => rw [← (hG ⟨i.val, hlo⟩ (hlast _)).2]
    exact ffa_herm_UH hU w _
  by_cases hhi : r + k < i.val
  · have hb : 2 * r + k - i.val < r := by omega
    have hi' : i = esI k r ⟨2 * r + k - i.val, hb⟩ := Fin.ext (by simp [esI]; omega)
    rw [hi', ← herm_bvec_eI_quadratic_form_two_two (n *ᵥ w), ← herm_bvec_eI_quadratic_form_two_two w]
    conv_lhs => rw [← (hG ⟨2 * r + k - i.val, hb⟩ (hlast _)).1]
    exact ffa_herm_UH hU w _
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [h3 i i (by omega) (by omega) (by omega), if_pos rfl, one_mul]
  · intro j _ hji
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [h3 i j hj.1 hj.2 (by omega), if_neg (Ne.symm hji), zero_mul]
    · rw [hw j (by omega), mul_zero]
  · simp
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
