-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.n_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:56:14.395804+00:00
-- url     : https://prove2.me/submissions/8fc1aea7-8787-4974-b342-78b44fe30b8f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_row
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_row__71270a473e04

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} (hz : inWb k r z) {m : Mx k r}
    (hm : m ∈ Nlev k r i) : m *ᵥ fvec k r z i = fvec k r z i := by
  unfold Nlev at hm
  simp only [QuantumDeterminants.Nset, Set.mem_inter_iff, Set.mem_setOf_eq] at hm
  obtain ⟨⟨_, hcol, hmid⟩, hG⟩ := hm
  unfold inWb at hz
  unfold fvec
  split_ifs with hi
  · funext x
    rw [show (m *ᵥ bvec (eI k r ⟨i.val, hi⟩)) x = m x (eI k r ⟨i.val, hi⟩) by
      simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]]
    by_cases hx : i.val ≤ x.val
    · rw [hcol ⟨i.val, hi⟩ x hx]
      simp [bvec, Pi.single_apply]
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      rw [glev_row' hG x (eI k r ⟨i.val, hi⟩) hout]
  · funext x
    by_cases hx : r ≤ x.val
    · simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single x]
      · by_cases hxk : x.val ≤ r + k
        · rw [hmid x x hx hxk hx]
          simp
        · rw [hz x (Or.inr (by omega)), mul_zero]
      · intro j _ hj
        by_cases hjm : r ≤ j.val ∧ j.val ≤ r + k
        · rw [hmid x j hjm.1 hjm.2 hx, if_neg (Ne.symm hj), zero_mul]
        · rw [hz j (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      exact glev_row hG x hout z
end Formalism.FourierDecayAlt.Q.TInvW
