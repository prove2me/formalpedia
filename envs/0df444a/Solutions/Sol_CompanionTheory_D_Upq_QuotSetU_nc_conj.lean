-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.nc_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:24.246609+00:00
-- url     : https://prove2.me/submissions/69df8462-0751-4274-9522-b8e87eada845

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.QuotSetU
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution {a b m : 𝕄} (ha : WB k r a) (hb : WB k r b) (hab : a * b = 1) (hm : NC k r m) :
    NC k r (a * m * b) := by
  intro i j hj hi
  by_cases hjr : j.val < r
  ·
    have hjW : ¬ inW k r j := by unfold inW; omega
    have hji : j.val ≤ i.val := by omega
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hb j j (fun h => hjW h.2), if_pos rfl, mul_one, Matrix.mul_apply,
        Finset.sum_eq_single j]
      · rw [hm j j hj (by omega), if_pos rfl, mul_one]
        exact ha i j (fun h => hjW h.2)
      · intro p _ hpj
        by_cases hp : j.val ≤ p.val
        · rw [hm p j hj (by omega), if_neg hpj, mul_zero]
        · have hpW : ¬ inW k r p := by unfold inW; omega
          have hip : i ≠ p := by intro e; subst e; omega
          rw [ha i p (fun h => hpW h.2), if_neg hip, zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h
    · intro q _ hqj
      rw [hb q j (fun h => hjW h.2), if_neg hqj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  ·
    have hjW : inW k r j := by unfold inW; omega
    have hir : r ≤ i.val := by omega
    have key : ∀ q : Fin (2 * r + k + 1), (a * m) i q * b q j = a i q * b q j := by
      intro q
      by_cases hqW : inW k r q
      · congr 1
        rw [Matrix.mul_apply, Finset.sum_eq_single q]
        · rw [hm q q hqW.2 (by unfold inW at hqW; omega), if_pos rfl, mul_one]
        · intro p _ hpq
          by_cases hp : r ≤ p.val
          · rw [hm p q hqW.2 (by unfold inW at hqW; omega), if_neg hpq, mul_zero]
          · have hpW : ¬ inW k r p := by unfold inW; omega
            have hip : i ≠ p := by intro e; subst e; omega
            rw [ha i p (fun h => hpW h.2), if_neg hip, zero_mul]
        · intro h; exact absurd (Finset.mem_univ q) h
      · have hqj : q ≠ j := by intro e; subst e; exact hqW hjW
        rw [hb q j (fun h => hqW h.1), if_neg hqj, mul_zero, mul_zero]
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun q _ => key q), ← Matrix.mul_apply, hab,
      Matrix.one_apply]
end CompanionTheory.D.Upq.QuotSetU
