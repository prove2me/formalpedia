-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.cdiag_mem_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:43.669868+00:00
-- url     : https://prove2.me/submissions/54d73060-802a-4f35-9884-5927c070f01b

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_NContract
import Theorems.Thm_CompanionTheory_D_Upq_QuotSetU_expo_add_piI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_apply


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
theorem _root_.solution {t : ℝ} (ht : t ≠ 0) : cdiag k r t ∈ UH (Hpk k r) := by
  show (cdiag k r t)ᴴ * Hpk k r * cdiag k r t = Hpk k r
  ext i j
  rw [cdiag, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Hpk_apply]
  split_ifs with h
  · subst h
    have e : star (dvec (k := k) (r := r) t) i * dvec t (piI k r i) = 1 := by
      rw [Pi.star_apply, dvec, dvec, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        ← zpow_add₀ ht, expo_add_piI, zpow_zero, Complex.ofReal_one]
    calc star (dvec (k := k) (r := r) t) i * epsI k r i * dvec t (piI k r i)
        = epsI k r i * (star (dvec (k := k) (r := r) t) i * dvec t (piI k r i)) := by ring
      _ = epsI k r i := by rw [e, mul_one]
  · simp
end CompanionTheory.D.Upq.QuotSetU
