-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.tgood_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:43:30.671833+00:00
-- url     : https://prove2.me/submissions/13097454-f1ce-4015-884a-6885ee71f5f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open MvPolynomial
variable {σ : Type*}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (w : σ → ℕ) (c : ℕ) {d₁ d₂ : ℕ} {F G : Polynomial (MvPolynomial σ ℂ)}
    (hF : TGood w c d₁ F) (hG : TGood w c d₂ G) : TGood w c (d₁ + d₂) (F * G) := by
  classical
  intro j m h
  rw [Polynomial.coeff_mul, coeff_sum] at h
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_mul] at hx0
  obtain ⟨y, hy, hy0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  have h1 := hF x.1 y.1 (left_ne_zero_of_mul hy0)
  have h2 := hG x.2 y.2 (right_ne_zero_of_mul hy0)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  rw [← hx, ← hy, map_add, ← h1, ← h2]
  ring
end Formalism.L2.SG.Pf.ColDictValCPf
