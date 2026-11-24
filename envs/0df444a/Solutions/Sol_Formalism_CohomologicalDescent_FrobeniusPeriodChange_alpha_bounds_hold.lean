-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.alpha_bounds_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:36.055802+00:00
-- url     : https://prove2.me/submissions/9432666d-0051-488e-9a14-19d3240e23a9

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_block_height_on_line_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_mul_eq_X_pow_smul_one
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_diagonal_entry_eq_unit_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : AlphaBounds := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' wt kap hl2 hW i s
  obtain ⟨h1, u0, hu0⟩ := frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' wt kap hW i s
  refine ⟨h1, ?_⟩
  obtain ⟨M, hM⟩ := frobenius_mul_eq_X_pow_smul_one l h W σ u U' hW.2.1 i
  obtain ⟨-, -, -, ⟨-, hb⟩, hPhiT, -, -, -⟩ := hW.1
  have hline := block_height_on_line_holds (F⟦X⟧) X n h (W.Phi l σ i) M W.b (W.pos s) X_ne_zero
    (hPhiT i) hM (hb s)
  rw [hu0] at hline
  set e := (l : ℤ) * kap (σ i) s + wt i s - kap i s with he
  have hdvd : (X : F⟦X⟧) ^ e.toNat ∣ X ^ h :=
    ⟨u0 * M (W.pos s) (W.pos s), by rw [← hline]; ring⟩
  have hle : e.toNat ≤ h := by
    first
    | exact (pow_dvd_pow_iff X_ne_zero X_prime.not_unit).1 hdvd
    | exact (pow_dvd_pow_iff_le X_ne_zero X_prime.not_unit).1 hdvd
  have h2 : ((e.toNat : ℕ) : ℤ) ≤ (h : ℤ) := by exact_mod_cast hle
  linarith [Int.toNat_of_nonneg h1]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
