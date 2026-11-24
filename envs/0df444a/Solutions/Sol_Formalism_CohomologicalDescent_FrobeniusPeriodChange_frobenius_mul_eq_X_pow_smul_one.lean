-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.frobenius_mul_eq_X_pow_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:03:35.0108+00:00
-- url     : https://prove2.me/submissions/a606c28a-90f6-4d42-b3b7-fcb61bb02c1b

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_base_change_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_map_X_sub_C_prime_pow_eq_X_pow

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
theorem _root_.solution (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ)
    (hN : LatW l W.N h u U') (i : ι) :
    ∃ M, W.Phi l σ i * M = ((X : F⟦X⟧) ^ h) • (1 : Matrix (Fin n) (Fin n) F⟦X⟧) := by
  obtain ⟨hP, -, -, -, -⟩ := hN
  obtain ⟨M, hM⟩ := hP i
  have hmap : (W.N.P i).map (PowerSeries.map W.red) * M.map (PowerSeries.map W.red) =
      ((X : F⟦X⟧) ^ h) • (1 : Matrix (Fin n) (Fin n) F⟦X⟧) := by
    rw [← Matrix.map_mul, hM]
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · simp only [mul_one, map_X_sub_C_prime_pow_eq_X_pow]
    · simp only [mul_zero, map_zero]
  exact (frobenius_base_change_holds F n l h (W.g i) (W.g (σ i)) _ (Fact.out : l.Prime).pos).1 ⟨_, hmap⟩
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
