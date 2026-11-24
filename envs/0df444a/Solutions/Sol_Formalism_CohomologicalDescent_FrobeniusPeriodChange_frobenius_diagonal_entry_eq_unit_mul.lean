-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.frobenius_diagonal_entry_eq_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:49.901579+00:00
-- url     : https://prove2.me/submissions/8b8f922a-8316-40b5-b69d-77cd6b345d98

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_diagonal_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_map_X_sub_C_prime_pow_eq_X_pow
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_rank_one_model_holds

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
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (wt kap : ι → Fin t → ℤ) (hW : WInputs W σ l h u c U' wt kap) (i : ι) (s : Fin t) :
    0 ≤ (l : ℤ) * kap (σ i) s + wt i s - kap i s ∧
      ∃ u0 : (F⟦X⟧)ˣ, W.Phi l σ i (W.pos s) (W.pos s) =
        (u0 : F⟦X⟧) * X ^ ((l : ℤ) * kap (σ i) s + wt i s - kap i s).toNat := by
  obtain ⟨⟨hu, -, -⟩, -, hwt, -, -, -, hPhiE, -⟩ := hW.1
  obtain ⟨⟨v, hv⟩, -⟩ := rank_one_model_holds ι l h O F W.red (W.Npsi s) u c (fun i => wt i s) hu
    (hW.2.2 s) i
  have hmv : PowerSeries.map W.red ((W.Npsi s).P i 0 0) =
      ((Units.map (PowerSeries.map W.red).toMonoidHom v : (F⟦X⟧)ˣ) : F⟦X⟧) * X ^ (wt i s).toNat := by
    rw [hv, map_mul, map_X_sub_C_prime_pow_eq_X_pow]
    rfl
  have heq := hPhiE i s
  rw [hmv] at heq
  obtain ⟨h1, u0, hu0⟩ := frobenius_diagonal_holds F l (wt i s).toNat _ _ (W.w i s) (W.w (σ i) s) (kap i s)
    (kap (σ i) s) (Fact.out : l.Prime).pos heq
  have hw : (((wt i s).toNat : ℕ) : ℤ) = wt i s := Int.toNat_of_nonneg (hwt i s).1
  rw [hw] at h1 hu0
  exact ⟨h1, u0, hu0⟩
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
