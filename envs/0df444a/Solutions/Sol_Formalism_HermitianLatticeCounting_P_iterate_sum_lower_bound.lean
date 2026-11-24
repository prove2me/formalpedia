-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.iterate_sum_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:36.882246+00:00
-- url     : https://prove2.me/submissions/55d2a6f6-f44a-445e-b8d7-fcb461ffe05f

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sum_fin_succ_cons
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_foldr_ofFn_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R W ι : Type} [CommSemiring R] [PartialOrder R] [IsOrderedRing R] [Fintype ι]
    (Eop : ι → W → W) (Φ : W → R) (κ : R) (hκ : 0 ≤ κ) (h : ∀ w, κ * Φ w ≤ ∑ i, Φ (Eop i w))
    (q : ℕ) (w : W) : κ ^ q * Φ w ≤ ∑ σ : Fin q → ι, Φ ((List.ofFn σ).foldr Eop w) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_fin_succ_cons]
    calc κ ^ (q + 1) * Φ w = κ * (κ ^ q * Φ w) := by ring
      _ ≤ κ * ∑ τ : Fin q → ι, Φ ((List.ofFn τ).foldr Eop w) := mul_le_mul_of_nonneg_left ih hκ
      _ = ∑ τ : Fin q → ι, κ * Φ ((List.ofFn τ).foldr Eop w) := Finset.mul_sum _ _ _
      _ ≤ ∑ τ : Fin q → ι, ∑ i, Φ (Eop i ((List.ofFn τ).foldr Eop w)) :=
          Finset.sum_le_sum fun τ _ => h _
      _ = _ := by simp only [foldr_ofFn_cons]
end Formalism.HermitianLatticeCounting.P
