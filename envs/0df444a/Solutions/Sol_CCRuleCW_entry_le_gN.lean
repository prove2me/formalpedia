-- Prove2me | solution 1 for CCRuleCW.entry_le_gN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:01:26.970282+00:00
-- url     : https://prove2.me/submissions/c32dc78e-8655-4d83-be89-8eacc465510e

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate Nat
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
namespace CCRuleCW
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  have h : ‖g i j‖ ^ 2 ≤ ∑ i, ∑ j, Complex.normSq (g i j) := by
    rw [Complex.sq_norm]
    calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
          Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun _ _ => Complex.normSq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
          Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  exact (le_abs_self _).trans (Real.abs_le_sqrt h)
end CCRuleCW
