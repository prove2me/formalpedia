-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwin_weight_ht
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:29.829977+00:00
-- url     : https://prove2.me/submissions/97e9a3d9-4a78-41de-92eb-bcc7e6647db6

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (lhwinHt r n) d =
      ∑ a : Fin r, (a.val : ℤ) * ((Finsupp.weight (rowW r n) d a : ℕ) : ℤ) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib, hf, hg]
  | single v c =>
    simp [Finsupp.weight_apply, lhwinHt, rowW, Pi.single_apply, Finsupp.sum_single_index, mul_comm]
end Formalism.GradedWeylDivisibility
