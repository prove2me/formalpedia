-- Prove2me | solution 1 for Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower.rv_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:52.567991+00:00
-- url     : https://prove2.me/submissions/2c1af16e-2919-45a2-a971-7794572ee940

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven
import Theorems.Thm_Formalism_HermitianLattices_WeilRepresentation_CocycleEighthPower_rv_sumexp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
open Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
theorem _root_.solution : GramExpansion := by
  intro Z O M Q _ _ _ _ _ _ _ φ nm hadd hadj hnm n _ k A u
  classical
  have hs := rv_sumexp M Q φ hadd k
  have h00 : ∀ b, cob φ 0 b = 0 := by
    intro b; have := hadd 0 0 b; simpa using this
  have hsumF : ∀ (s : Finset n) (c : n → M) (b : M),
      cob φ (∑ i ∈ s, c i) b = ∑ i ∈ s, cob φ (c i) b := by
    intro s c b
    induction s using Finset.induction_on with
    | empty => simp [h00]
    | insert a s ha ih => rw [sum_insert ha, sum_insert ha, hadd, ih]
  simp_rw [hs, hnm]
  rw [sum_add_distrib]
  congr 1
  · rw [sum_comm]; simp [sum_smul]
  · rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun j' _ => ?_
    rw [sum_smul, hsumF]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_smul, hadj (star (A i j')) (A i j • u j) (u j'), star_star]
end Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
