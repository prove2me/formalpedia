-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.exists_tp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:35.274185+00:00
-- url     : https://prove2.me/submissions/32e296a6-dca7-45fe-8f53-a68494c17c27

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_ee_eq_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution (n : ℕ) : ∃ (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ), ∀ y : Fin d → ℝ,
    tp B c y = ∏ j, (1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))) ^ n := by
  have hinj : Function.Injective (fun (p : Fin d → ℕ) (j : Fin d) => (p j : ℤ)) := by
    intro p q h
    funext j
    have := congrFun h j
    simpa using this
  refine ⟨(Fintype.piFinset fun _ : Fin d => Finset.range (n + 1)).map ⟨_, hinj⟩,
    fun σ => ∏ j, (n.choose (σ j).toNat : ℂ), fun y => ?_⟩
  unfold tp
  rw [Finset.sum_map]
  simp_rw [add_comm (1 : ℂ), add_pow, one_pow, mul_one]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [ee_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [Function.Embedding.coeFn_mk, Int.toNat_natCast]
  rw [mul_comm, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring
end Formalism.FourierDecayAlt.P.HLsc
