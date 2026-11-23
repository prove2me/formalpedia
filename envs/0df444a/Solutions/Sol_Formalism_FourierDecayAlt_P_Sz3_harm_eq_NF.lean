-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.harm_eq_NF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:13.77706+00:00
-- url     : https://prove2.me/submissions/dfba54e7-e2a4-4041-8a14-136dd9d74555

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_harmonic_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (J : ℕ) (de : ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, de i * (((harmonic (i - 1) : ℚ) : ℝ) - ((harmonic (J - i) : ℚ) : ℝ)) =
      NF J de := by
  simp_rw [harmonic_real, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, NF]
  simp_rw [sub_div, Finset.sum_div]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm' (t' := Icc 1 J) (s' := fun d => Ioc d J)]
    · apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro i _; ring
    · intro i d; simp only [mem_Icc, mem_Ioc]; omega
  · rw [Finset.sum_comm' (t' := Icc 1 J) (s' := fun d => Icc 1 (J - d))]
    · apply Finset.sum_congr rfl; intro d _; apply Finset.sum_congr rfl; intro i _; ring
    · intro i d; simp only [mem_Icc]; omega
end Formalism.FourierDecayAlt.P.Sz3
