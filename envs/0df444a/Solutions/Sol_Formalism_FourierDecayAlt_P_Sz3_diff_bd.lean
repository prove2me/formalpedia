-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.diff_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:14.382912+00:00
-- url     : https://prove2.me/submissions/9d0a1a55-ab2e-4533-aab1-ade417efea44

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_sum_de_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_Icc_one_eq

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
theorem _root_.solution (J d : ℕ) (hd : d ≤ J) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) :
    |∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (d : ℝ) ∧
    |∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i| ≤ (J : ℝ) - (d : ℝ) := by
  rw [Icc_one_eq]
  have c1 := Finset.sum_Ioc_consecutive de (Nat.zero_le d) hd
  have c2 := Finset.sum_Ioc_consecutive de (Nat.zero_le (J - d)) (Nat.sub_le J d)
  have b1 := sum_de_bd de hde (Ioc 0 d)
  have b2 := sum_de_bd de hde (Ioc d J)
  have b3 := sum_de_bd de hde (Ioc 0 (J - d))
  have b4 := sum_de_bd de hde (Ioc (J - d) J)
  simp only [Nat.card_Ioc] at b1 b2 b3 b4
  have e1 : ((J - d : ℕ) : ℝ) = (J : ℝ) - d := by rw [Nat.cast_sub hd]
  have e2 : ((J - (J - d) : ℕ) : ℝ) = (d : ℝ) := by
    have : J - (J - d) = d := by omega
    rw [this]
  rw [e1] at b2
  rw [Nat.sub_zero] at b1 b3
  rw [e1] at b3
  rw [e2] at b4
  constructor <;> rw [abs_le] <;> constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2]
end Formalism.FourierDecayAlt.P.Sz3
