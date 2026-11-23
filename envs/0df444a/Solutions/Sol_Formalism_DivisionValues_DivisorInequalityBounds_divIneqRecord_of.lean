-- Prove2me | solution 1 for Formalism.DivisionValues.DivisorInequalityBounds.divIneqRecord_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:29.426038+00:00
-- url     : https://prove2.me/submissions/550d3bf8-c0b1-4414-8e27-8d1cdb3a396e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_DivisorInequalityBounds_eKaux
import Theorems.Thm_Formalism_DivisionValues_DivisorInequalityBounds_recAux
import Theorems.Thm_Formalism_DivisionValues_DivisorInequalityBounds_constant_factor_le_sixty
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_WeightedPlaceLogSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.DivisorInequalityBounds
namespace Formalism.DivisionValues.DivisorInequalityBounds
theorem _root_.solution (H : TheoremDivIneq) : DivIneqRecord := by
  intro J Pl _ _ TT _ muC mu0 Fo hu hP mlam logT hK aT phν nν fa
    x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 ce Lpass Eb e6 eP logOm eK pq w eE δ
  intro s1 s2 s3 s4 s5 s6 s7 s8 z1 z2 z3 z4 z5 l1 l2 l3 l4 hB0 hNc c1 c2 c3 c4 r1 r2 r3 r4 r5 hw
    g1 g2 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 hC0 hce e1 e2 e3 e4 e5 e6' e7
  have hX : 0 < x ^ eps := Real.rpow_pos_of_pos (by linarith only [z1]) _
  have hb : 0 < b := by rw [z4]; exact Real.exp_pos _
  have hB0' : 0 ≤ B0 := by rw [hB0]; positivity
  obtain ⟨t0, t1, t2, t3⟩ := recAux (x ^ eps) B0 Nc m C0 ce Eb ((Real.log x) ^ 2) ((TT.card : ℝ) * a * La) hX hNc hC0 hce (sq_nonneg _) e2
  have hc : 0 < 50 * C0 + 10 := by linarith only [hC0]
  have hC00 : 0 ≤ C0 := by linarith only [hC0]
  have p2' : N ^ 2 * 1 ≤ b := by rw [mul_one]; exact p2
  have key := H J Pl TT muC mu0 Fo hu hP mlam logT hK aT phν nν fa
    x eps L b a rd La B0 ((Real.log x) ^ 2 * Nc / x ^ eps) (ce / C0 * x ^ eps) m f k N S tt η w'' b' 1 (m * lam0) C0
    Lpass Eb e6 eP logOm eK pq w eE δ
    s1 s2 s3 s4 s5 s6 s7 s8 z1 z2 z3 z4 z5 l1 l2 l3 l4 hB0 t0 t1 c1 c2 c3 c4 r1 r2 r3 r4 r5 le_rfl hw
    g1 g2 p1 p2' p3 p4 p5 p6 p7 p8 p9 p10 hC00 e1 t2
    (fun j => eKaux C0 f N La m L (eK j) hC0 c4 r2 (e3 j))
    e4 e5 e6' e7
  rw [t3] at key
  have hfac : (50 * C0 + 10) * (ce / C0) ≤ 60 * ce := constant_factor_le_sixty C0 ce hC0 (by linarith only [hC0, hce])
  have hnn : 0 ≤ m * (x ^ eps * B0 + (Real.log x) ^ 2 * Nc) :=
    mul_nonneg (by linarith only [c3]) (add_nonneg (mul_nonneg hX.le hB0') (mul_nonneg (sq_nonneg _) hNc))
  have hmul := mul_le_mul_of_nonneg_right hfac hnn
  linarith only [key, hmul]
end Formalism.DivisionValues.DivisorInequalityBounds
