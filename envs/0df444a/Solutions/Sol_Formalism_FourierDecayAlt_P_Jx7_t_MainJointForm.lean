-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_MainJointForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:50.386012+00:00
-- url     : https://prove2.me/submissions/c33e1ac3-5d64-44dc-84e9-7b857bea5e10

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_SizesToRecursion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_jn_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : MainJointForm := by
  intro hA hS C₁ C₄ Cthr h1 h4
  obtain ⟨CT, CT', hT⟩ := hA C₁ C₄ h1 h4
  refine ⟨max (max Cthr 1) |CT|, |CT|, le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), abs_nonneg _, le_max_right _ _, ?_⟩
  intro C0 CG CDel cT Cb hC0 hCG hCDel hcT hCb hcTb
  obtain ⟨k0, hk0⟩ := t_SizesToRecursion hS (max (max Cthr 1) |CT|) C0 CG CDel cT Cb |CT| CT'
    (le_trans (le_max_right _ _) (le_max_left _ _)) hC0 hCG hCDel hcT hCb hcTb (abs_nonneg _)
    (le_max_right _ _)
  refine ⟨k0, ?_⟩
  intro ι _ G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf E W _ D jn H _ _ _ Vt c hr hf hrec he
    P _ B he1 hI hδ hrow
  obtain ⟨s1, s2, s3, s4, s5⟩ := hk0 ι G bb Cp Cf Th de de' T T' du du' l hk hyp h16 hCf
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hrec
  have hjn := jn_nonneg D jn a5 a15
  have habs : (CT / Th) ^ D.f ≤ (|CT| / Th) ^ D.f := by
    calc (CT / Th) ^ D.f ≤ |(CT / Th) ^ D.f| := le_abs_self _
      _ = (|CT| / Th) ^ D.f := by rw [abs_pow, abs_div, abs_of_pos a3]
  have hpn : 0 ≤ (|CT| / Th) ^ D.f := by positivity
  have hr0 : (0 : ℝ) ≤ D.r := Nat.cast_nonneg _
  have hsm : (D.r : ℝ) * (CT / Th) ^ D.f ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left habs hr0) ?_
    rw [hr, hf]; exact s3
  have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) = B.e1 := by
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ D.r + 1),
      Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), one_mul, he1]
  have he0 : 0 ≤ D.e (D.r + 1) := (a9 (D.r + 1) 1 le_rfl (by omega) le_rfl).1.1
  have he1p : 0 ≤ B.e1 := by rw [← he1]; linarith
  refine ⟨?_, ?_, ?_⟩
  · have key := hrow ((1 + B.δ) * B.e1 * B.IntN) (fun R => by
      have := hT E W D Th jn H Vt c a1 a2 a3 s1 hsm a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R
      rw [hprod] at this
      refine le_trans this ?_
      rw [hδ, hI]
      have h2 : CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f ≤
          |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
        calc CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f
            ≤ |CT * ((D.r : ℝ) + 1) * (CT / Th) ^ D.f| := le_abs_self _
          _ = |CT| * ((D.r : ℝ) + 1) * (|CT| / Th) ^ D.f := by
              rw [abs_mul, abs_mul, abs_pow, abs_div, abs_of_pos a3,
                abs_of_nonneg (by linarith : (0:ℝ) ≤ (D.r : ℝ) + 1)]
      apply mul_le_mul_of_nonneg_right _ hjn
      apply mul_le_mul_of_nonneg_right _ he1p
      linarith)
    calc B.c0 * B.c0' * B.KV ≤ B.n0c * ((1 + B.δ) * B.e1 * B.IntN) := key
      _ = _ := by ring
  · rw [hδ]; positivity
  · rw [hδ, hr, hf]; exact s5
end Formalism.FourierDecayAlt.P.Jx7
