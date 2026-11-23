-- Prove2me | solution 1 for Formalism.DimensionVariation.heightBound6_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:43.450177+00:00
-- url     : https://prove2.me/submissions/55e305ff-1867-4509-8dfd-7b894d1829af

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_DimensionVariation_per_embedding_explicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : HeightBound6 := by
  intro J Pl Emb Frm _ _ _ _ _ _ r ν g0 logB logP logK MainNotions loglam logOmτ logth0 logh logh' hlam
    hP logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 hC1 hPs h32 hlm hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  obtain ⟨cst, c0, c1, c2⟩ := per_embedding_explicit J Pl Emb r ν g0 logK MainNotions logOmτ logth0 logh logh'
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h32 hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have hE : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hpt : ∀ s, logB s ≤
      hP + ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j) := by
    intro s
    have m1 : (∑ j, hlam j) ≤
        Finset.univ.inf' Finset.univ_nonempty (fun y : Frm => ∑ j, loglam j y s) := by
      refine Finset.le_inf' _ _ (fun y _ => ?_)
      exact Finset.sum_le_sum (fun j _ => hlm j y s)
    have m2 : (∑ j, logK j s) ≤
        ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j) :=
      Finset.sum_le_sum (fun j _ => c1 j s)
    have m3 := hC1 s
    have m4 := hPs s
    rw [Finset.sum_sub_distrib]
    linarith
  have hmean : (∑ s, (hP + ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j))) /
      (Fintype.card Emb : ℝ) = hP + ∑ j, (sizeB ν logOm f m N L La C0 j - hlam j) := by
    have c2' : ∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j)) =
        sizeB ν logOm f m N L La C0 j * (Fintype.card Emb : ℝ) :=
      fun j => (div_eq_iff hE.ne').mp (c2 j)
    rw [div_eq_iff hE.ne', Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_comm]
    have : ∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j)) =
        (sizeB ν logOm f m N L La C0 j - hlam j) * (Fintype.card Emb : ℝ) := by
      intro j
      rw [Finset.sum_sub_distrib, c2' j, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul]
    ring
  refine ⟨cst, c0, c2, hpt, hmean, ?_⟩
  rw [← hmean]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun s _ => hpt s)) hE.le
end Formalism.DimensionVariation
