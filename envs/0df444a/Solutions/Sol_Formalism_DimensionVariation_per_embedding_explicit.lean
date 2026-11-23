-- Prove2me | solution 1 for Formalism.DimensionVariation.per_embedding_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:21.956696+00:00
-- url     : https://prove2.me/submissions/1b5e2962-e5c3-4dbe-a9db-f65baaf855bb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_DimensionVariation_first_descent_explicit

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
theorem _root_.solution : PerEmbedding6 := by
  intro J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' logOm v f m N L La logT logg
    C2 C3 C4 c5 c6 C7 C8 C0 h32 hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  obtain ⟨d1, -⟩ := first_descent_explicit J Pl Emb r ν g0 (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v) MainNotions logOmτ
    logth0 logh logh'
    (fun j => (∑ s, liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) / (Fintype.card Emb : ℝ))
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 (fun j s => le_refl _) (fun j => rfl)
    hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have hE : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨fun j => sizeB ν logOm f m N L La C0 j -
      (∑ s, liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) / (Fintype.card Emb : ℝ), ?_, ?_, ?_⟩
  · intro j
    have e1 := d1 j
    simp only at e1 ⊢
    linarith
  · intro j s
    have e1 := d1 j
    have e3 := h32 j s
    simp only at e1 e3 ⊢
    linarith
  · intro j
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
      mul_div_cancel_left₀ _ hE.ne']
    ring
end Formalism.DimensionVariation
