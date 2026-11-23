-- Prove2me | solution 1 for Formalism.DimensionVariation.first_descent_product_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:57.711992+00:00
-- url     : https://prove2.me/submissions/27b795d5-15ca-4bfa-8cad-40e64db2ab44

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_DimensionVariation_first_descent_explicit
import Theorems.Thm_Formalism_DimensionVariation_size_at_embedding


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
theorem _root_.solution : StepDiProd6 := by
  intro J Pl Emb _ _ _ _ r ν n g0 Ksq kc Om th0sq hcl hcl' hK logOm v f m N L La logT logg
    C2 C3 C4 c5 c6 C7 C8 C0 hn hK0 hkc hOm0 hth0 hh0 hh0' hv hprod hmean hOm hSK hth hh hh' hcard hg0
    hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  refine first_descent_explicit J Pl Emb r ν (fun j => (g0 j : ℝ)) (fun j s => Real.log (Ksq j s))
    (fun j s => Real.log (kc j s)) (fun τ s => Real.log (Om τ s)) (fun s => Real.log (th0sq s))
    (fun j => Real.log (hcl j)) (fun j => Real.log (hcl' j)) hK logOm v f m N L La logT logg
    C2 C3 C4 c5 c6 C7 C8 C0 ?_ hmean hOm hSK hth hh hh' hcard
    (fun j => ⟨Nat.cast_nonneg _, hg0 j⟩) hm hN hL hLLa hLa ?_ ?_ hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  · intro j s
    have hM : (0 : ℝ) < 8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v := by positivity
    have := size_at_embedding Pl r (g0 j) (ν j) (n j) (fun τ => Om τ s) (Ksq j s) (kc j s)
      ((8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j))
      (th0sq s ^ (Fintype.card Pl * g0 j)) (hcl j * hcl' j) (hK0 j s) (hkc j s) (pow_pos hM _)
      (pow_pos (hth0 s) _) (mul_pos (hh0 j) (hh0' j)) (fun τ => hOm0 τ s) (hprod j s)
    rw [Real.log_pow, Real.log_pow, Real.log_mul (hh0 j).ne' (hh0' j).ne'] at this
    unfold liftedMapLogSize
    simp only [hn]
    push_cast at this ⊢
    linarith
  · intro j
    have := h5 j
    push_cast at this ⊢
    exact this
  · intro j τ
    rw [hn]; exact h6 j τ
end Formalism.DimensionVariation
