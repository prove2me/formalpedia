-- Prove2me | solution 1 for Formalism.GM.mahler_binomial_unit_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:14.652854+00:00
-- url     : https://prove2.me/submissions/5eeda4d3-be3c-4943-b1b3-f0fea0e5959a

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MahlerK
import Theorems.Thm_Formalism_GM_mahler_disc_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Polynomial
namespace Formalism.GM
theorem _root_.solution : MahlerK := by
  intro p hp K _ _ h k t₀ hk m
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  set P : ℚ[X] := Polynomial.C ((k.factorial : ℚ)⁻¹) *
    (descPochhammer ℚ k).comp (Polynomial.C ((p : ℚ) ^ h) * X + Polynomial.C (t₀ : ℚ)) with hP
  have hmap : P.map (Rat.castHom K) =
      (binK K k).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K)) := by
    rw [hP, binK, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, descPochhammer_map,
      mul_comp, C_comp]
    simp
  rw [← hmap, Polynomial.coeff_map]
  have h1 := mahler_disc_bound p h k t₀ hp.out hk m
  rw [← hP] at h1
  have h2 : ((Rat.castHom K) (P.coeff m)) = algebraMap ℚ_[p] K ((P.coeff m : ℚ) : ℚ_[p]) := by
    rw [map_ratCast]; rfl
  rw [h2, norm_algebraMap', Padic.eq_padicNorm]
  exact_mod_cast h1
end Formalism.GM
