-- Prove2me | solution 1 for Formalism.L2.G.ServJoint.vAdd_eq_vw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:14.729653+00:00
-- url     : https://prove2.me/submissions/610ee471-3651-4617-a126-d64252d5c106

import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_JointServices_VAddEqVw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions (vAdd)
open Formalism.DivisionValues (vw)
noncomputable section
namespace Formalism.L2.G.ServJoint
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem vAdd_mul_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold Formalism.BasicNotions.vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]
  ring
private theorem vw_mul_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    Formalism.DivisionValues.vw w (x * y) = Formalism.DivisionValues.vw w x + Formalism.DivisionValues.vw w y := by
  have hx' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hx
  have hy' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hy
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K w hx' hy']
private theorem vAdd_algebraMap_eq_vw_of_ne_zero (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    vAdd w (algebraMap (𝓞 K) K a) = Formalism.DivisionValues.vw w (algebraMap (𝓞 K) K a) := by
  have hI : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  unfold Formalism.BasicNotions.vAdd Formalism.DivisionValues.vw
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha, WithZero.log_exp,
    neg_neg, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hI]
end Formalism.L2.G.ServJoint
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions (vAdd)
open Formalism.DivisionValues (vw)
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.ServJoint
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.G.ServJoint
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) : vAdd w x = vw w x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h; apply hx; rw [h, zero_div]
  have ha0 : a ≠ 0 := by
    rintro rfl; exact haK (map_zero _)
  have hq : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K b = algebraMap (𝓞 K) K a :=
    div_mul_cancel₀ _ hbK
  have h1 := vAdd_mul_of_ne_zero w hx hbK
  have h2 := vw_mul_of_ne_zero w hx hbK
  rw [hq] at h1 h2
  have e1 := vAdd_algebraMap_eq_vw_of_ne_zero w a ha0
  have e2 := vAdd_algebraMap_eq_vw_of_ne_zero w b hb0
  linarith
end Formalism.L2.G.ServJoint
