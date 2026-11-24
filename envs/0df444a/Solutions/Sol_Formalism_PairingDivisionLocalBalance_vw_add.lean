-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.vw_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:12.518076+00:00
-- url     : https://prove2.me/submissions/fee62825-e7ae-4cf4-9a09-1d01c0f9d4ea

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_ValAdd
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_add_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
namespace Formalism.PairingDivisionLocalBalance
section Val
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem vw_mul_lemma (w : Pl K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold Formalism.DivisionValues.vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul]
  · exact fun h => ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
  · exact fun h => hb (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
private theorem vw_div_eq_sub_of_ne_zero (w : Pl K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a / b) = vw w a - vw w b := by
  have h1 := vw_mul_lemma w (a / b) b (div_ne_zero ha hb) hb
  rw [div_mul_cancel₀ a hb] at h1
  omega
private theorem min_vw_le_vw_add_of_ne_zero (w : Pl K) (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) :
    min (vw w (algebraMap (𝓞 K) K x)) (vw w (algebraMap (𝓞 K) K y)) ≤
      vw w (algebraMap (𝓞 K) K (x + y)) :=
  vw_add_int w x y hx hy hxy
end Val
end Formalism.PairingDivisionLocalBalance
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.PairingDivisionLocalBalance
theorem _root_.solution (w : Pl K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (vw w a) (vw w b) ≤ vw w (a + b) := by
  obtain ⟨x, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  obtain ⟨y, e, he, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) b
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have he0 : algebraMap (𝓞 K) K e ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors he
  have hde : algebraMap (𝓞 K) K (d * e) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hd0 he0
  have h1 : algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K d =
      algebraMap (𝓞 K) K (x * e) / algebraMap (𝓞 K) K (d * e) := by
    rw [div_eq_div_iff hd0 hde, map_mul, map_mul]; ring
  have h2 : algebraMap (𝓞 K) K y / algebraMap (𝓞 K) K e =
      algebraMap (𝓞 K) K (y * d) / algebraMap (𝓞 K) K (d * e) := by
    rw [div_eq_div_iff he0 hde, map_mul, map_mul]; ring
  rw [h1] at ha hab ⊢
  rw [h2] at hb hab ⊢
  rw [← add_div, ← map_add (algebraMap (𝓞 K) K)] at hab ⊢
  have nz : ∀ z : 𝓞 K, z ≠ 0 → algebraMap (𝓞 K) K z ≠ 0 := fun z hz h =>
    hz ((IsFractionRing.injective (𝓞 K) K) (by rw [h, map_zero]))
  have hxe : x * e ≠ 0 := fun h => ha (by rw [h, map_zero, zero_div])
  have hyd : y * d ≠ 0 := fun h => hb (by rw [h, map_zero, zero_div])
  have hs : x * e + y * d ≠ 0 := fun h => hab (by rw [h, map_zero, zero_div])
  rw [vw_div_eq_sub_of_ne_zero w _ _ (nz _ hxe) hde, vw_div_eq_sub_of_ne_zero w _ _ (nz _ hyd) hde,
    vw_div_eq_sub_of_ne_zero w _ _ (nz _ hs) hde, min_sub_sub_right]
  exact sub_le_sub_right (min_vw_le_vw_add_of_ne_zero w _ _ hxe hyd hs) _
end Formalism.PairingDivisionLocalBalance
