-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crv_vLa_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:32:00.554947+00:00
-- url     : https://prove2.me/submissions/28356373-6f4a-43cb-9360-7e55d23190b2

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Theorems.Thm_Formalism_L2_Pj_Crude_resCharOf_prime
import Theorems.Thm_Formalism_L2_Pj_Crude_crv_vLa_natCast_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
  {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K'] {ι : K →+* K'} {e : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution : vLa la ((resCharOf la : ℕ) : K) = ramOverZ la := by
  rw [crv_vLa_natCast_eq]
  unfold ramOverZ Ideal.ramificationIdx'
  have hr0 : ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (resCharOf_prime la).ne_zero
  have hv0 : la.intValuation ((resCharOf la : ℕ) : 𝓞 K) ≠ 0 := la.intValuation_ne_zero _ hr0
  have e1 : ∀ m : ℤ, la.intValuation ((resCharOf la : ℕ) : 𝓞 K) ≤ WithZero.exp m ↔
      WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K)) ≤ m := by
    intro m
    conv_lhs => rw [← WithZero.exp_log hv0]
    exact WithZero.exp_le_exp
  have key : ∀ n : ℕ, (Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((resCharOf la : ℕ) : ℤ)}) ≤
      la.asIdeal ^ n ↔ (n : ℤ) ≤ -WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K))) := by
    intro n
    rw [Ideal.map_span, Set.image_singleton, map_natCast, ← Ideal.dvd_iff_le,
      ← la.intValuation_le_pow_iff_dvd, e1]
    omega
  have hk : (0 : ℤ) ≤ -WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K)) := by
    exact_mod_cast (key 0).mp (by simp)
  have hS : {n : ℕ | Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {((resCharOf la : ℕ) : ℤ)}) ≤
      la.asIdeal ^ n} = Set.Iic (-WithZero.log (la.intValuation ((resCharOf la : ℕ) : 𝓞 K))).toNat := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    rw [key]
    omega
  rw [hS, csSup_Iic]
  omega
end Formalism.L2.Pj.Crude
