-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.traceDualGe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:41.551955+00:00
-- url     : https://prove2.me/submissions/5649a74c-7e24-4d88-98b5-235d88535f26

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitPrimeToDifferent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x4_mem_twLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x4_mem_idl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x4_trace_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x4_exists_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x4
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.DualSupset := by
  intro E _ _ _ hU g ν s hg l hl t ht
  have hrel : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
    have h := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ
      (𝓞 (maximalRealSubfield E)) (𝓞 E)
    unfold Unram at hU
    have h0 : (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
        (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≠ ⊥ := by
      rw [← hU]; exact differentIdeal_ne_bot
    rw [hU] at h
    have h2 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) *
        (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
        1 * (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by rw [one_mul]; exact h.symm
    simpa using mul_right_cancel₀ h0 h2
  obtain ⟨θ, hθ⟩ := exists_theta E hrel
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have hd : dd E ≠ 0 := by
    unfold dd
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hdual : dd E ^ (-(ν + 1)) * dd E ^ ν = FractionalIdeal.dual ℤ ℚ (1 : FI E) := by
    rw [← zpow_add₀ hd, show -(ν + 1) + ν = -1 by ring, zpow_neg_one]
    unfold dd
    rw [coeIdeal_differentIdeal ℤ ℚ, inv_inv]
  unfold perLat at ht
  unfold dualIdl at hl
  rw [mem_twLat, mem_idl E g _ _ _ hg, mem_idl E g _ _ _ hg] at hl ht
  obtain ⟨hl1, hl2⟩ := hl
  obtain ⟨ht1, ht2⟩ := ht
  set ε : E := (-1) ^ s with hε
  have hεε : ε * ε = 1 := by rw [hε, ← pow_add, ← two_mul, pow_mul]; simp
  have hεc : complexConj E ε = ε := by rw [hε, map_pow, map_neg, map_one]
  set x : E := l * t / g with hx
  have hy : x + complexConj E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FI E) := by
    rw [← hdual]
    have m1 := FractionalIdeal.mul_mem_mul hl2 ht1
    have m2 := FractionalIdeal.mul_mem_mul hl2 ht2
    have m3 := FractionalIdeal.mul_mem_mul hl1 ht2
    have m2' := (dd E ^ (-(ν + 1)) * dd E ^ ν : FI E).coeToSubmodule.smul_mem (g : 𝓞 E) m2
    have m := (dd E ^ (-(ν + 1)) * dd E ^ ν : FI E).coeToSubmodule.add_mem
      ((dd E ^ (-(ν + 1)) * dd E ^ ν : FI E).coeToSubmodule.sub_mem m1 m2') m3
    have e : x + complexConj E x =
        (l - (-1) ^ (s + 1) * complexConj E l) / (g : E) ^ (0 : ℤ) * (t / (g : E) ^ (1 : ℤ))
          - (g : 𝓞 E) • ((l - (-1) ^ (s + 1) * complexConj E l) / (g : E) ^ (0 : ℤ)
            * ((t - ε * complexConj E t) / (g : E) ^ (2 : ℤ)))
          + l / (g : E) ^ (-1 : ℤ) * ((t - ε * complexConj E t) / (g : E) ^ (2 : ℤ)) := by
      rw [Algebra.smul_def, hx, map_div₀, map_mul, map_natCast, map_natCast, pow_succ, ← hε,
        zpow_zero, zpow_one, zpow_neg_one, zpow_ofNat]
      field_simp
      linear_combination (-(complexConj E l * complexConj E t)) * hεε
    rw [e]
    exact m
  have hz := (FractionalIdeal.mem_dual (one_ne_zero : (1 : FI E) ≠ 0)).1 hy (θ : E)
    ((FractionalIdeal.mem_one_iff _).2 ⟨θ, rfl⟩)
  rw [Algebra.traceForm_apply] at hz
  have e : Algebra.trace ℚ E ((x + complexConj E x) * (θ : E)) = Algebra.trace ℚ E x := by
    rw [add_mul, map_add, ← trace_conj E (complexConj E x * (θ : E)), map_mul (complexConj E),
      complexConj_apply_apply, ← map_add, ← mul_add, hθ, mul_one]
  rw [e] at hz
  exact hz
end Formalism.FourierDecayAlt.P
