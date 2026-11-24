-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.dvd_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:17.424283+00:00
-- url     : https://prove2.me/submissions/491c7124-b0ce-4d43-b8bf-c850400839ab

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_gs_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_gs_ne_zero
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_gs_map
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_prim_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_aut
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_fix
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_cop_of_mod_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_eq_zero_of_neg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] (hp4 : p % 4 = 3) {m : ℕ} [NeZero m] (y : Cyc m)
    (hy : y ^ 2 = -(p : Cyc m)) : p ∣ m := by
  by_contra hpm
  have hp3 : 3 ≤ p := by omega
  haveI : NeZero (m * p) := ⟨mul_ne_zero (NeZero.ne m) hp.out.ne_zero⟩
  have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm).symm
  obtain ⟨v, hv1, hv2⟩ := Nat.chineseRemainder hcop 1 (p - 1)
  have hvm : v.Coprime m := cop_of_mod_one hv1
  have hvp : v.Coprime p := by
    apply Nat.Coprime.symm
    apply (Nat.Prime.coprime_iff_not_dvd hp.out).mpr
    intro hdv
    have h0 : v % p = 0 := Nat.mod_eq_zero_of_dvd hdv
    have h1 : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : v % p = (p - 1) % p := hv2
    rw [h0, h1] at h2
    omega
  have hv' : (v : ZMod p) = -1 := by
    have h1 : (v : ZMod p) = ((p - 1 : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff' v (p - 1) p).mpr hv2
    rw [h1, Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self, Nat.cast_one, zero_sub]
  obtain ⟨σ, hσ⟩ := aut (m * p) v (Nat.Coprime.mul_right hvm hvp)
  obtain ⟨ι⟩ := emb m (m * p) (dvd_mul_right m p)
  have hσy : σ (ι y) = ι y := fix (dvd_mul_right m p) ι σ v hσ hv1 y
  obtain ⟨x, hx⟩ : ∃ x : Cyc (m * p), IsPrimitiveRoot x p := ⟨_, prim_pow (dvd_mul_left p m)⟩
  have hσx : σ x = x ^ v := hσ x (by rw [pow_mul', hx.pow_eq_one, one_pow])
  have hσg : σ (gs p hx.pow_eq_one) = -gs p hx.pow_eq_one :=
    gs_map hp4 hx.pow_eq_one (σ : Cyc (m * p) →+* Cyc (m * p)) v hσx hv'
  have hyN : (ι y) ^ 2 = -(p : Cyc (m * p)) := by rw [← map_pow, hy, map_neg, map_natCast]
  have hg2 : (gs p hx.pow_eq_one) ^ 2 = -(p : Cyc (m * p)) := gs_sq hp4 hx
  have hfac : (ι y - gs p hx.pow_eq_one) * (ι y + gs p hx.pow_eq_one) = 0 := by
    linear_combination hyN - hg2
  apply gs_ne_zero hp4 hx
  apply eq_zero_of_neg_eq
  rcases mul_eq_zero.mp hfac with h1 | h1
  · have e1 : ι y = gs p hx.pow_eq_one := sub_eq_zero.mp h1
    rw [e1] at hσy
    rw [← hσg, hσy]
  · have e2 : ι y = -gs p hx.pow_eq_one := eq_neg_of_add_eq_zero_left h1
    rw [e2, map_neg, neg_inj] at hσy
    rw [← hσg, hσy]
end Formalism.FrobeniusOrbits.Cond
