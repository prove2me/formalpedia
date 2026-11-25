-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Decomp.hPart_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:55.432597+00:00
-- url     : https://prove2.me/submissions/38230dfd-8598-4099-8469-a387d30cf340

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_mem_P_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_hcl_at_one
import Theorems.Thm_P2M_Formalism_FrobeniusOrbits_Decomp_hcl_neg_one__ac824373ef67

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Decomp
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Decomp
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]
    (P : Ideal (𝓞 (hostE ζ a b))) [Q.LiesOver P] (ρ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hρ : ∀ x : 𝓞 (hostE ζ a b), ρ • x - x ∈ P) : (galE e ζ a b ρ).2 = 1 := by
  show hPart e ζ a b ρ = 1
  unfold hPart
  split_ifs with hex
  swap
  · rfl
  have hu := Classical.choose_spec hex
  generalize Classical.choose hex = u at hu ⊢
  obtain ⟨n, hn⟩ : ∃ n, (u : ZMod (2 ^ (e + 2))).val = n := ⟨_, rfl⟩
  rw [hn] at hu
  have hnu : ((n : ℕ) : ZMod (2 ^ (e + 2))) = u := by
    rw [← hn]
    exact ZMod.natCast_zmod_val _
  have hprim : IsPrimitiveRoot ζ (2 ^ (e + 2)) := h.1
  have hN1 : 1 ≤ 2 ^ (e + 2) := Nat.one_le_two_pow
  have hζN : ζ ^ (2 ^ (e + 2)) = 1 := hprim.pow_eq_one
  have hinv : ζ⁻¹ = ζ ^ (2 ^ (e + 2) - 1) := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← pow_succ', Nat.sub_add_cancel hN1, hζN]
  have hζint : IsIntegral ℤ ζ := hprim.isIntegral (by positivity)
  have hζiint : IsIntegral ℤ ζ⁻¹ := by
    rw [hinv]
    exact hζint.pow _
  have hθint : IsIntegral ℤ (thE ζ a b) :=
    (isIntegral_algebraMap_iff (algebraMap (hostE ζ a b) L).injective).mp (hζint.add hζiint)
  obtain ⟨zz, hzz⟩ : ∃ z : 𝓞 L, (z : L) = ζ := ⟨⟨ζ, hζint⟩, rfl⟩
  obtain ⟨tt, htt⟩ : ∃ t : 𝓞 (hostE ζ a b), (t : hostE ζ a b) = thE ζ a b := ⟨⟨_, hθint⟩, rfl⟩
  have hth : ((thE ζ a b : hostE ζ a b) : L) = ζ + ζ⁻¹ := rfl
  have hmemQ : algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) ∈ Q := (mem_P_iff P Q _).mp (hρ tt)
  have heq : algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) =
      zz ^ n + zz ^ ((2 ^ (e + 2) - 1) * n) - zz - zz ^ (2 ^ (e + 2) - 1) := by
    ext1
    have e1 : ((algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (ρ • tt - tt) : 𝓞 L) : L) =
        ((ρ (tt : hostE ζ a b) : hostE ζ a b) : L) - ((tt : hostE ζ a b) : L) := by
      first
        | rfl
        | simp
    have e2 : ((zz ^ n + zz ^ ((2 ^ (e + 2) - 1) * n) - zz - zz ^ (2 ^ (e + 2) - 1) : 𝓞 L) : L) =
        (zz : L) ^ n + (zz : L) ^ ((2 ^ (e + 2) - 1) * n) - (zz : L) - (zz : L) ^ (2 ^ (e + 2) - 1) := by
      first
        | rfl
        | simp
    rw [e1, e2, htt, hth, hu, hzz, pow_mul, ← hinv]
    ring
  obtain ⟨zq, hzq⟩ : ∃ w, Ideal.Quotient.mk Q zz = w := ⟨_, rfl⟩
  have hrel : zq ^ n + zq ^ ((2 ^ (e + 2) - 1) * n) = zq + zq ^ (2 ^ (e + 2) - 1) := by
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmemQ
    rw [heq] at h0
    simp only [map_sub, map_add, map_pow, hzq] at h0
    linear_combination h0
  have hzzN : zz ^ (2 ^ (e + 2)) = 1 := by
    ext1
    have e3 : ((zz ^ (2 ^ (e + 2)) : 𝓞 L) : L) = (zz : L) ^ (2 ^ (e + 2)) := by
      first
        | rfl
        | simp
    rw [e3, hzz, hζN]
    all_goals first | rfl | simp
  have hneg : ζ ^ (2 ^ (e + 1)) = -1 := by
    have hsq : ζ ^ (2 ^ (e + 1)) * ζ ^ (2 ^ (e + 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hζN
    rcases mul_self_eq_one_iff.mp hsq with h1 | h1
    · exfalso
      have hdv := (hprim.pow_eq_one_iff_dvd _).mp h1
      have h4 := Nat.le_of_dvd (by positivity) hdv
      have hx : 0 < 2 ^ (e + 1) := by positivity
      have h5 : 2 ^ (e + 2) = 2 * 2 ^ (e + 1) := by ring
      omega
    · exact h1
  have hzzneg : zz ^ (2 ^ (e + 1)) = -1 := by
    ext1
    have e4 : ((zz ^ (2 ^ (e + 1)) : 𝓞 L) : L) = (zz : L) ^ (2 ^ (e + 1)) := by
      first
        | rfl
        | simp
    rw [e4, hzz, hneg]
    all_goals first | rfl | simp
  have h2notQ : (2 : 𝓞 L) ∉ Q := by
    intro h2
    have h2' : (2 : ℤ) ∈ Q.under ℤ := Ideal.mem_comap.mpr (by simpa using h2)
    rw [← (Ideal.LiesOver.over : span {(p : ℤ)} = Q.under ℤ), Ideal.mem_span_singleton] at h2'
    have h6 : p ∣ 2 := by exact_mod_cast h2'
    rcases Nat.prime_two.eq_one_or_self_of_dvd p h6 with h3 | h3
    · exact hp.one_lt.ne' h3
    · exact hp2 h3
  have hfin : zq ^ (2 ^ (e + 2)) = 1 := by
    rw [← hzq, ← map_pow, hzzN, map_one]
  have hnot : ¬ zq ^ (2 ^ (e + 1)) = 1 := by
    intro h1
    rw [← hzq, ← map_pow, hzzneg, map_neg, map_one] at h1
    apply h2notQ
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
    have h7 : (2 : 𝓞 L ⧸ Q) = 1 - (-1) := by ring
    rw [h7, h1, sub_self]
  have horder : orderOf zq = 2 ^ (e + 2) := orderOf_eq_prime_pow hnot hfin
  have hpz : IsPrimitiveRoot zq (2 ^ (e + 2)) := horder ▸ IsPrimitiveRoot.orderOf zq
  have hCD : zq * zq ^ (2 ^ (e + 2) - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hN1, hfin]
  have hAB : zq ^ n * zq ^ ((2 ^ (e + 2) - 1) * n) = 1 := by
    rw [pow_mul, ← mul_pow, hCD, one_pow]
  have hkey : (zq ^ n * zq - 1) * (zq ^ n * zq ^ (2 ^ (e + 2) - 1) - 1) = 0 := by
    linear_combination (zq ^ n) * hrel - hAB + (zq ^ n) ^ 2 * hCD
  rcases mul_eq_zero.mp hkey with h1 | h1
  · have h1' : zq ^ (n + 1) = 1 := by
      rw [pow_succ]
      exact sub_eq_zero.mp h1
    have hd := (hpz.pow_eq_one_iff_dvd _).mp h1'
    have hc : ((n + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).mpr hd
    have hu' : (u : ZMod (2 ^ (e + 2))) = -1 := by
      rw [← hnu]
      push_cast at hc
      linear_combination hc
    have hu1 : u = -1 := Units.ext (by rw [hu', Units.val_neg, Units.val_one])
    rw [hu1]
    exact hcl_neg_one' e
  · have h1' : zq ^ (n + (2 ^ (e + 2) - 1)) = 1 := by
      rw [pow_add]
      exact sub_eq_zero.mp h1
    have hd := (hpz.pow_eq_one_iff_dvd _).mp h1'
    have hc : ((n + (2 ^ (e + 2) - 1) : ℕ) : ZMod (2 ^ (e + 2))) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod (2 ^ (e + 2))) (2 ^ (e + 2)) _).mpr hd
    have hu' : (u : ZMod (2 ^ (e + 2))) = 1 := by
      rw [Nat.cast_add, Nat.cast_sub hN1, ZMod.natCast_self, Nat.cast_one, hnu] at hc
      linear_combination hc
    have hu1 : u = 1 := Units.ext (by rw [hu', Units.val_one])
    rw [hu1]
    exact hcl_at_one e
end Formalism.FrobeniusOrbits.Decomp
