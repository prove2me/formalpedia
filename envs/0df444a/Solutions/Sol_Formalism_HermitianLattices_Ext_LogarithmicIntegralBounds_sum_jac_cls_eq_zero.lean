-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_jac_cls_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:46.651555+00:00
-- url     : https://prove2.me/submissions/afa0b360-b024-43cd-947a-3c1cc3dee1c7

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
private theorem sum_clsB_mul_mod_eq_sum {M : Type*} [AddCommMonoid M] (m₀ s a₀ u : ℕ) (hN : 0 < m₀ * s)
    (hu1 : u % m₀ = 1 % m₀) (hus : u.Coprime s) (f : ℕ → M) :
    ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s)) = ∑ b ∈ clsB m₀ s a₀, f b := by
  have hcm : ∀ x k : ℕ, Nat.Coprime x k ↔ Nat.Coprime (x % k) k := fun x k => by
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
  have hum : u.Coprime m₀ := by
    rw [hcm, hu1, ← hcm]
    exact Nat.coprime_one_left _
  have huN : u.Coprime (m₀ * s) := Nat.Coprime.mul_right hum hus
  have hmap : ∀ b ∈ clsB m₀ s a₀, (b * u) % (m₀ * s) ∈ clsB m₀ s a₀ := by
    intro b hb
    simp only [clsB, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨Nat.mod_lt _ hN, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m₀ s), Nat.mul_mod, hb.2.1, hu1, ← Nat.mul_mod, mul_one]
    · rw [hcm, Nat.mod_mod_of_dvd _ (dvd_mul_left s m₀), ← hcm]
      exact Nat.Coprime.mul hb.2.2 hus
  have hinj : Set.InjOn (fun b => (b * u) % (m₀ * s)) (clsB m₀ s a₀) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, clsB, Finset.mem_filter, Finset.mem_range] at hx hy
    have h := Nat.ModEq.cancel_right_of_coprime huN.symm (show x * u ≡ y * u [MOD m₀ * s] from hxy)
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h
  have himg : (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)) = clsB m₀ s a₀ :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hmap)
      (by rw [Finset.card_image_of_injOn hinj])
  calc ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s))
      = ∑ x ∈ (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)), f x := (Finset.sum_image hinj).symm
    _ = ∑ b ∈ clsB m₀ s a₀, f b := by rw [himg]
private theorem jacobiSym_mul_mod_eq_mul (m₀ s b u : ℕ) :
    jacobiSym (((b * u) % (m₀ * s) : ℕ) : ℤ) s = jacobiSym (b : ℤ) s * jacobiSym (u : ℤ) s := by
  rw [← jacobiSym.mul_left]
  apply jacobiSym.mod_left'
  push_cast
  exact Int.emod_emod_of_dvd _ (dvd_mul_left _ _)
private theorem exists_jacobiSym_neg_one_in_residue_class (m₀ s : ℕ) (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s)
    (hcop : m₀.Coprime s) :
    ∃ u : ℕ, u % m₀ = 1 % m₀ ∧ u.Coprime s ∧ jacobiSym (u : ℤ) s = -1 := by
  have hp : s.minFac.Prime := Nat.minFac_prime (by omega)
  haveI := Fact.mk hp
  haveI : NeZero s := ⟨by omega⟩
  obtain ⟨t, ht⟩ := Nat.minFac_dvd s
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    omega
  haveI : NeZero t := ⟨ht0⟩
  haveI : NeZero s.minFac := ⟨hp.ne_zero⟩
  have hp2 : s.minFac ≠ 2 := by
    intro h2
    rw [h2] at ht
    rw [ht] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul t)
  have hpt : s.minFac.Coprime t := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨v, hv⟩
    have hu := hsq s.minFac ⟨v, by rw [mul_assoc, ← hv]; exact ht⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp hu)
  have hmp : (m₀ * t).Coprime s.minFac :=
    Nat.Coprime.mul (Nat.Coprime.coprime_dvd_right (Nat.minFac_dvd s) hcop) hpt.symm
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod s.minFac)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  let c := Nat.chineseRemainder hmp 1 g.val
  have hc1 : (c : ℕ) ≡ 1 [MOD m₀ * t] := c.2.1
  have hc2 : (c : ℕ) ≡ g.val [MOD s.minFac] := c.2.2
  have hJ : jacobiSym ((c : ℕ) : ℤ) s = -1 := by
    have e1 : jacobiSym ((c : ℕ) : ℤ) s.minFac = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
      have hcg : (((c : ℕ) : ℤ) : ZMod s.minFac) = g := by
        rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc2, ZMod.natCast_zmod_val]
      rwa [hcg]
    have e2 : jacobiSym ((c : ℕ) : ℤ) t = 1 := by
      have hct : (c : ℕ) ≡ 1 [MOD t] := Nat.ModEq.of_mul_left m₀ hc1
      have h' : (((c : ℕ) % t : ℕ) : ℤ) = ((1 % t : ℕ) : ℤ) := congrArg _ hct
      push_cast at h'
      rw [jacobiSym.mod_left' h', jacobiSym.one_left]
    have hsplit : jacobiSym ((c : ℕ) : ℤ) s = jacobiSym ((c : ℕ) : ℤ) (s.minFac * t) := by rw [← ht]
    rw [hsplit, jacobiSym.mul_right, e1, e2]
    norm_num
  refine ⟨c, Nat.ModEq.of_mul_right t hc1, ?_, hJ⟩
  have hg1 : Int.gcd ((c : ℕ) : ℤ) s = 1 := by
    by_contra hne
    have h0 := jacobiSym.eq_zero_iff_not_coprime.mpr hne
    rw [hJ] at h0
    norm_num at h0
  rwa [Int.gcd_natCast_natCast] at hg1
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) :
    ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) = 0 := by
  have hN : 0 < m₀ * s := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨u, hu1, hus, hJu⟩ := exists_jacobiSym_neg_one_in_residue_class m₀ s h1 hodd hsq hcop
  have hre := sum_clsB_mul_mod_eq_sum m₀ s a₀ u hN hu1 hus (fun x => (jacobiSym (x : ℤ) s : ℝ))
  simp only [jacobiSym_mul_mod_eq_mul, hJu, Int.cast_mul, Int.cast_neg, Int.cast_one, mul_neg, mul_one,
    Finset.sum_neg_distrib] at hre
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
