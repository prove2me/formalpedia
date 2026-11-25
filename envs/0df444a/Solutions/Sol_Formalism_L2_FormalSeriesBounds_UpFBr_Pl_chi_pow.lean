-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:08.742024+00:00
-- url     : https://prove2.me/submissions/4ec47d8a-fc42-4441-a93f-cae1f87a024c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP

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
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) (s : ℤ_[l] ⊗[ℤ] OE) :
    chi (em 0) s ^ (l ^ d) = chi (em 0) s := by
  have hl0 : residue R ((l : ℕ) : R) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hl
  have hlk : ((l : ℕ) : IsLocalRing.ResidueField R) = 0 := by
    have h := map_natCast (residue R) l
    rw [← h]
    exact hl0
  haveI : CharP (IsLocalRing.ResidueField R) l := by
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hlk
  have hstep : ∀ (a : ZMod d) (x : OE), residue R (em (a + 1) x) = residue R (em a x) ^ l := by
    intro a x
    rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hfrob a x
  have hiter : ∀ (n : ℕ) (x : OE), residue R (em (n : ZMod d) x) = residue R (em 0 x) ^ (l ^ n) := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hstep, ih, ← pow_mul, pow_succ]
  have htx : ∀ x : OE, tauX (l := l) (em 0) (1 ⊗ₜ x) = em 0 x := by
    intro x
    simp [tauX, Algebra.TensorProduct.lift_tmul]
  have hx : ∀ x : OE, chi (l := l) (em 0) (1 ⊗ₜ x) ^ (l ^ d) = chi (l := l) (em 0) (1 ⊗ₜ x) := by
    intro x
    change residue R (tauX (l := l) (em 0) (1 ⊗ₜ x)) ^ (l ^ d) = residue R (tauX (l := l) (em 0) (1 ⊗ₜ x))
    rw [htx, ← hiter d x, ZMod.natCast_self]
  have hnat : ∀ a : ℕ, ((a : IsLocalRing.ResidueField R)) ^ (l ^ d) = (a : IsLocalRing.ResidueField R) := by
    intro a
    have h0 : ((a : ZMod l)) ^ (l ^ d) = (a : ZMod l) := ZMod.pow_card_pow _
    have h := congrArg (ZMod.castHom (dvd_refl l) (IsLocalRing.ResidueField R)) h0
    rwa [map_pow, map_natCast] at h
  have hc : ∀ c : ℤ_[l], chi (l := l) (em 0) (c ⊗ₜ (1 : OE)) ^ (l ^ d) = chi (l := l) (em 0) (c ⊗ₜ (1 : OE)) := by
    intro c
    have htc : tauX (l := l) (em 0) (c ⊗ₜ (1 : OE)) = algebraMap ℤ_[l] R c := by
      simp [tauX, Algebra.TensorProduct.lift_tmul]
    change residue R (tauX (l := l) (em 0) (c ⊗ₜ (1 : OE))) ^ (l ^ d) =
      residue R (tauX (l := l) (em 0) (c ⊗ₜ (1 : OE)))
    rw [htc]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 c)
    obtain ⟨a, ha⟩ : ∃ a, a = c.appr 1 := ⟨_, rfl⟩
    rw [← ha, pow_one] at hy
    have hc' : c = ((a : ℕ) : ℤ_[l]) + y * ((l : ℕ) : ℤ_[l]) := by
      rw [hy]
      ring
    have hr : residue R (algebraMap ℤ_[l] R c) = (a : IsLocalRing.ResidueField R) := by
      rw [hc', map_add, map_mul, map_natCast, map_natCast, map_add, map_mul, hl0, mul_zero, add_zero,
        map_natCast]
    rw [hr, hnat]
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  | tmul c x =>
    have hsplit : c ⊗ₜ[ℤ] x = (c ⊗ₜ[ℤ] (1 : OE)) * ((1 : ℤ_[l]) ⊗ₜ[ℤ] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hsplit, map_mul, mul_pow, hc c, hx x]
  | add s t hs ht => rw [map_add, add_pow_char_pow, hs, ht]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
