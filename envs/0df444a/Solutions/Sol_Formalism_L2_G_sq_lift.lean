-- Prove2me | solution 1 for Formalism.L2.G.sq_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:01:29.96323+00:00
-- url     : https://prove2.me/submissions/f69218f8-2946-4c67-ac3e-0129e3f59c36

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
noncomputable section
namespace Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
private theorem exists_mul_p_pow_eq_verschiebung_iterate (k : Type) [Field k] [CharP k p] [PerfectRing k p] (m : ℕ)
    (s : WittVector p k) :
    ∃ a : WittVector p k, a * (p : WittVector p k) ^ m = (⇑WittVector.verschiebung)^[m] s := by
  induction m generalizing s with
  | zero => exact ⟨s, by simp⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih s
    obtain ⟨b, hb⟩ : ∃ b, WittVector.frobenius b = a := by
      refine ⟨(WittVector.frobeniusEquiv p k).symm a, ?_⟩
      have := (WittVector.frobeniusEquiv p k).apply_symm_apply a
      rwa [WittVector.frobeniusEquiv_apply] at this
    refine ⟨b, ?_⟩
    rw [Function.iterate_succ_apply', ← ha, ← hb]
    have : WittVector.frobenius b * (p : WittVector p k) ^ m =
        WittVector.frobenius (b * (p : WittVector p k) ^ m) := by
      rw [map_mul, map_pow, map_natCast]
    rw [this, WittVector.verschiebung_frobenius]
    ring
private theorem mem_span_p_pow_iff_coeff_eq_zero (k : Type) [Field k] [CharP k p] [PerfectRing k p] (m : ℕ)
    (x : WittVector p k) :
    x ∈ Ideal.span {(p : WittVector p k)} ^ m ↔ ∀ i < m, x.coeff i = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    induction m with
    | zero => intro i hi; omega
    | succ m ih =>
      intro i hi
      have e : a * (p : WittVector p k) ^ (m + 1) = (a * (p : WittVector p k) ^ m) * p := by ring
      rw [e, ← WittVector.verschiebung_frobenius]
      cases i with
      | zero => exact WittVector.verschiebung_coeff_zero _
      | succ i =>
        rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP,
          ih i (by omega), zero_pow hp.out.ne_zero]
  · intro hx
    obtain ⟨a, ha⟩ := exists_mul_p_pow_eq_verschiebung_iterate p k m (x.shift m)
    exact ⟨a, by rw [ha]; exact (WittVector.eq_iterate_verschiebung hx).symm⟩
private theorem coeff_sub_eq_zero_iff_coeff_eq (k : Type) [CommRing k] (m : ℕ) (x y : WittVector p k) :
    (∀ i < m, (x - y).coeff i = 0) ↔ ∀ i < m, x.coeff i = y.coeff i := by
  have h0 : ∀ z : WittVector p k, (∀ i < m, z.coeff i = 0) ↔ WittVector.truncate m z = 0 := by
    intro z
    constructor
    · intro h
      ext i
      simp [WittVector.coeff_truncate, h i i.2]
    · intro h i hi
      have := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
      simpa [WittVector.coeff_truncate] using this
  rw [h0, map_sub, sub_eq_zero]
  constructor
  · intro h i hi
    have := congrArg (TruncatedWittVector.coeff ⟨i, hi⟩) h
    simpa [WittVector.coeff_truncate] using this
  · intro h
    ext i
    simp [WittVector.coeff_truncate, h i i.2]
private theorem isAdicComplete_span_p_wittVector (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := by
  have hmem : ∀ (m : ℕ) (x : WittVector p k),
      x ∈ (Ideal.span {(p : WittVector p k)} ^ m • ⊤ : Submodule (WittVector p k) (WittVector p k)) ↔
        ∀ i < m, x.coeff i = 0 := by
    intro m x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, mem_span_p_pow_iff_coeff_eq_zero]
  have hmod : ∀ (m : ℕ) (x y : WittVector p k),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p k)} ^ m • ⊤ : Submodule (WittVector p k) (WittVector p k))] ↔
        ∀ i < m, x.coeff i = y.coeff i := by
    intro m x y
    rw [SModEq.sub_mem, hmem, coeff_sub_eq_zero_iff_coeff_eq]
  have H : IsHausdorff (Ideal.span {(p : WittVector p k)}) (WittVector p k) := by
    refine ⟨fun x hx => ?_⟩
    ext i
    have := (hmod (i + 1) x 0).mp (hx (i + 1)) i (by omega)
    simpa using this
  have P : IsPrecomplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := by
    refine ⟨fun f hf => ?_⟩
    refine ⟨WittVector.mk p (fun i => (f (i + 1)).coeff i), fun m => ?_⟩
    rw [hmod]
    intro i hi
    simp only [WittVector.coeff_mk]
    exact ((hmod (i + 1) (f (i + 1)) (f m)).mp (hf (by omega)) i (by omega)).symm
  haveI := H
  haveI := P
  constructor
end Formalism.L2.G
end
end

set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
omit [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution (c : W2 p n) (y0 : F2 p n) (hc : c.coeff 0 = y0 * y0) (hy00 : y0 ≠ 0)
    (h2 : (2 : F2 p n) ≠ 0) : ∃ y : W2 p n, y ^ 2 = c := by
  haveI := isAdicComplete_span_p_wittVector p (F2 p n)
  haveI := IsAdicComplete.henselianRing (W2 p n) (Ideal.span {(p : W2 p n)})
  have hmon : (Polynomial.X ^ 2 - Polynomial.C c).Monic := Polynomial.monic_X_pow_sub_C c (by norm_num)
  set a0 : W2 p n := WittVector.teichmuller p y0 with ha0
  have ha00 : WittVector.constantCoeff a0 = y0 := WittVector.teichmuller_coeff_zero p y0
  have hev : (Polynomial.X ^ 2 - Polynomial.C c).eval a0 ∈ Ideal.span {(p : W2 p n)} := by
    have := (mem_span_p_pow_iff_coeff_eq_zero p (F2 p n) 1 ((Polynomial.X ^ 2 - Polynomial.C c).eval a0)).mpr
      (fun i hi => by
        obtain rfl : i = 0 := by omega
        show WittVector.constantCoeff _ = 0
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
          map_sub, map_pow, ha00]
        rw [show WittVector.constantCoeff c = c.coeff 0 from rfl, hc]
        ring)
    rwa [pow_one] at this
  have hder : IsUnit ((Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C c)).eval a0) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    show WittVector.constantCoeff _ ≠ 0
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
      sub_zero, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_natCast, map_mul, map_pow, map_natCast, ha00]
    norm_num
    exact ⟨h2, hy00⟩
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian _ hmon a0 hev (hder.map _)
  refine ⟨y, ?_⟩
  have := hy.eq_zero
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this
  exact sub_eq_zero.mp this
end Formalism.L2.G
