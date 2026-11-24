-- Prove2me | solution 1 for Formalism.L2.G.jW_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:20.684506+00:00
-- url     : https://prove2.me/submissions/a3c1485e-38a4-47cb-9131-20bc61d08856

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Theorems.Thm_Formalism_L2_G_precomplete_pi
import Theorems.Thm_Formalism_L2_G_jW_coeff
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
private theorem mem_span_pow_smul_top_pi_iff {R : Type*} [CommRing R] (π : R) (d m : ℕ) (v : Fin d → R) :
    v ∈ (Ideal.span {π} ^ m • ⊤ : Submodule R (Fin d → R)) ↔ ∀ i, v i ∈ Ideal.span {π} ^ m := by
  constructor
  · intro hv
    refine Submodule.smul_induction_on (p := fun v : Fin d → R => ∀ i, v i ∈ Ideal.span {π} ^ m)
      hv ?_ ?_
    · intro r hr w _ i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
    · intro x y hx hy i
      simp only [Pi.add_apply]
      exact Ideal.add_mem _ (hx i) (hy i)
  · intro hv
    have hsum : v = ∑ i, v i • Pi.single i (1 : R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hv i) Submodule.mem_top
end Formalism.L2.G
end
end

set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution : (jW p n).Finite := by
  classical
  haveI hc1 := isAdicComplete_span_p_wittVector p (F1 p n)
  haveI hc2 := isAdicComplete_span_p_wittVector p (F2 p n)
  haveI : IsPrecomplete (Ideal.span {(p : WQ p n)}) (Fin 2 → WQ p n) := precomplete_pi _ 2
  have hfr : Module.finrank (F1 p n) (F2 p n) = 2 := FiniteField.finrank_extension _ _ _
  let b : Module.Basis (Fin 2) (F1 p n) (F2 p n) := Module.finBasisOfFinrankEq _ _ hfr
  let e : Fin 2 → W2 p n := fun j => WittVector.teichmuller p (b j)
  have hjW : ∀ (m : ℕ) (a : WQ p n), jW p n ((p : WQ p n) ^ m * a) = (p : W2 p n) ^ m * jW p n a := by
    intro m a
    rw [map_mul, map_pow, map_natCast]
  have step : ∀ w : W2 p n, ∃ a : Fin 2 → WQ p n, ∃ w' : W2 p n,
      w = ∑ j, jW p n (a j) * e j + (p : W2 p n) * w' := by
    intro w
    set c := b.repr (w.coeff 0) with hc
    refine ⟨fun j => WittVector.teichmuller p (c j), ?_⟩
    have h0 : (w - ∑ j, jW p n (WittVector.teichmuller p (c j)) * e j).coeff 0 = 0 := by
      show WittVector.constantCoeff (w - ∑ j, jW p n (WittVector.teichmuller p (c j)) * e j) = 0
      rw [map_sub, map_sum]
      have h1 : ∀ j, WittVector.constantCoeff (jW p n (WittVector.teichmuller p (c j)) * e j) =
          c j • b j := by
        intro j
        rw [map_mul, Algebra.smul_def]
        congr 1 <;> first
          | exact WittVector.teichmuller_coeff_zero p (b j)
          | (show (jW p n _).coeff 0 = _; rw [jW_coeff, WittVector.teichmuller_coeff_zero])
      simp only [h1]
      rw [sub_eq_zero, hc, b.sum_repr]
      rfl
    have hm : w - ∑ j, jW p n (WittVector.teichmuller p (c j)) * e j ∈
        Ideal.span {(p : W2 p n)} := by
      have := (mem_span_p_pow_iff_coeff_eq_zero p (F2 p n) 1 _).mpr (fun i hi => by
        obtain rfl : i = 0 := by omega
        exact h0)
      rwa [pow_one] at this
    obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨w', by rw [mul_comm, hw']; ring⟩
  choose A Rm hAR using step
  have expand : ∀ (w : W2 p n) (N : ℕ), w = ∑ j, jW p n (∑ m ∈ Finset.range N,
      (p : WQ p n) ^ m * A (Rm^[m] w) j) * e j + (p : W2 p n) ^ N * Rm^[N] w := by
    intro w N
    induction N with
    | zero => simp
    | succ N ih =>
      have h := hAR (Rm^[N] w)
      rw [Function.iterate_succ_apply']
      conv_lhs => rw [ih]
      conv_lhs => rw [h]
      simp only [Finset.sum_range_succ, map_add, add_mul, Finset.sum_add_distrib, hjW, mul_add,
        Finset.mul_sum]
      ring
  unfold RingHom.Finite
  letI : Algebra (WQ p n) (W2 p n) := (jW p n).toAlgebra
  refine ⟨⟨Finset.univ.image e, ?_⟩⟩
  rw [Submodule.eq_top_iff']
  intro w
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → Fin 2 → WQ p n, ∀ N j,
      s N j = ∑ m ∈ Finset.range N, (p : WQ p n) ^ m * A (Rm^[m] w) j := ⟨_, fun _ _ => rfl⟩
  have hs : ∀ {a b : ℕ}, a ≤ b → s a ≡ s b [SMOD (Ideal.span {(p : WQ p n)} ^ a • ⊤ :
      Submodule (WQ p n) (Fin 2 → WQ p n))] := by
    intro a b hab
    rw [SModEq.sub_mem, mem_span_pow_smul_top_pi_iff]
    intro j
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    have h1 : s a j - s (a + d) j = -((p : WQ p n) ^ a *
        ∑ l ∈ Finset.range d, (p : WQ p n) ^ l * A (Rm^[a + l] w) j) := by
      simp only [Pi.sub_apply, hsdef, Finset.sum_range_add, Finset.mul_sum, pow_add]
      ring
    rw [Pi.sub_apply, h1, Ideal.span_singleton_pow]
    exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hs
  have hw : w = ∑ j, jW p n (L j) * e j := by
    rw [← sub_eq_zero]
    refine IsHausdorff.haus hc2.toIsHausdorff _ (fun N => ?_)
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton']
    have h1 := hL N
    rw [SModEq.sub_mem, mem_span_pow_smul_top_pi_iff] at h1
    have h2 : ∀ j, ∃ t, t * (p : WQ p n) ^ N = s N j - L j := fun j => by
      have := h1 j
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at this
      exact this
    choose tt htt using h2
    have h3 : ∀ j, jW p n (L j) = jW p n (s N j) - (p : W2 p n) ^ N * jW p n (tt j) := by
      intro j
      have : L j = s N j - (p : WQ p n) ^ N * tt j := by rw [mul_comm, htt j]; ring
      rw [this, map_sub, hjW]
    have hx : w = ∑ j, jW p n (s N j) * e j + (p : W2 p n) ^ N * Rm^[N] w := by
      simp only [hsdef]
      exact expand w N
    have key : w - ∑ j, jW p n (L j) * e j =
        (∑ j, jW p n (tt j) * e j + Rm^[N] w) * (p : W2 p n) ^ N := by
      conv_lhs => rw [hx]
      simp only [h3, sub_mul, Finset.sum_sub_distrib, add_mul, Finset.sum_mul]
      ring_nf
    exact ⟨_, key.symm⟩
  rw [hw]
  refine Submodule.sum_mem _ fun j _ => ?_
  have h4 : jW p n (L j) * e j = L j • e j := rfl
  rw [h4]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
end Formalism.L2.G
