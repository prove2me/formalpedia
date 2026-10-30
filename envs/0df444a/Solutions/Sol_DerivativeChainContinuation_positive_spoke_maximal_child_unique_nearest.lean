-- Prove2me | solution 1 for DerivativeChainContinuation.positive_spoke_maximal_child_unique_nearest
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:46:15.718982+00:00
-- url     : https://prove2.me/submissions/b9505e0a-4a5c-4ed9-bd41-0f1143bebb65

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_quotient_outer_root
import Theorems.Thm_DerivativeChainContinuation_positive_quotient_radial_gap
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_derivative_closed
import Theorems.Thm_DerivativeChainContinuation_ray_unique_nearest_comparison
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial



theorem spoke_derivative_succ (k r : ℕ) (q : Polynomial ℝ) :
    (spokePoly (k + 1) (r + 1) q).derivative =
      spokePoly (k + 1) r
        (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [spokePoly, derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, derivative_comp, derivative_map, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.add_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
  rw [pow_succ (X : Polynomial ℂ) r, pow_succ (X : Polynomial ℂ) k]
  simp only [map_add, map_natCast, map_one]
  push_cast
  ring

theorem spoke_derivative_zero (k : ℕ) (q : Polynomial ℝ) :
    (spokePoly (k + 1) 0 q).derivative =
      spokePoly (k + 1) k (C (k + 1 : ℝ) * q.derivative) := by
  simp only [spokePoly, pow_zero, one_mul, derivative_comp, derivative_pow,
    derivative_X, mul_one, Nat.add_sub_cancel, derivative_map,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.mul_comp, Polynomial.C_comp]
  simp only [map_add, map_natCast, map_one]
  push_cast
  ring





theorem spoke_eval_real_power (k r : ℕ) (q : Polynomial ℝ) (w : ℂ) (y : ℝ)
    (hw : w ^ k = (y : ℂ)) :
    (spokePoly k r q).eval w = w ^ r * ((q.eval y : ℝ) : ℂ) := by
  simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp, hw]
  exact congrArg (fun z : ℂ => w ^ r * z)
    (Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := q) y)



theorem spoke_root_power_real (k r : ℕ) (q : Polynomial ℝ) (hq : q.Splits)
    (hqne : q ≠ 0) (w : ℂ) (hw : w ≠ 0) (hz : (spokePoly k r q).eval w = 0) :
    ∃ y : ℝ, w ^ k = (y : ℂ) := by
  have heval : (q.map Complex.ofRealHom).eval (w ^ k) = 0 := by
    simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hw)
  obtain ⟨y, hy⟩ := hq.mem_range_of_isRoot hqne heval
  exact ⟨y, hy.symm⟩

end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

















theorem positive_spoke_nonzero_root_power (k r : ℕ) (Q : Polynomial ℝ)
    (hQ : PositiveQuotient Q) (z : ℂ) (hz : z≠0)
    (hroot : (spokePoly k r Q).eval z=0) :
    ∃ t : ℝ,0<t ∧ z^k=(t : ℂ) ∧ Q.eval t=0 := by
  obtain ⟨t,ht⟩ := spoke_root_power_real k r Q hQ.2.1 hQ.1 z hz hroot
  have hv : Q.eval t=0 := by
    rw [spoke_eval_real_power k r Q z t ht] at hroot
    have h := (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hz)
    exact Complex.ofReal_eq_zero.mp h
  exact ⟨t,hQ.2.2 t ((mem_roots hQ.1).mpr hv),ht,hv⟩






end DerivativeChainContinuation



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial







theorem weighted_positive_parent (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (r k : ℕ) (y : ℝ) (hy : 0 < y)
    (hz : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).eval y = 0) :
    ∃ x ∈ q.roots, y ≤ x := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    have hm := (Polynomial.mem_roots hq).mpr heq
    exact (not_lt_of_ge (le_refl y)) (h y hm)
  let s := (q.roots.map fun x => 1 / (y - x)).sum
  have hsnonneg : 0 ≤ s := by
    apply Multiset.sum_nonneg
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    exact le_of_lt (one_div_pos.mpr (sub_pos.mpr (h x hx)))
  have hd : q.derivative.eval y = q.eval y * s := hs.eval_derivative_eq_eval_mul_sum hqy
  simp only [eval_add, eval_mul, eval_C, eval_X] at hz
  rw [hd] at hz
  have heq : q.eval y * ((r + 1 : ℝ) + (k + 1 : ℝ) * y * s) = 0 := by
    nlinarith [hz]
  have hb := (mul_eq_zero.mp heq).resolve_left hqy
  have hprod : 0 ≤ (k + 1 : ℝ) * y * s :=
    mul_nonneg (mul_nonneg (by positivity) hy.le) hsnonneg
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith



theorem derivative_positive_parent (q : Polynomial ℝ) (hq : q ≠ 0) (hs : q.Splits)
    (hdeg : 0 < q.natDegree) (y : ℝ) (hz : q.derivative.eval y = 0) :
    ∃ x ∈ q.roots, y ≤ x := by
  classical
  by_contra h
  push Not at h
  have hqy : q.eval y ≠ 0 := by
    intro heq
    exact (lt_irrefl y) (h y ((Polynomial.mem_roots hq).mpr heq))
  let s := (q.roots.map fun x => 1 / (y - x)).sum
  have hterms : ∀ a ∈ (q.roots.map fun x => 1 / (y - x)), 0 ≤ a := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
    exact (one_div_pos.mpr (sub_pos.mpr (h x hx))).le
  have hnonempty : q.roots ≠ 0 := by
    intro heq
    have hc := hs.natDegree_eq_card_roots
    simp only [heq, Multiset.card_zero] at hc
    omega
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hnonempty
  have hle : 1 / (y - x) ≤ s :=
    Multiset.single_le_sum hterms _ (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have hd := hs.eval_derivative_eq_eval_mul_sum hqy
  rw [hz] at hd
  have hs0 : s = 0 := (mul_eq_zero.mp hd.symm).resolve_left hqy
  have hpos := one_div_pos.mpr (sub_pos.mpr (h x hx))
  linarith



end DerivativeChainPrivate


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem positive_spoke_weighted_eval (k s : ℕ) (Q : Polynomial ℝ) (hk : 1 ≤ k)
    (z : ℂ) (t : ℝ) (hpower : z^k=(t : ℂ)) :
    z*(spokePoly k s Q).derivative.eval z=z^s*(((positiveWeighted s k Q).eval t : ℝ) : ℂ) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
  cases s with
  | zero =>
    rw [spoke_derivative_zero,spoke_eval_real_power _ _ _ z t hpower]
    simp only [positiveWeighted,Nat.cast_zero,C_0,zero_mul,zero_add,pow_zero,one_mul,
      eval_mul,eval_C,eval_X]
    push_cast
    rw [←mul_assoc,←pow_succ',hpower]
    ring
  | succ s =>
    rw [spoke_derivative_succ,spoke_eval_real_power _ _ _ z t hpower]
    simp only [positiveWeighted,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,pow_succ]
    ring

theorem positive_spoke_derivative_weighted_root (k s : ℕ) (Q : Polynomial ℝ)
    (hk : 2 ≤ k) (hQ : PositiveQuotient Q) (hdegree : 2 ≤ (spokePoly k s Q).natDegree)
    (w : ℂ) (hw : w≠0) (hroot : (spokePoly k s Q).derivative.eval w=0) :
    ∃ t : ℝ,0<t ∧ w^k=(t : ℂ) ∧ (positiveWeighted s k Q).eval t=0 := by
  obtain ⟨r,V,hV,heq⟩ := positive_spoke_derivative_closed k s Q hk hQ hdegree
  obtain ⟨t,ht,hpow,hVroot⟩ := positive_spoke_nonzero_root_power k r V hV w hw (by rwa [←heq])
  have he := positive_spoke_weighted_eval k s Q (by omega) w t hpow
  rw [hroot,mul_zero] at he
  have hz := (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hw)
  exact ⟨t,ht,hpow,Complex.ofReal_eq_zero.mp hz⟩

theorem positive_weighted_root_spoke_derivative (k s : ℕ) (Q : Polynomial ℝ)
    (hk : 1 ≤ k) (z : ℂ) (hz : z≠0) (t : ℝ) (hpower : z^k=(t : ℂ))
    (hroot : (positiveWeighted s k Q).eval t=0) : (spokePoly k s Q).derivative.eval z=0 := by
  have he := positive_spoke_weighted_eval k s Q hk z t hpower
  rw [hroot,Complex.ofReal_zero,mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left hz

theorem positive_power_norm (k : ℕ) (w : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hpow : w^k=(t : ℂ)) : ‖w‖^k=t := by
  have h := congrArg norm hpow
  simpa only [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] using h

theorem positive_weighted_child_max (k s : ℕ) (Q : Polynomial ℝ)
    (hk : 2 ≤ k) (w : ℂ)
    (hmax : ∀ z : ℂ,(spokePoly k s Q).derivative.eval z=0 → ‖z‖ ≤ ‖w‖)
    (t : ℝ) (ht : 0<t) (hpow : w^k=(t : ℂ)) :
    ∀ y : ℝ,0<y → (positiveWeighted s k Q).eval y=0 → y ≤ t := by
  intro y hy hyroot
  let x : ℝ := y^((k : ℝ)⁻¹)
  have hx : 0<x := Real.rpow_pos_of_pos hy _
  have hxpow : x^k=y := Real.rpow_inv_natCast_pow hy.le (by omega)
  have hzpow : (x : ℂ)^k=(y : ℂ) := by rw [←Complex.ofReal_pow,hxpow]
  have hroot := positive_weighted_root_spoke_derivative k s Q (by omega)
    (x : ℂ) (by exact_mod_cast (ne_of_gt hx)) y hzpow hyroot
  have hnorm : x ≤ ‖w‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx] using hmax _ hroot
  have hp := pow_le_pow_left₀ hx.le hnorm k
  rw [hxpow,positive_power_norm k w t ht.le hpow] at hp
  exact hp

theorem positive_weighted_root_le_outer (s k : ℕ) (Q : Polynomial ℝ)
    (hk : 1 ≤ k) (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree)
    (b t : ℝ) (hB : ∀ y : ℝ,Q.eval y=0 → y ≤ b) (ht : 0<t)
    (hroot : (positiveWeighted s k Q).eval t=0) : t ≤ b := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
  cases s with
  | zero =>
    have hd : Q.derivative.eval t=0 := by
      simp only [positiveWeighted,Nat.cast_zero,C_0,zero_mul,zero_add,eval_mul,eval_C,eval_X] at hroot
      exact (mul_eq_zero.mp hroot).resolve_left (mul_ne_zero (by positivity) (ne_of_gt ht))
    obtain ⟨y,hy,hty⟩ := derivative_positive_parent Q hQ.1 hQ.2.1 hQdegree t hd
    exact hty.trans (hB y ((mem_roots hQ.1).mp hy))
  | succ s =>
    obtain ⟨y,hy,hty⟩ := weighted_positive_parent Q hQ.1 hQ.2.1 s j t ht (by
      simpa only [positiveWeighted,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using hroot)
    exact hty.trans (hB y ((mem_roots hQ.1).mp hy))






end DerivativeChainContinuation

theorem solution (k s : ℕ) (Q : Polynomial ℝ)
    (hk : 2 ≤ k) (hQ : PositiveQuotient Q) (hQdegree : 0<Q.natDegree)
    (hdegree : 2 ≤ (spokePoly k s Q).natDegree)
    (w : ℂ) (hw : w≠0) (hroot : (spokePoly k s Q).derivative.eval w=0)
    (hmax : ∀ z : ℂ,(spokePoly k s Q).derivative.eval z=0 → ‖z‖ ≤ ‖w‖) :
    ∃ v : ℂ,(spokePoly k s Q).eval v=0 ∧ ‖w‖ ≤ ‖v‖ ∧
      (∃ c : ℝ,1 ≤ c ∧ v=(c : ℂ)*w) ∧
      (∀ u : ℂ,(spokePoly k s Q).eval u=0 → ‖u‖ ≤ ‖v‖) ∧
      ∀ u : ℂ,(spokePoly k s Q).eval u=0 →
        ‖v-w‖ ≤ ‖u-w‖ ∧ (‖u-w‖ ≤ ‖v-w‖ → u=v) := by
  obtain ⟨t,ht,hwpow,htroot⟩ := positive_spoke_derivative_weighted_root k s Q hk hQ hdegree w hw hroot
  have htmax := positive_weighted_child_max k s Q hk w hmax t ht hwpow
  obtain ⟨b,hb,hbroot,hbmax⟩ := positive_quotient_outer_root Q hQ hQdegree
  have htb := positive_weighted_root_le_outer s k Q (by omega) hQ hQdegree b t hbmax ht htroot
  let c : ℝ := (b/t)^((k : ℝ)⁻¹)
  have hratio : 1 ≤ b/t := (le_div_iff₀ ht).mpr (by linarith)
  have hc : 1 ≤ c := Real.one_le_rpow hratio (by positivity)
  have hcpow : c^k=b/t := Real.rpow_inv_natCast_pow (by positivity) (by omega)
  let v : ℂ := (c : ℂ)*w
  have hvpow : v^k=(b : ℂ) := by
    simp only [v,mul_pow,←Complex.ofReal_pow,hcpow,hwpow,←Complex.ofReal_mul]
    rw [div_mul_cancel₀ b (ne_of_gt ht)]
  have hvroot : (spokePoly k s Q).eval v=0 := by
    rw [spoke_eval_real_power k s Q v b hvpow,hbroot]
    simp
  have hwnorm := positive_power_norm k w t ht.le hwpow
  have hvnorm := positive_power_norm k v b hb.le hvpow
  have hnormv : ‖v‖=c*‖w‖ := by
    dsimp only [v]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ c)]
  have hwv : ‖w‖ ≤ ‖v‖ := by rw [hnormv]; nlinarith [norm_nonneg w]
  have hparent (u : ℂ) (hu : (spokePoly k s Q).eval u=0) :
      (‖u‖=0 ∨ Q.eval (‖u‖^k)=0) ∧ ‖u‖ ≤ ‖v‖ := by
    by_cases hu0 : u=0
    · subst u
      exact ⟨Or.inl (norm_zero : ‖(0 : ℂ)‖=0),by simpa only [norm_zero] using norm_nonneg v⟩
    · obtain ⟨y,hy,hupow,hyroot⟩ := positive_spoke_nonzero_root_power k s Q hQ u hu0 hu
      have hunorm := positive_power_norm k u y hy.le hupow
      have hle : ‖u‖^k ≤ ‖v‖^k := by rw [hunorm,hvnorm]; exact hbmax y hyroot
      exact ⟨Or.inr (by rw [hunorm]; exact hyroot),le_of_pow_le_pow_left₀ (by omega) (norm_nonneg v) hle⟩
  refine ⟨v,hvroot,hwv,⟨c,hc,rfl⟩,fun u hu => (hparent u hu).2,?_⟩
  intro u hu
  apply ray_unique_nearest_comparison w u c hc hw (hparent u hu).2
  intro hsmall
  exact positive_quotient_radial_gap s k Q hQ hQdegree hk b t hbroot hbmax ht htroot htmax
    ‖v‖ ‖w‖ ‖u‖ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hvnorm hwnorm (hparent u hu).1 hsmall
