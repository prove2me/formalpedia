-- Prove2me | solution 1 for CerednikDrinfeld.image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/bf8e5bd6-a896-56de-8af2-b899c6ed9090

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_WeierstrassCurve_RatPointHom
import Theorems.Thm_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_eq_setOf_padicValRat_nrd
import Theorems.Thm_WeierstrassCurve_exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
import Theorems.Thm_WeierstrassCurve_forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero
import Theorems.Thm_WeierstrassCurve_comp_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_add_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_surjective_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_mem_rationalEndSubring_iff_mem_rationalHomSet
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_WeierstrassCurve_exists_xCoord_rep_of_mem_rationalHomSet
import Theorems.Thm_WeierstrassCurve_natDegree_lt_of_xCoord_rep
import Theorems.Thm_Polynomial_isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero
import Theorems.Thm_WeierstrassCurve_exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace FrobKernelIdealShift
namespace Poly

variable {k : Type*} [Field k]

theorem wronskian_C_mul (a : k) (u v : k[X]) :
    wronskian (C a * u) (C a * v) = C a ^ 2 * wronskian u v := by
  simp only [wronskian, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

theorem wronskian_map {S : Type*} [Field S] (f : k →+* S) (u v : k[X]) :
    wronskian (u.map f) (v.map f) = (wronskian u v).map f := by
  simp only [wronskian, derivative_map, Polynomial.map_mul, Polynomial.map_sub]

theorem derivative_expand_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] {j : ℕ} (hj : j ≠ 0)
    (f : k[X]) : derivative (expand k (p ^ j) f) = 0 := by
  rw [derivative_expand]
  have : ((p ^ j : ℕ) : k[X]) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero k[X] p, zero_pow hj]
  rw [this, zero_mul, mul_zero]

theorem wronskian_expand_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] {j : ℕ} (hj : j ≠ 0)
    (f g : k[X]) : wronskian (expand k (p ^ j) f) (expand k (p ^ j) g) = 0 := by
  simp only [wronskian, derivative_expand_pow_eq_zero p hj, mul_zero, zero_mul, sub_self]

theorem ne_C_mul_of_isCoprime_of_pos {u v : k[X]} (huv : IsCoprime u v)
    (h : 0 < max u.natDegree v.natDegree) (c : k) : u ≠ C c * v := by
  intro huc
  have hvu : v ∣ u := ⟨C c, by rw [huc, mul_comm]⟩
  have hunit : IsUnit v := huv.isUnit_of_dvd' hvu (dvd_refl v)
  have hv0 : v.natDegree = 0 := natDegree_eq_zero_of_isUnit hunit
  have hu0 : u.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    rw [huc]; exact (natDegree_C_mul_le _ _).trans_eq hv0
  omega

theorem eval_ne_zero_of_isCoprime {u v : k[X]} (huv : IsCoprime u v) {x : k} (hv : v.eval x = 0) :
    u.eval x ≠ 0 := by
  intro hu
  obtain ⟨a, b, hab⟩ := huv
  have := congr_arg (eval x) hab
  simp [hu, hv] at this

theorem exists_C_mul_of_mul_eq_mul {u₁ v₁ u₂ v₂ : k[X]} (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (heq : u₁ * v₂ = u₂ * v₁) :
    ∃ c : k, c ≠ 0 ∧ u₂ = C c * u₁ ∧ v₂ = C c * v₁ := by
  have d12 : u₁ ∣ u₂ := h₁.dvd_of_dvd_mul_right ⟨v₂, by rw [heq]⟩
  have d21 : u₂ ∣ u₁ := h₂.dvd_of_dvd_mul_right ⟨v₁, by rw [← heq]⟩
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd d12 d21
  obtain ⟨c, hc, hcw⟩ := Polynomial.isUnit_iff.mp w.isUnit
  refine ⟨c, hc.ne_zero, by rw [← hw, ← hcw, mul_comm], ?_⟩
  have : u₁ * v₂ = u₁ * (C c * v₁) := by
    rw [heq, ← hw, ← hcw]; ring
  exact mul_left_cancel₀ hu₁ this

section CharP

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem exists_expand_wronskian_ne_zero {u v : k[X]} (huv : IsCoprime u v)
    (h : 0 < max u.natDegree v.natDegree) :
    ∃ (e : ℕ) (u₀ v₀ : k[X]), u = expand k (p ^ e) u₀ ∧ v = expand k (p ^ e) v₀ ∧
      IsCoprime u₀ v₀ ∧ 0 < max u₀.natDegree v₀.natDegree ∧ wronskian u₀ v₀ ≠ 0 := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  suffices H : ∀ n : ℕ, ∀ u v : k[X], max u.natDegree v.natDegree = n → IsCoprime u v →
      0 < max u.natDegree v.natDegree →
      ∃ (e : ℕ) (u₀ v₀ : k[X]), u = expand k (p ^ e) u₀ ∧ v = expand k (p ^ e) v₀ ∧
        IsCoprime u₀ v₀ ∧ 0 < max u₀.natDegree v₀.natDegree ∧ wronskian u₀ v₀ ≠ 0 from
    H _ u v rfl huv h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v hn huv hpos
    by_cases hw : wronskian u v ≠ 0
    · exact ⟨0, u, v, by simp, by simp, huv, hpos, hw⟩
    push Not at hw
    obtain ⟨hdu, hdv⟩ := huv.wronskian_eq_zero_iff.mp hw
    set u₁ := contract p u
    set v₁ := contract p v
    have hu : u = expand k p u₁ := (expand_contract p hdu hp).symm
    have hv : v = expand k p v₁ := (expand_contract p hdv hp).symm
    have hcop : IsCoprime u₁ v₁ := by
      rw [hu, hv, isCoprime_expand hp] at huv; exact huv
    have hdeg_u : u.natDegree = u₁.natDegree * p := by rw [hu, natDegree_expand]
    have hdeg_v : v.natDegree = v₁.natDegree * p := by rw [hv, natDegree_expand]
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hmax : max u.natDegree v.natDegree = max u₁.natDegree v₁.natDegree * p := by
      rw [hdeg_u, hdeg_v, Nat.mul_max_mul_right]
    have hpos₁ : 0 < max u₁.natDegree v₁.natDegree := by
      rcases Nat.eq_zero_or_pos (max u₁.natDegree v₁.natDegree) with h0 | h0
      · rw [hmax, h0, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    have hlt : max u₁.natDegree v₁.natDegree < n := by
      rw [← hn, hmax]
      exact lt_mul_of_one_lt_right hpos₁ hp1
    obtain ⟨e, u₀, v₀, hu₀, hv₀, hc₀, hpos₀, hw₀⟩ := ih _ hlt u₁ v₁ rfl hcop hpos₁
    refine ⟨e + 1, u₀, v₀, ?_, ?_, hc₀, hpos₀, hw₀⟩
    · rw [hu, hu₀, expand_expand, pow_succ']
    · rw [hv, hv₀, expand_expand, pow_succ']

theorem expand_exponent_le {u₁ v₁ u₂ v₂ c₁ c₁' c₂ c₂' : k[X]} {a b : ℕ}
    (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂) (heq : u₁ * v₂ = u₂ * v₁)
    (ha : u₁ = expand k (p ^ a) c₁) (ha' : v₁ = expand k (p ^ a) c₁')
    (hb : u₂ = expand k (p ^ b) c₂) (hb' : v₂ = expand k (p ^ b) c₂')
    (hw₁ : wronskian c₁ c₁' ≠ 0) (hw₂ : wronskian c₂ c₂' ≠ 0) : b ≤ a := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_contra hlt
  push Not at hlt
  have hu₁ : u₁ ≠ 0 := by
    intro h0; apply hw₁
    have : c₁ = 0 := expand_injective (pow_pos hp a) (by rw [← ha, h0, map_zero])
    rw [this, wronskian_zero_left]
  have hu₂ : u₂ ≠ 0 := by
    intro h0; apply hw₂
    have : c₂ = 0 := expand_injective (pow_pos hp b) (by rw [← hb, h0, map_zero])
    rw [this, wronskian_zero_left]
  obtain ⟨c, hc, hcu, hcv⟩ := exists_C_mul_of_mul_eq_mul h₁ h₂ hu₁ hu₂ heq

  obtain ⟨j, hj⟩ : ∃ j, b = a + j := ⟨b - a, by omega⟩
  have hj0 : j ≠ 0 := by omega
  have e1 : C c * c₁ = expand k (p ^ j) c₂ := by
    apply expand_injective (pow_pos hp a)
    rw [map_mul, expand_C, ← ha, ← hcu, hb, hj, pow_add, mul_comm (p ^ a), ← expand_expand,
      expand_expand, expand_expand, mul_comm]
  have e2 : C c * c₁' = expand k (p ^ j) c₂' := by
    apply expand_injective (pow_pos hp a)
    rw [map_mul, expand_C, ← ha', ← hcv, hb', hj, pow_add, mul_comm (p ^ a), ← expand_expand,
      expand_expand, expand_expand, mul_comm]
  have hz : wronskian (C c * c₁) (C c * c₁') = 0 := by
    rw [e1, e2, wronskian_expand_pow_eq_zero p hj0]
  rw [wronskian_C_mul] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact hc (by simpa using h)
  · exact hw₁ h

theorem expand_exponent_unique {u₁ v₁ u₂ v₂ c₁ c₁' c₂ c₂' : k[X]} {a b : ℕ}
    (h₁ : IsCoprime u₁ v₁) (h₂ : IsCoprime u₂ v₂) (heq : u₁ * v₂ = u₂ * v₁)
    (ha : u₁ = expand k (p ^ a) c₁) (ha' : v₁ = expand k (p ^ a) c₁')
    (hb : u₂ = expand k (p ^ b) c₂) (hb' : v₂ = expand k (p ^ b) c₂')
    (hw₁ : wronskian c₁ c₁' ≠ 0) (hw₂ : wronskian c₂ c₂' ≠ 0) : a = b :=
  le_antisymm
    (expand_exponent_le p h₂ h₁ (by rw [mul_comm, heq, mul_comm]) hb hb' ha ha' hw₂ hw₁)
    (expand_exponent_le p h₁ h₂ heq ha ha' hb hb' hw₁ hw₂)

end CharP

noncomputable def hom (m : ℕ) (u v s : k[X]) : k[X] :=
  ∑ i ∈ Finset.range (m + 1), C (s.coeff i) * u ^ i * v ^ (m - i)

theorem eval_hom {m : ℕ} {u v s : k[X]} (hs : s.natDegree ≤ m) {x x' : k}
    (hx : x' * v.eval x = u.eval x) :
    (hom m u v s).eval x = (v.eval x) ^ m * s.eval x' := by
  simp only [hom, eval_finsetSum, eval_mul, eval_pow, eval_C]
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hs), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← hx, mul_pow, show (v.eval x) ^ m = (v.eval x) ^ i * (v.eval x) ^ (m - i) by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hi)]]
  ring

theorem eval_hom_div {m : ℕ} {u v s : k[X]} (hs : s.natDegree ≤ m) {x : k} (hv : v.eval x ≠ 0) :
    (hom m u v s).eval x = (v.eval x) ^ m * s.eval (u.eval x / v.eval x) :=
  eval_hom hs (div_mul_cancel₀ _ hv)

theorem comp_core [IsAlgClosed k] {u v s t : k[X]} (huv : IsCoprime u v)
    (hu : 0 < max u.natDegree v.natDegree) (hw : wronskian u v ≠ 0) (hst : IsCoprime s t)
    (hs : 0 < max s.natDegree t.natDegree) (hw' : wronskian s t ≠ 0) :
    IsCoprime (hom (max s.natDegree t.natDegree) u v s) (hom (max s.natDegree t.natDegree) u v t) ∧
      0 < max (hom (max s.natDegree t.natDegree) u v s).natDegree
        (hom (max s.natDegree t.natDegree) u v t).natDegree ∧
      wronskian (hom (max s.natDegree t.natDegree) u v s)
        (hom (max s.natDegree t.natDegree) u v t) ≠ 0 :=
  Polynomial.isCoprime_and_wronskian_ne_zero_comp_of_wronskian_ne_zero huv hu hw hst hs hw'
    (fun x hx => eval_hom_div (le_max_left _ _) hx) (fun x hx => eval_hom_div (le_max_right _ _) hx)

section Twist

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem eval_pow_eq_eval_map_iterateFrobenius (u : k[X]) (y : k) (j : ℕ) :
    (u.eval y) ^ (p ^ j) = (u.map (iterateFrobenius k p j)).eval (y ^ (p ^ j)) := by
  rw [eval_map, ← iterateFrobenius_def, ← iterateFrobenius_def p j y, eval₂_at_apply]

theorem natDegree_map' (u : k[X]) (f : k →+* k) : (u.map f).natDegree = u.natDegree :=
  natDegree_map_eq_of_injective f.injective u

theorem wronskian_map_ne_zero_iff {u v : k[X]} (f : k →+* k) :
    wronskian (u.map f) (v.map f) ≠ 0 ↔ wronskian u v ≠ 0 := by
  rw [wronskian_map, Ne, Polynomial.map_eq_zero_iff f.injective]

end Twist

section Comp

variable (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k]

theorem exists_comp_expand {u v s t a₁ a₂ b₁ b₂ : k[X]} {a b : ℕ}
    (hu : u = expand k (p ^ b) b₁) (hv : v = expand k (p ^ b) b₂)
    (hs : s = expand k (p ^ a) a₁) (ht : t = expand k (p ^ a) a₂)
    (hbc : IsCoprime b₁ b₂) (hbpos : 0 < max b₁.natDegree b₂.natDegree) (hbw : wronskian b₁ b₂ ≠ 0)
    (hac : IsCoprime a₁ a₂) (hapos : 0 < max a₁.natDegree a₂.natDegree) (haw : wronskian a₁ a₂ ≠ 0) :
    ∃ U₀ V₀ : k[X], IsCoprime U₀ V₀ ∧ 0 < max U₀.natDegree V₀.natDegree ∧ wronskian U₀ V₀ ≠ 0 ∧
      ∀ x : k, v.eval x ≠ 0 → t.eval (u.eval x / v.eval x) ≠ 0 →
        (expand k (p ^ (a + b)) V₀).eval x ≠ 0 ∧
        (expand k (p ^ (a + b)) U₀).eval x / (expand k (p ^ (a + b)) V₀).eval x =
          s.eval (u.eval x / v.eval x) / t.eval (u.eval x / v.eval x) := by
  set σ := iterateFrobenius k p a
  set b₁' := b₁.map σ
  set b₂' := b₂.map σ
  have hbc' : IsCoprime b₁' b₂' := (isCoprime_map σ).mpr hbc
  have hbpos' : 0 < max b₁'.natDegree b₂'.natDegree := by
    rwa [natDegree_map' b₁ σ, natDegree_map' b₂ σ]
  have hbw' : wronskian b₁' b₂' ≠ 0 := (wronskian_map_ne_zero_iff σ).mpr hbw
  set m := max a₁.natDegree a₂.natDegree
  obtain ⟨hc, hpos, hw⟩ := comp_core hbc' hbpos' hbw' hac hapos haw
  refine ⟨hom m b₁' b₂' a₁, hom m b₁' b₂' a₂, hc, hpos, hw, fun x hvx htx => ?_⟩
  set z := x ^ (p ^ (a + b)) with hz
  set w := u.eval x / v.eval x with hw_def
  have hz' : z = (x ^ (p ^ b)) ^ (p ^ a) := by rw [hz, ← pow_mul, ← pow_add, add_comm]
  have e₁ : b₁'.eval z = (u.eval x) ^ (p ^ a) := by
    rw [hz', hu, expand_eval, eval_pow_eq_eval_map_iterateFrobenius p]
  have e₂ : b₂'.eval z = (v.eval x) ^ (p ^ a) := by
    rw [hz', hv, expand_eval, eval_pow_eq_eval_map_iterateFrobenius p]
  have hb₂z : b₂'.eval z ≠ 0 := by rw [e₂]; exact pow_ne_zero _ hvx
  have hwz : w ^ (p ^ a) * b₂'.eval z = b₁'.eval z := by
    rw [e₁, e₂, hw_def, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hvx)]
  have hs' : s.eval w = a₁.eval (w ^ (p ^ a)) := by rw [hs, expand_eval]
  have ht' : t.eval w = a₂.eval (w ^ (p ^ a)) := by rw [ht, expand_eval]
  have hU : (expand k (p ^ (a + b)) (hom m b₁' b₂' a₁)).eval x = (b₂'.eval z) ^ m * s.eval w := by
    rw [expand_eval, ← hz, eval_hom (le_max_left _ _) hwz, hs']
  have hV : (expand k (p ^ (a + b)) (hom m b₁' b₂' a₂)).eval x = (b₂'.eval z) ^ m * t.eval w := by
    rw [expand_eval, ← hz, eval_hom (le_max_right _ _) hwz, ht']
  have hVne : (b₂'.eval z) ^ m * t.eval w ≠ 0 := mul_ne_zero (pow_ne_zero _ hb₂z) htx
  refine ⟨by rwa [hV], ?_⟩
  rw [hU, hV, mul_div_mul_left _ _ (pow_ne_zero _ hb₂z)]

end Comp

theorem eq_of_eval_eq_off_finite [Infinite k] {f g : k[X]} {S : Set k} (hS : S.Finite)
    (h : ∀ x, x ∉ S → f.eval x = g.eval x) : f = g := by
  apply eq_of_infinite_eval_eq
  apply Set.Infinite.mono (s := Sᶜ)
  · intro x hx; exact h x hx
  · exact hS.infinite_compl

theorem finite_fibre {u v : k[X]} (huv : IsCoprime u v) (h : 0 < max u.natDegree v.natDegree)
    (c : k) : {x : k | u.eval x = c * v.eval x}.Finite := by
  have hne : u - C c * v ≠ 0 := sub_ne_zero.mpr (ne_C_mul_of_isCoprime_of_pos huv h c)
  refine (finite_setOf_isRoot hne).subset ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  simp [IsRoot, hx]

end FrobKernelIdealShift.Poly

namespace FrobKernelIdealShift

open WeierstrassCurve WeierstrassCurve.Affine Polynomial FrobKernelIdealShift.Poly

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k]

omit [DecidableEq k] in
theorem exists_nonsingular (W : WeierstrassCurve k) [W.IsElliptic] (x : k) :
    ∃ y, W.toAffine.Nonsingular x y := by
  set q : k[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    with hq
  have hdeg : q.degree = 2 := by
    rw [hq]; compute_degree!
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q (by rw [hdeg]; decide)
  refine ⟨y, (Affine.equation_iff_nonsingular).mp ?_⟩
  rw [Affine.equation_iff]
  simp only [hq, IsRoot.def, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hy
  linear_combination hy

section XPair

variable {W₁ W₂ W₃ : WeierstrassCurve k}

def IsXPair (f : W₁.toAffine.Point → W₂.toAffine.Point) (u v : k[X]) (B : Set k) : Prop :=
  IsCoprime u v ∧ 0 < max u.natDegree v.natDegree ∧ B.Finite ∧
    ∀ (x y : k) (h : W₁.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : W₂.toAffine.Nonsingular x' y'),
        f (.some x y h) = .some x' y' h' ∧ x' * v.eval x = u.eval x

variable [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

theorem IsXPair.eval_ne_zero {f : W₁.toAffine.Point → W₂.toAffine.Point} {u v : k[X]} {B : Set k}
    (hf : IsXPair f u v B) {x : k} (hx : x ∉ B) : v.eval x ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
  obtain ⟨x', y', h', -, hx'⟩ := hf.2.2.2 x y hy hx
  intro hv
  rw [hv, mul_zero] at hx'
  exact eval_ne_zero_of_isCoprime hf.1 hv hx'.symm

theorem IsXPair.mul_eq_mul {f : W₁.toAffine.Point → W₂.toAffine.Point} {u₁ v₁ u₂ v₂ : k[X]}
    {B₁ B₂ : Set k} (h₁ : IsXPair f u₁ v₁ B₁) (h₂ : IsXPair f u₂ v₂ B₂) :
    u₁ * v₂ = u₂ * v₁ := by
  apply eq_of_eval_eq_off_finite (h₁.2.2.1.union h₂.2.2.1)
  intro x hx
  rw [Set.mem_union, not_or] at hx
  obtain ⟨y, hy⟩ := exists_nonsingular W₁ x
  obtain ⟨x₁, y₁, h₁', e₁, r₁⟩ := h₁.2.2.2 x y hy hx.1
  obtain ⟨x₂, y₂, h₂', e₂, r₂⟩ := h₂.2.2.2 x y hy hx.2
  rw [e₁] at e₂
  obtain ⟨rfl, -⟩ := (Affine.Point.some.injEq _ _ _ _ _ _).mp e₂
  rw [eval_mul, eval_mul, ← r₁, ← r₂]; ring

omit [W₂.IsElliptic] in

theorem exists_isXPair {α : W₁.toAffine.Point →+ W₂.toAffine.Point} [W₂.IsElliptic]
    (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) : ∃ u v B, IsXPair α u v B := by
  obtain ⟨u, v, B, huv, hB, hrep⟩ := WeierstrassCurve.exists_xCoord_rep_of_mem_rationalHomSet k W₁ W₂ hα hα0
  have hlt : v.natDegree < u.natDegree :=
    WeierstrassCurve.natDegree_lt_of_xCoord_rep W₁ W₂ α huv hB hrep
  exact ⟨u, v, B, huv, lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hlt) (le_max_left _ _), hB,
    hrep⟩

end XPair

section Height

variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {W₁ W₂ W₃ : WeierstrassCurve k}

def HasHeight (f : W₁.toAffine.Point → W₂.toAffine.Point) (e : ℕ) : Prop :=
  ∃ (u v : k[X]) (B : Set k) (u₀ v₀ : k[X]), IsXPair f u v B ∧
    u = expand k (p ^ e) u₀ ∧ v = expand k (p ^ e) v₀ ∧
    IsCoprime u₀ v₀ ∧ 0 < max u₀.natDegree v₀.natDegree ∧ wronskian u₀ v₀ ≠ 0

variable [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

theorem hasHeight_unique {f : W₁.toAffine.Point → W₂.toAffine.Point} {a b : ℕ}
    (ha : HasHeight p f a) (hb : HasHeight p f b) : a = b := by
  obtain ⟨u₁, v₁, B₁, c₁, c₁', h₁, hu₁, hv₁, -, -, hw₁⟩ := ha
  obtain ⟨u₂, v₂, B₂, c₂, c₂', h₂, hu₂, hv₂, -, -, hw₂⟩ := hb
  exact expand_exponent_unique p h₁.1 h₂.1 (h₁.mul_eq_mul h₂) hu₁ hv₁ hu₂ hv₂ hw₁ hw₂

omit [W₂.IsElliptic] in
theorem exists_hasHeight [W₂.IsElliptic] {α : W₁.toAffine.Point →+ W₂.toAffine.Point}
    (hα : α ∈ rationalHomSet k W₁ W₂) (hα0 : α ≠ 0) : ∃ e, HasHeight p α e := by
  obtain ⟨u, v, B, h⟩ := exists_isXPair hα hα0
  obtain ⟨e, u₀, v₀, hu, hv, hc, hpos, hw⟩ := exists_expand_wronskian_ne_zero p h.1 h.2.1
  exact ⟨e, u, v, B, u₀, v₀, h, hu, hv, hc, hpos, hw⟩

theorem HasHeight.comp {f : W₂.toAffine.Point → W₃.toAffine.Point}
    {g : W₁.toAffine.Point → W₂.toAffine.Point} {a b : ℕ}
    (hf : HasHeight p f a) (hg : HasHeight p g b) : HasHeight p (f ∘ g) (a + b) := by
  obtain ⟨s, t, Bf, a₁, a₂, hfx, hs, ht, hac, hapos, haw⟩ := hf
  obtain ⟨u, v, Bg, b₁, b₂, hgx, hu, hv, hbc, hbpos, hbw⟩ := hg
  obtain ⟨U₀, V₀, hc, hpos, hw, hsem⟩ :=
    exists_comp_expand p hu hv hs ht hbc hbpos hbw hac hapos haw
  have hp : (p ^ (a + b)) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  refine ⟨expand k (p ^ (a + b)) U₀, expand k (p ^ (a + b)) V₀,
    Bg ∪ ⋃ c ∈ Bf, {x : k | u.eval x = c * v.eval x}, U₀, V₀, ⟨?_, ?_, ?_, ?_⟩, rfl, rfl, hc, hpos, hw⟩
  · exact (isCoprime_expand hp).mpr hc
  · rw [natDegree_expand, natDegree_expand, Nat.mul_max_mul_right]
    exact Nat.mul_pos hpos (Nat.pos_of_ne_zero hp)
  · exact hgx.2.2.1.union (hfx.2.2.1.biUnion fun c _ => finite_fibre hgx.1 hgx.2.1 c)
  · intro x y h hx
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists] at hx
    obtain ⟨hxg, hxf⟩ := hx
    obtain ⟨x', y', h', e₁, r₁⟩ := hgx.2.2.2 x y h hxg
    have hvx : v.eval x ≠ 0 := hgx.eval_ne_zero hxg
    have hx' : x' = u.eval x / v.eval x := by rw [← r₁, mul_div_cancel_right₀ _ hvx]
    have hx'B : x' ∉ Bf := fun hmem => hxf x' hmem (by rw [← r₁])
    obtain ⟨x'', y'', h'', e₂, r₂⟩ := hfx.2.2.2 x' y' h' hx'B
    have htx : t.eval x' ≠ 0 := hfx.eval_ne_zero hx'B
    obtain ⟨hV, hUV⟩ := hsem x hvx (by rwa [← hx'])
    refine ⟨x'', y'', h'', by rw [Function.comp_apply, e₁, e₂], ?_⟩
    rw [← hx'] at hUV
    rw [← eq_div_iff hV, hUV, eq_div_iff htx, r₂]

theorem hasHeight_id : HasHeight p (id : W₁.toAffine.Point → W₁.toAffine.Point) 0 := by
  refine ⟨X, 1, ∅, X, 1, ⟨isCoprime_one_right, by simp, Set.finite_empty, ?_⟩, by simp, by simp,
    isCoprime_one_right, by simp, ?_⟩
  · intro x y h _
    exact ⟨x, y, h, rfl, by simp⟩
  · simp [wronskian]

end Height

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

noncomputable abbrev frobTwist (W : WeierstrassCurve k) : WeierstrassCurve k := W.map (frobenius k p)

scoped instance instIsEllipticFrobTwist (W : WeierstrassCurve k) [W.IsElliptic] : (frobTwist p W).IsElliptic := by
  unfold frobTwist; infer_instance

omit [IsAlgClosed k] [DecidableEq k] [Fact p.Prime] [CharP k p] in

scoped instance instIsEllipticBaseChangeSelf (W : WeierstrassCurve k) [W.IsElliptic] : (W.baseChange k).IsElliptic := by
  unfold WeierstrassCurve.baseChange; infer_instance

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_nonsingular_iff (W : WeierstrassCurve k) (x y : k) :
    (frobTwist p W).toAffine.Nonsingular (x ^ p) (y ^ p) ↔ W.toAffine.Nonsingular x y := by
  have := Affine.map_nonsingular W.toAffine (f := frobenius k p) (frobenius_inj k p) x y
  simpa only [frobenius_def] using this

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_nonsingular (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    (frobTwist p W).toAffine.Nonsingular (x ^ p) (y ^ p) :=
  (frob_nonsingular_iff p W x y).mpr h

noncomputable def frobPt (W : WeierstrassCurve k) :
    W.toAffine.Point →+ (frobTwist p W).toAffine.Point where
  toFun P := match P with
    | 0 => 0
    | .some x y h => .some (x ^ p) (y ^ p) (frob_nonsingular p W h)
  map_zero' := rfl
  map_add' := by
    have hf : ∀ z : k, frobenius k p z = z ^ p := frobenius_def p
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.left hxy.right]
      have h2 : y₁ ^ p = (frobTwist p W).toAffine.negY (x₂ ^ p) (y₂ ^ p) := by
        rw [hxy.right, ← hf, ← hf, ← hf, Affine.map_negY]
      rw [Affine.Point.add_of_Y_eq (congr_arg (· ^ p) hxy.left) h2]
    · have hxy' : ¬ (x₁ ^ p = x₂ ^ p ∧
          y₁ ^ p = (frobTwist p W).toAffine.negY (x₂ ^ p) (y₂ ^ p)) := by
        rintro ⟨e1, e2⟩
        apply hxy
        refine ⟨frobenius_inj k p (by rw [hf, hf]; exact e1), frobenius_inj k p ?_⟩
        rw [hf, hf, e2, ← hf, ← hf, Affine.map_negY, hf]
      rw [Affine.Point.add_some hxy, Affine.Point.add_some hxy']
      simp only [Affine.Point.some.injEq]
      refine ⟨?_, ?_⟩
      · rw [← hf, ← hf, ← hf, ← hf, ← hf, Affine.map_slope, Affine.map_addX]
      · rw [← hf, ← hf, ← hf, ← hf, ← hf, Affine.map_slope, Affine.map_addY]

theorem frobPt_some (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    frobPt p W (.some x y h) = .some (x ^ p) (y ^ p) (frob_nonsingular p W h) := rfl

theorem frobPt_injective (W : WeierstrassCurve k) : Function.Injective (frobPt p W) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · exact absurd h.symm (Affine.Point.some_ne_zero _)
  · exact absurd h (Affine.Point.some_ne_zero _)
  · rw [frobPt_some, frobPt_some, Affine.Point.some.injEq] at h
    obtain ⟨e1, e2⟩ := h
    have hx : x₁ = x₂ := frobenius_inj k p (by rw [frobenius_def, frobenius_def]; exact e1)
    have hy : y₁ = y₂ := frobenius_inj k p (by rw [frobenius_def, frobenius_def]; exact e2)
    subst hx hy
    rfl

theorem frobPt_surjective (W : WeierstrassCurve k) : Function.Surjective (frobPt p W) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rintro (_ | ⟨u, v, h⟩)
  · exact ⟨0, rfl⟩
  · obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq u hp
    obtain ⟨y, rfl⟩ := IsAlgClosed.exists_pow_nat_eq v hp
    exact ⟨.some x y ((frob_nonsingular_iff p W x y).mp h), rfl⟩

theorem frobPt_ne_zero (W : WeierstrassCurve k) [W.IsElliptic] : frobPt p W ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_nonsingular W 0
  intro h0
  have : frobPt p W (.some 0 y hy) = 0 := by rw [h0]; rfl
  rw [frobPt_some] at this
  exact Affine.Point.some_ne_zero _ this

theorem frobPt_mem_rationalHomSet (W : WeierstrassCurve k) :
    (frobPt p W : (W.baseChange k).toAffine.Point →+ ((frobTwist p W).baseChange k).toAffine.Point) ∈
      rationalHomSet k W (frobTwist p W) := by
  refine Or.inr ⟨C (X ^ p), 1, X ^ p, 1, ∅, Set.finite_empty, fun x y h _ => ?_⟩
  have e0 : evalEvalBC k (1 : k[X][X]) x y = 1 := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e1 : evalEvalBC k (C (X ^ p) : k[X][X]) x y = x ^ p := by
    simp [evalEvalBC, Polynomial.evalEval]
  have e2 : evalEvalBC k (X ^ p : k[X][X]) x y = y ^ p := by
    simp [evalEvalBC, Polynomial.evalEval]
  refine ⟨by rw [e0]; exact one_ne_zero, by rw [e0]; exact one_ne_zero, ?_⟩
  simp only [e0, e1, e2, div_one]
  exact ⟨frob_nonsingular p W h, rfl⟩

theorem hasHeight_frobPt (W : WeierstrassCurve k) [W.IsElliptic] : HasHeight p (frobPt p W) 1 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨X ^ p, 1, ∅, X, 1, ⟨isCoprime_one_right, ?_, Set.finite_empty, ?_⟩, ?_, ?_,
    isCoprime_one_right, by simp, ?_⟩
  · rw [natDegree_X_pow]; exact lt_of_lt_of_le hp (le_max_left _ _)
  · intro x y h _
    exact ⟨x ^ p, y ^ p, frob_nonsingular p W h, rfl, by simp⟩
  · rw [pow_one, expand_X]
  · rw [map_one]
  · simp [wronskian]

variable {W W₃ : WeierstrassCurve k} [W.IsElliptic] [W₃.IsElliptic]

theorem exists_eq_comp_frobPt_of_hasHeight {δ : W.toAffine.Point →+ W₃.toAffine.Point}
    (hδ : δ ∈ rationalHomSet k W W₃) (hδ0 : δ ≠ 0) {e : ℕ} (he : HasHeight p δ e) (h1 : 1 ≤ e) :
    ∃ γ ∈ rationalHomSet k (frobTwist p W) W₃, δ = γ.comp (frobPt p W) := by
  obtain ⟨u, v, B, c₁, c₂, hpair, hu, hv, hcc, -, -⟩ := he
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set d₁ := expand k (p ^ (e - 1)) c₁ with hd₁
  set d₂ := expand k (p ^ (e - 1)) c₂ with hd₂
  have hpe : p ^ e = p * p ^ (e - 1) := by rw [← pow_succ', Nat.sub_add_cancel h1]
  have hu' : u = expand k p d₁ := by rw [hu, hd₁, expand_expand, ← hpe]
  have hv' : v = expand k p d₂ := by rw [hv, hd₂, expand_expand, ← hpe]
  have hd : IsCoprime d₁ d₂ := (isCoprime_expand (pow_ne_zero _ hp)).mpr hcc
  have hr : IsCoprime (X : k[X]) 1 := isCoprime_one_right
  have hrw : wronskian (X : k[X]) 1 ≠ 0 := by simp [wronskian]
  have hker : ∀ T : W.toAffine.Point, frobPt p W T = 0 → δ T = 0 := by
    intro T hT
    have : T = 0 := frobPt_injective p W (by rw [hT, map_zero])
    rw [this, map_zero]
  have hρx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : (frobTwist p W).toAffine.Nonsingular x' y'),
        frobPt p W (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * (1 : k[X]).eval (x ^ p ^ 1) = (X : k[X]).eval (x ^ p ^ 1) := by
    intro x y h _
    exact ⟨x ^ p, y ^ p, frob_nonsingular p W h, rfl, by simp⟩
  have hδx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : W₃.toAffine.Nonsingular x' y'),
        δ (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * d₂.eval (x ^ p ^ 1) = d₁.eval (x ^ p ^ 1) := by
    intro x y h hx
    obtain ⟨x', y', h', e1, r1⟩ := hpair.2.2.2 x y h hx
    refine ⟨x', y', h', e1, ?_⟩
    rw [pow_one, ← expand_eval, ← expand_eval, ← hu', ← hv']; exact r1
  exact WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p W (frobTwist p W) W₃
    (frobPt_mem_rationalHomSet p W) hδ (frobPt_ne_zero p W) hδ0 hker 1 hr hrw hd hpair.2.2.1 hρx hδx

theorem exists_hasHeight_pos_comp_frobPt {γ : (frobTwist p W).toAffine.Point →+ W₃.toAffine.Point}
    (hγ : γ ∈ rationalHomSet k (frobTwist p W) W₃) (hγ0 : γ ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ HasHeight p (⇑γ ∘ ⇑(frobPt p W)) m := by
  obtain ⟨e, he⟩ := exists_hasHeight p hγ hγ0
  exact ⟨e + 1, Nat.le_add_left 1 e, he.comp p (hasHeight_frobPt p W)⟩

end Frobenius

section Frobenius2

variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable {W W₃ : WeierstrassCurve k} [W.IsElliptic] [W₃.IsElliptic]

theorem frobPt_frobPt_some (W : WeierstrassCurve k) {x y : k} (h : W.toAffine.Nonsingular x y) :
    (frobPt p (frobTwist p W)) (frobPt p W (.some x y h)) =
      .some (x ^ p ^ 2) (y ^ p ^ 2) (by
        have h1 := frob_nonsingular p (frobTwist p W) (frob_nonsingular p W h)
        rwa [← pow_mul, ← pow_mul, ← sq] at h1) := by
  rw [frobPt_some, frobPt_some]
  congr 1 <;> rw [← pow_mul, ← sq]

theorem exists_eq_comp_frobPt_frobPt_of_hasHeight {δ : W.toAffine.Point →+ W₃.toAffine.Point}
    (hδ : δ ∈ rationalHomSet k W W₃) (hδ0 : δ ≠ 0) {e : ℕ} (he : HasHeight p δ e) (h2 : 2 ≤ e) :
    ∃ γ ∈ rationalHomSet k (frobTwist p (frobTwist p W)) W₃,
      δ = γ.comp ((frobPt p (frobTwist p W)).comp (frobPt p W)) := by
  obtain ⟨u, v, B, c₁, c₂, hpair, hu, hv, hcc, -, -⟩ := he
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set d₁ := expand k (p ^ (e - 2)) c₁ with hd₁
  set d₂ := expand k (p ^ (e - 2)) c₂ with hd₂
  have hpe : p ^ e = p ^ 2 * p ^ (e - 2) := by rw [← pow_add, Nat.add_sub_cancel' h2]
  have hu' : u = expand k (p ^ 2) d₁ := by rw [hu, hd₁, expand_expand, ← hpe]
  have hv' : v = expand k (p ^ 2) d₂ := by rw [hv, hd₂, expand_expand, ← hpe]
  have hd : IsCoprime d₁ d₂ := (isCoprime_expand (pow_ne_zero _ hp)).mpr hcc
  have hr : IsCoprime (X : k[X]) 1 := isCoprime_one_right
  have hrw : wronskian (X : k[X]) 1 ≠ 0 := by simp [wronskian]
  have hFFmem : (frobPt p (frobTwist p W)).comp (frobPt p W) ∈ rationalHomSet k W (frobTwist p (frobTwist p W)) :=
    WeierstrassCurve.comp_mem_rationalHomSet k W (frobTwist p W) (frobTwist p (frobTwist p W))
      (frobPt_mem_rationalHomSet p W) (frobPt_mem_rationalHomSet p (frobTwist p W))
  have hFFinj : Function.Injective ((frobPt p (frobTwist p W)).comp (frobPt p W)) :=
    (frobPt_injective p (frobTwist p W)).comp (frobPt_injective p W)
  have hFF0 : (frobPt p (frobTwist p W)).comp (frobPt p W) ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := exists_nonsingular W 0
    have h1 : ((frobPt p (frobTwist p W)).comp (frobPt p W)) (.some 0 y hy) =
        ((frobPt p (frobTwist p W)).comp (frobPt p W)) 0 := by rw [h0]; rfl
    exact Affine.Point.some_ne_zero _ (hFFinj h1)
  have hker : ∀ T : W.toAffine.Point, ((frobPt p (frobTwist p W)).comp (frobPt p W)) T = 0 → δ T = 0 := by
    intro T hT
    have : T = 0 := hFFinj (by rw [hT, map_zero])
    rw [this, map_zero]
  have hρx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : (frobTwist p (frobTwist p W)).toAffine.Nonsingular x' y'),
        ((frobPt p (frobTwist p W)).comp (frobPt p W)) (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * (1 : k[X]).eval (x ^ p ^ 2) = (X : k[X]).eval (x ^ p ^ 2) := by
    intro x y h _
    exact ⟨x ^ p ^ 2, y ^ p ^ 2, _, by rw [AddMonoidHom.comp_apply, frobPt_frobPt_some], by simp⟩
  have hδx : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), x ∉ B →
      ∃ (x' y' : k) (h' : W₃.toAffine.Nonsingular x' y'),
        δ (Affine.Point.some x y h) = Affine.Point.some x' y' h' ∧
          x' * d₂.eval (x ^ p ^ 2) = d₁.eval (x ^ p ^ 2) := by
    intro x y h hx
    obtain ⟨x', y', h', e1, r1⟩ := hpair.2.2.2 x y h hx
    refine ⟨x', y', h', e1, ?_⟩
    rw [← expand_eval, ← expand_eval, ← hu', ← hv']; exact r1
  exact WeierstrassCurve.exists_mem_rationalHomSet_comp_eq_of_ker_le_of_xCoord_expand p W
    (frobTwist p (frobTwist p W)) W₃ hFFmem hδ hFF0 hδ0 hker 2 hr hrw hd hpair.2.2.1 hρx hδx

end Frobenius2

section Quat

p2m_open "QuaternionAlgebra~baseChange"
open scoped Quaternion Pointwise

variable {a b : ℚ}

theorem quat_intCast_eq_coe (m : ℤ) : ((m : ℤ) : ℍ[ℚ, a, b]) = ((m : ℚ) : ℍ[ℚ, a, b]) := by
  ext <;> simp

theorem quat_natCast_mul_eq_smul (n : ℕ) (z : ℍ[ℚ, a, b]) : (n : ℍ[ℚ, a, b]) * z = (n : ℚ) • z := by
  rw [← QuaternionAlgebra.coe_natCast, QuaternionAlgebra.coe_mul_eq_smul]

theorem quat_mul_natCast_eq_smul (n : ℕ) (z : ℍ[ℚ, a, b]) : z * (n : ℍ[ℚ, a, b]) = (n : ℚ) • z := by
  rw [← (Nat.cast_commute n z).eq, quat_natCast_mul_eq_smul]

theorem star_mem_of_isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {t : ℍ[ℚ, a, b]} (ht : t ∈ Λ) :
    star t ∈ Λ := by
  obtain ⟨-, tt, htt⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ ht
  have h1 : star t = ((trd t : ℚ) : ℍ[ℚ, a, b]) - t := by
    rw [← add_star_eq_coe_trd t]; abel
  rw [h1, ← htt, ← quat_intCast_eq_coe, ← zsmul_one]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hΛ.one_mem) ht

theorem mem_star_image_smul_iff {L : Submodule ℤ ℍ[ℚ, a, b]} {d : (ℍ[ℚ, a, b])ˣ} {s : ℍ[ℚ, a, b]} :
    s ∈ star '' ((d • L : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) ↔
      ∃ z ∈ L, s = star ((d : ℍ[ℚ, a, b]) * z) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Units.smul_def, Submodule.mem_smul_pointwise_iff_exists] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(d : ℍ[ℚ, a, b]) * z, ?_, rfl⟩
    rw [SetLike.mem_coe, Units.smul_def, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨z, hz, rfl⟩

theorem q_mul_mem {Lx Lxπ Lπ : Submodule ℤ ℍ[ℚ, a, b]} (hA : Lxπ = Lx * Lπ)
    {s t : ℍ[ℚ, a, b]} (hs : s ∈ Lx) (ht : t ∈ Lπ) : s * t ∈ Lxπ := by
  rw [hA]; exact Submodule.mul_mem_mul hs ht

theorem q_mem_of_forall_mul {Lx Lxπ Lπ : Submodule ℤ ℍ[ℚ, a, b]} (q' : ℕ) (hq' : q' ≠ 0)
    (hA : Lxπ = Lx * Lπ) (hqmem : (q' : ℍ[ℚ, a, b]) ∈ Lπ * Lπ)
    {z : ℍ[ℚ, a, b]} (hz : ∀ t ∈ Lπ, ∃ y ∈ Lx, z * t = (q' : ℚ) • y) : z ∈ Lxπ := by
  have key : ∀ r ∈ Lπ * Lπ, ∃ y ∈ Lxπ, z * r = (q' : ℚ) • y := by
    intro r hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro t ht t' ht'
      obtain ⟨y, hy, hzy⟩ := hz t ht
      refine ⟨y * t', q_mul_mem hA hy ht', ?_⟩
      rw [← mul_assoc, hzy, smul_mul_assoc]
    · rintro r₁ r₂ ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
      exact ⟨y₁ + y₂, add_mem hy₁ hy₂, by rw [mul_add, h₁, h₂, smul_add]⟩
  obtain ⟨y, hy, hzy⟩ := key _ hqmem
  rw [quat_mul_natCast_eq_smul] at hzy
  have hq0 : (q' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq'
  rw [smul_right_injective ℍ[ℚ, a, b] hq0 hzy]
  exact hy

end Quat

section Assembly

p2m_open "QuaternionAlgebra~baseChange"
open scoped Quaternion TensorProduct NumberField Pointwise

theorem frobPt_eq_ratPointHom {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (p : ℕ) [Fact p.Prime] [CharP κ p] (W : WeierstrassCurve κ) :
    frobPt p W = WeierstrassCurve.ratPointHom (frobenius κ p) (W₀ := W) := by
  ext P
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

theorem comp_ne_zero_of_surjective {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {g : B →+ C} {f : A →+ B} (hg : g ≠ 0) (hf : Function.Surjective f) : g.comp f ≠ 0 := by
  intro h0
  apply hg
  ext b
  obtain ⟨a, rfl⟩ := hf b
  exact DFunLike.congr_fun h0 a

theorem main {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hπv : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
        (π : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hπP : ∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele Λ₁ π ↔
      h ∈ Λ₁ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h)))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (W : WeierstrassCurve κ) [W.IsElliptic]
    (χ : X₁.toAffine.Point →+ W.toAffine.Point) (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0)
    (d : (ℍ[ℚ, a, b])ˣ)
    (hreal : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :
    θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ (frobTwist q' W) ((frobPt q' W).comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * π) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  classical
  have hO : IsOrder Λ₁ := hΛ₁.isOrder
  have hq'0 : q' ≠ 0 := (Fact.out : q'.Prime).ne_zero

  set Lx := Submodule.ofFiniteIdele Λ₁ x with hLx
  set Lπ := Submodule.ofFiniteIdele Λ₁ π with hLπ
  set Lxπ := Submodule.ofFiniteIdele Λ₁ (x * π) with hLxπ

  obtain ⟨hAx, hBx⟩ := QuaternionAlgebra.IsMaximalOrder.ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
    q' hdef Λ₁ hΛ₁ π hπv hπP x
  obtain ⟨hAxπ, -⟩ := QuaternionAlgebra.IsMaximalOrder.ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
    q' hdef Λ₁ hΛ₁ π hπv hπP (x * π)
  obtain ⟨-, hB1⟩ := QuaternionAlgebra.IsMaximalOrder.ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
    q' hdef Λ₁ hΛ₁ π hπv hπP 1
  obtain ⟨hA1π, -⟩ := QuaternionAlgebra.IsMaximalOrder.ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
    q' hdef Λ₁ hΛ₁ π hπv hπP (1 * π)
  have hL1 : Submodule.ofFiniteIdele Λ₁ 1 = Λ₁ := Submodule.ofFiniteIdele_one Λ₁ hO.fg hO.spanTop

  have hqmem : (q' : ℍ[ℚ, a, b]) ∈ Lπ * Lπ := by
    have h1 : (q' : ℍ[ℚ, a, b]) ∈ Submodule.ofFiniteIdele Λ₁ (1 * π * π) := by
      rw [hB1]
      refine ⟨1, by rw [hL1]; exact hO.one_mem, ?_⟩
      rw [← QuaternionAlgebra.coe_natCast, ← QuaternionAlgebra.coe_one, QuaternionAlgebra.smul_coe, mul_one]
    rwa [hA1π, one_mul] at h1

  have hiii : ∀ z ∈ Lxπ, ∀ t ∈ Lπ, ∃ y ∈ Lx, z * t = (q' : ℚ) • y := by
    intro z hz t ht
    have h1 : z * t ∈ Submodule.ofFiniteIdele Λ₁ (x * π * π) := by rw [hAxπ]; exact Submodule.mul_mem_mul hz ht
    exact (hBx (z * t)).mp h1

  have hPset : ∀ t ∈ Lπ, star t ∈ {h | h ∈ Λ₁ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h))} := by
    intro t ht
    obtain ⟨htΛ, hcase⟩ := (hπP t).mp ht
    refine ⟨star_mem_of_isOrder hO htΛ, ?_⟩
    rw [star_eq_zero, nrd_star]; exact hcase

  have hP := CerednikDrinfeld.image_kernelIdealSet_ratPointHom_frobenius_eq_setOf_padicValRat_nrd
    q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ
  rw [← frobPt_eq_ratPointHom] at hP
  have hPmem : ∀ t ∈ Lπ, ∃ (e : WeierstrassCurve.rationalEndSubring κ X₁)
      (γ : (frobTwist q' X₁).toAffine.Point →+ X₁.toAffine.Point),
      γ ∈ WeierstrassCurve.rationalHomSet κ (frobTwist q' X₁) X₁ ∧
      (e : AddMonoid.End (X₁.baseChange κ).toAffine.Point) = γ.comp (frobPt q' X₁) ∧ θ₁ e = star t := by
    intro t ht
    have h1 := hPset t ht
    rw [← hP] at h1
    obtain ⟨e, ⟨γ, hγ, heγ⟩, he⟩ := h1
    exact ⟨e, γ, hγ, heγ, he⟩

  have hssW : ∀ P : W.toAffine.Point, q' • P = 0 → P = 0 :=
    WeierstrassCurve.forall_smul_eq_zero_of_mem_rationalHomSet_of_forall_smul_eq_zero q' X₁ hss W χ hχ hχ0
  obtain ⟨ε, ε', hε, hε', -, -, -, hV⟩ :=
    WeierstrassCurve.exists_ratPointHom_frobenius_comp_ratPointHom_frobenius_eq_comp_nsmul_of_forall_nsmul_eq_zero
      q' W hssW
  rw [← frobPt_eq_ratPointHom, ← frobPt_eq_ratPointHom] at hV

  have hFmem : (frobPt q' W) ∈ WeierstrassCurve.rationalHomSet κ W (frobTwist q' W) := frobPt_mem_rationalHomSet q' W
  have hK'K : ∀ k' ∈ WeierstrassCurve.kernelIdealSet κ X₁ (frobTwist q' W) ((frobPt q' W).comp χ),
      k' ∈ WeierstrassCurve.kernelIdealSet κ X₁ W χ := by
    rintro k' ⟨ρ', hρ', hk'⟩
    exact ⟨ρ'.comp (frobPt q' W), WeierstrassCurve.comp_mem_rationalHomSet κ W (frobTwist q' W) X₁ hFmem hρ',
      by rw [hk', AddMonoidHom.comp_assoc]; rfl⟩

  have hS_of_K : ∀ k ∈ WeierstrassCurve.kernelIdealSet κ X₁ W χ, ∃ z ∈ Lx, θ₁ k = star ((d : ℍ[ℚ, a, b]) * z) := by
    intro k hk
    have h1 : θ₁ k ∈ θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ := ⟨k, hk, rfl⟩
    rw [hreal] at h1
    exact mem_star_image_smul_iff.mp h1
  have hK_of_S : ∀ z ∈ Lx, ∃ k ∈ WeierstrassCurve.kernelIdealSet κ X₁ W χ, θ₁ k = star ((d : ℍ[ℚ, a, b]) * z) := by
    intro z hz
    have h1 : star ((d : ℍ[ℚ, a, b]) * z) ∈ star '' ((d • Lx : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) :=
      mem_star_image_smul_iff.mpr ⟨z, hz, rfl⟩
    rw [← hreal] at h1
    obtain ⟨k, hk, hkz⟩ := h1
    exact ⟨k, hk, hkz⟩

  have hI : ∀ (γ : (frobTwist q' X₁).toAffine.Point →+ X₁.toAffine.Point)
      (ρ : W.toAffine.Point →+ X₁.toAffine.Point),
      γ ∈ WeierstrassCurve.rationalHomSet κ (frobTwist q' X₁) X₁ → ρ ∈ WeierstrassCurve.rationalHomSet κ W X₁ →
      ∃ ρ'' ∈ WeierstrassCurve.rationalHomSet κ (frobTwist q' W) X₁,
        (γ.comp (frobPt q' X₁)).comp ρ = ρ''.comp (frobPt q' W) := by
    intro γ ρ hγ hρ
    by_cases hγ0 : γ = 0
    · exact ⟨0, WeierstrassCurve.zero_mem_rationalHomSet κ _ _, by rw [hγ0]; rfl⟩
    by_cases hρ0 : ρ = 0
    · refine ⟨0, WeierstrassCurve.zero_mem_rationalHomSet κ _ _, ?_⟩
      rw [hρ0, AddMonoidHom.comp_zero]; rfl
    obtain ⟨m, hm1, hγF⟩ := exists_hasHeight_pos_comp_frobPt q' (W := X₁) (W₃ := X₁) hγ hγ0
    obtain ⟨eρ, hρh⟩ := exists_hasHeight q' hρ hρ0
    have hδmem : (γ.comp (frobPt q' X₁)).comp ρ ∈ WeierstrassCurve.rationalHomSet κ W X₁ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ W X₁ X₁ hρ
        (WeierstrassCurve.comp_mem_rationalHomSet κ X₁ (frobTwist q' X₁) X₁ (frobPt_mem_rationalHomSet q' X₁) hγ)
    have hδ0 : (γ.comp (frobPt q' X₁)).comp ρ ≠ 0 :=
      comp_ne_zero_of_surjective (comp_ne_zero_of_surjective hγ0 (frobPt_surjective q' X₁))
        (WeierstrassCurve.surjective_of_mem_rationalHomSet κ hρ hρ0)
    have hδh : HasHeight q' ((γ.comp (frobPt q' X₁)).comp ρ) (m + eρ) := hγF.comp q' hρh
    obtain ⟨ρ'', hρ'', hfac⟩ := exists_eq_comp_frobPt_of_hasHeight q' hδmem hδ0 hδh (by omega)
    exact ⟨ρ'', hρ'', hfac⟩

  have hII : ∀ (γ : (frobTwist q' X₁).toAffine.Point →+ X₁.toAffine.Point)
      (ρ' : (frobTwist q' W).toAffine.Point →+ X₁.toAffine.Point),
      γ ∈ WeierstrassCurve.rationalHomSet κ (frobTwist q' X₁) X₁ →
      ρ' ∈ WeierstrassCurve.rationalHomSet κ (frobTwist q' W) X₁ →
      ∃ ν ∈ WeierstrassCurve.rationalHomSet κ W X₁,
        ∀ P, γ (frobPt q' X₁ (ρ' (frobPt q' W P))) = ν (q' • P) := by
    intro γ ρ' hγ hρ'
    by_cases hγ0 : γ = 0
    · exact ⟨0, WeierstrassCurve.zero_mem_rationalHomSet κ _ _, fun P => by rw [hγ0]; rfl⟩
    by_cases hρ0 : ρ' = 0
    · refine ⟨0, WeierstrassCurve.zero_mem_rationalHomSet κ _ _, fun P => ?_⟩
      rw [hρ0, AddMonoidHom.zero_apply, map_zero, map_zero]; rfl
    obtain ⟨m, hm1, hγF⟩ := exists_hasHeight_pos_comp_frobPt q' (W := X₁) (W₃ := X₁) hγ hγ0
    obtain ⟨eρ, hρh⟩ := exists_hasHeight q' hρ' hρ0
    have hδmem : ((γ.comp (frobPt q' X₁)).comp ρ').comp (frobPt q' W) ∈ WeierstrassCurve.rationalHomSet κ W X₁ :=
      WeierstrassCurve.comp_mem_rationalHomSet κ W (frobTwist q' W) X₁ hFmem
        (WeierstrassCurve.comp_mem_rationalHomSet κ (frobTwist q' W) X₁ X₁ hρ'
          (WeierstrassCurve.comp_mem_rationalHomSet κ X₁ (frobTwist q' X₁) X₁ (frobPt_mem_rationalHomSet q' X₁) hγ))
    have hδ0 : ((γ.comp (frobPt q' X₁)).comp ρ').comp (frobPt q' W) ≠ 0 :=
      comp_ne_zero_of_surjective
        (comp_ne_zero_of_surjective (comp_ne_zero_of_surjective hγ0 (frobPt_surjective q' X₁))
          (WeierstrassCurve.surjective_of_mem_rationalHomSet κ hρ' hρ0))
        (frobPt_surjective q' W)
    have hδh : HasHeight q' (((γ.comp (frobPt q' X₁)).comp ρ').comp (frobPt q' W)) (m + eρ + 1) :=
      (hγF.comp q' hρh).comp q' (hasHeight_frobPt q' W)
    obtain ⟨μ, hμ, hfac⟩ := exists_eq_comp_frobPt_frobPt_of_hasHeight q' hδmem hδ0 hδh (by omega)
    refine ⟨μ.comp ε', WeierstrassCurve.comp_mem_rationalHomSet κ W (frobTwist q' (frobTwist q' W)) X₁ hε' hμ, fun P => ?_⟩
    have h1 := DFunLike.congr_fun hfac P
    have h2 := DFunLike.congr_fun hV P
    calc γ (frobPt q' X₁ (ρ' (frobPt q' W P)))
        = (μ.comp ((frobPt q' (frobTwist q' W)).comp (frobPt q' W))) P := h1
      _ = μ ((frobPt q' (frobTwist q' W)) ((frobPt q' W) P)) := rfl
      _ = μ (ε' (((q' : ℕ) • AddMonoidHom.id W.toAffine.Point) P)) := congrArg μ h2
      _ = (μ.comp ε') (q' • P) := rfl

  apply Set.Subset.antisymm
  ·
    rintro _ ⟨k', hk', rfl⟩
    obtain ⟨z₁, hz₁, hkz₁⟩ := hS_of_K k' (hK'K k' hk')
    obtain ⟨ρ', hρ', hk'ρ'⟩ := hk'
    suffices hz₁π : z₁ ∈ Lxπ by
      rw [hkz₁]; exact mem_star_image_smul_iff.mpr ⟨z₁, hz₁π, rfl⟩
    refine q_mem_of_forall_mul q' hq'0 hAx hqmem fun t ht => ?_
    obtain ⟨e, γ, hγ, heγ, het⟩ := hPmem t ht
    obtain ⟨ν, hν, hνP⟩ := hII γ ρ' hγ hρ'

    have hk₂mem : ((ν.comp χ : X₁.toAffine.Point →+ X₁.toAffine.Point) :
        AddMonoid.End (X₁.baseChange κ).toAffine.Point) ∈ WeierstrassCurve.rationalEndSubring κ X₁ :=
      (WeierstrassCurve.mem_rationalEndSubring_iff_mem_rationalHomSet κ X₁ _).mpr
        (WeierstrassCurve.comp_mem_rationalHomSet κ X₁ W X₁ hχ hν)
    set k₂ : WeierstrassCurve.rationalEndSubring κ X₁ := ⟨_, hk₂mem⟩ with hk₂
    have hk₂K : k₂ ∈ WeierstrassCurve.kernelIdealSet κ X₁ W χ := ⟨ν, hν, rfl⟩
    obtain ⟨z₃, hz₃, hkz₃⟩ := hS_of_K k₂ hk₂K

    have hek : e * k' = (q' : ℕ) • k₂ := by
      apply Subtype.ext
      rw [Subring.coe_mul, heγ, hk'ρ']
      change (γ.comp (frobPt q' X₁)).comp (ρ'.comp ((frobPt q' W).comp χ)) =
        (((q' : ℕ) • k₂ : WeierstrassCurve.rationalEndSubring κ X₁) : AddMonoid.End (X₁.baseChange κ).toAffine.Point)
      rw [nsmul_eq_mul, Subring.coe_mul]
      ext P
      change γ (frobPt q' X₁ (ρ' (frobPt q' W (χ P)))) = ((q' : ℕ) : AddMonoid.End (X₁.baseChange κ).toAffine.Point) (ν (χ P))
      rw [AddMonoid.End.natCast_apply, ← map_nsmul]
      exact hνP (χ P)
    have h1 : θ₁ e * θ₁ k' = (q' : ℍ[ℚ, a, b]) * θ₁ k₂ := by
      rw [← map_mul, hek, map_nsmul, nsmul_eq_mul]
    rw [het, hkz₁, hkz₃] at h1
    have h3 := congrArg star h1
    simp only [star_mul, star_star, star_natCast] at h3
    rw [mul_assoc, mul_assoc] at h3
    have h4 := d.isUnit.mul_left_cancel h3
    exact ⟨z₃, hz₃, by rw [h4, quat_mul_natCast_eq_smul]⟩
  ·
    intro s hs
    obtain ⟨z₁, hz₁, rfl⟩ := mem_star_image_smul_iff.mp hs
    rw [hLxπ, hAx] at hz₁

    have key : ∀ z ∈ Lx * Lπ, star ((d : ℍ[ℚ, a, b]) * z) ∈
        θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ (frobTwist q' W) ((frobPt q' W).comp χ) := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro z hz t ht
        obtain ⟨k, ⟨ρ, hρ, hkρ⟩, hkz⟩ := hK_of_S z hz
        obtain ⟨e, γ, hγ, heγ, het⟩ := hPmem t ht
        obtain ⟨ρ'', hρ'', hfac⟩ := hI γ ρ hγ hρ
        refine ⟨e * k, ⟨ρ'', hρ'', ?_⟩, ?_⟩
        · rw [Subring.coe_mul, heγ, hkρ]
          change ((γ.comp (frobPt q' X₁)).comp ρ).comp χ = (ρ''.comp (frobPt q' W)).comp χ
          exact congrArg (fun φ => AddMonoidHom.comp φ χ) hfac
        · rw [map_mul, het, hkz, ← star_mul, mul_assoc]
      · intro u w hu hw
        obtain ⟨k₁, hk₁, hk₁u⟩ := hu
        obtain ⟨k₂, hk₂, hk₂w⟩ := hw
        obtain ⟨ρ₁, hρ₁, hk₁ρ⟩ := hk₁
        obtain ⟨ρ₂, hρ₂, hk₂ρ⟩ := hk₂
        refine ⟨k₁ + k₂, ⟨ρ₁ + ρ₂, WeierstrassCurve.add_mem_rationalHomSet κ (frobTwist q' W) X₁ hρ₁ hρ₂, ?_⟩, ?_⟩
        · rw [Subring.coe_add, hk₁ρ, hk₂ρ, AddMonoidHom.add_comp]; rfl
        · rw [map_add, hk₁u, hk₂w, mul_add, star_add]
    exact key z₁ hz₁

end Assembly

end FrobKernelIdealShift
p2m_reactivate "P2MW.S_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul.FrobKernelIdealShift"

open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra~baseChange CerednikDrinfeld"

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] [Algebra (ZMod q') κ] [Algebra.IsAlgebraic (ZMod q') κ]
    (X₁ : WeierstrassCurve κ) [X₁.IsElliptic] (hss : ∀ P : X₁.toAffine.Point, q' • P = 0 → P = 0)
    (a b : ℚ) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (θ₁ : ↥(WeierstrassCurve.rationalEndSubring κ X₁) →+* ℍ[ℚ, a, b])
    (hθ₁ : Function.Injective θ₁) (hθ₁Λ : Set.range θ₁ = (Λ₁ : Set ℍ[ℚ, a, b]))
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hπv : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
        (π : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hπP : ∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele Λ₁ π ↔
      h ∈ Λ₁ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h)))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (W : WeierstrassCurve κ) [W.IsElliptic]
    (χ : X₁.toAffine.Point →+ W.toAffine.Point) (hχ : χ ∈ WeierstrassCurve.rationalHomSet κ X₁ W) (hχ0 : χ ≠ 0)
    (d : (ℍ[ℚ, a, b])ˣ)
    (hreal : θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ W χ =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ x : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b])) :
    θ₁ '' WeierstrassCurve.kernelIdealSet κ X₁ (W.map (frobenius κ q'))
        ((WeierstrassCurve.ratPointHom (frobenius κ q') (W₀ := W)).comp χ) =
      star '' ((d • Submodule.ofFiniteIdele Λ₁ (x * π) : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ[ℚ, a, b]) := by
  rw [← FrobKernelIdealShift.frobPt_eq_ratPointHom]
  exact FrobKernelIdealShift.main q' X₁ hss a b hdef Λ₁ hΛ₁ θ₁ hθ₁ hθ₁Λ π hπv hπP x W χ hχ hχ0 d hreal

end S_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul
end P2MW
export P2MW.S_CerednikDrinfeld_image_kernelIdealSet_ratPointHom_frobenius_comp_eq_star_smul_ofFiniteIdele_mul (solution)
