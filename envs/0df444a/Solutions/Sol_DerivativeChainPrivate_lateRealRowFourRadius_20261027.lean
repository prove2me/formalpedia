-- Prove2me | solution 1 for DerivativeChainPrivate.lateRealRowFourRadius_20261027
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:07:54.252005+00:00
-- url     : https://prove2.me/submissions/bfc9acd7-ce69-4cd4-9a71-5507c7117fdd

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false


/- Complete frozen module: BaselineEnergy.lean -/


open scoped BigOperators Polynomial

noncomputable section

namespace DerivativeChain

/-- Normalized Gauss--Lucas weights, indexed only by actual roots of `P`. -/
def rootProbability (P : ℂ[X]) (z : ℂ) (w : P.roots.toFinset) : ℝ :=
  P.derivRootWeight z w / ∑ v ∈ P.roots.toFinset, P.derivRootWeight z v

theorem rootProbability_nonneg (P : ℂ[X]) (z : ℂ) (w : P.roots.toFinset) :
    0 ≤ rootProbability P z w := by
  exact div_nonneg (P.derivRootWeight_nonneg z w)
    (Finset.sum_nonneg fun v _ => P.derivRootWeight_nonneg z v)

theorem sum_rootProbability {P : ℂ[X]} (hP : 0 < P.degree) (z : ℂ) :
    ∑ w : P.roots.toFinset, rootProbability P z w = 1 := by
  classical
  simp only [rootProbability, ← Finset.sum_div, Finset.sum_coe_sort]
  exact div_self (Polynomial.sum_derivRootWeight_pos hP z).ne'

theorem rootProbability_mean {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∑ w : P.roots.toFinset, rootProbability P z w • (w : ℂ) = z := by
  classical
  simp only [rootProbability, div_eq_inv_mul, mul_smul, ← Finset.smul_sum]
  rw [Finset.sum_coe_sort P.roots.toFinset
    (fun w : ℂ => P.derivRootWeight z w • w)]
  exact (Polynomial.eq_centerMass_of_eval_derivative_eq_zero hP hz).symm

theorem rootProbability_mean_re {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∑ w : P.roots.toFinset, rootProbability P z w * (w : ℂ).re = z.re := by
  have h := congrArg Complex.reAddGroupHom (rootProbability_mean hP hz)
  simpa only [map_sum, Complex.coe_reAddGroupHom, Complex.smul_re, smul_eq_mul] using h

theorem rootProbability_mean_im {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∑ w : P.roots.toFinset, rootProbability P z w * (w : ℂ).im = z.im := by
  have h := congrArg Complex.imAddGroupHom (rootProbability_mean hP hz)
  simpa only [map_sum, Complex.coe_imAddGroupHom, Complex.smul_im, smul_eq_mul] using h

theorem rootProbability_support {P : ℂ[X]} (hP : 0 < P.degree)
    (w : P.roots.toFinset) : P.eval (w : ℂ) = 0 := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  exact (Polynomial.mem_roots hP0).mp (Multiset.mem_toFinset.mp w.property)

/-- A finite probability transition from any critical point of a nonconstant
complex polynomial to roots of that polynomial, with conditional mean equal
to the critical point. Repeated roots and shared roots require no extra hypotheses. -/
theorem exists_root_transition {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) :
    ∃ π : P.roots.toFinset → ℝ,
      (∀ w, 0 ≤ π w) ∧
      (∑ w, π w = 1) ∧
      (∑ w, π w * (w : ℂ).re = z.re) ∧
      (∑ w, π w * (w : ℂ).im = z.im) ∧
      (∀ w : P.roots.toFinset, P.eval (w : ℂ) = 0) := by
  exact ⟨rootProbability P z, rootProbability_nonneg P z,
    sum_rootProbability hP z, rootProbability_mean_re hP hz,
    rootProbability_mean_im hP hz, rootProbability_support hP⟩

/-- The actual polynomial transition has zero expected centered increment,
 in the coordinate form used by the finite chain completion theorem. -/
theorem rootProbability_centered_increment {P : ℂ[X]} {z : ℂ}
    (hP : 0 < P.degree) (hz : P.derivative.eval z = 0) (u : ℂ) :
    (∑ w : P.roots.toFinset, rootProbability P z w *
      ((z - u).re * ((w : ℂ) - z).re +
        (z - u).im * ((w : ℂ) - z).im)) = 0 := by
  have hre : (∑ w : P.roots.toFinset,
      rootProbability P z w * ((w : ℂ) - z).re) = 0 := by
    simp only [Complex.sub_re, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, rootProbability_mean_re hP hz,
      sum_rootProbability hP z, one_mul, sub_self]
  have him : (∑ w : P.roots.toFinset,
      rootProbability P z w * ((w : ℂ) - z).im) = 0 := by
    simp only [Complex.sub_im, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, rootProbability_mean_im hP hz,
      sum_rootProbability hP z, one_mul, sub_self]
  calc
    _ = (z - u).re * (∑ w : P.roots.toFinset,
          rootProbability P z w * ((w : ℂ) - z).re) +
        (z - u).im * (∑ w : P.roots.toFinset,
          rootProbability P z w * ((w : ℂ) - z).im) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = 0 := by rw [hre, him]; ring

end DerivativeChain



open scoped BigOperators Polynomial

noncomputable section

namespace DerivativeChainPrivate

/-- A real-valued function with zero average under a finite probability distribution
has a nonpositive value. Zero weights and an initially possibly empty index type
are allowed; normalization supplies the required nonemptiness. -/
theorem exists_nonpos_of_probability_mean_zero {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hzero : ∑ i, p i * f i = 0) :
    ∃ i, f i ≤ 0 := by
  classical
  have hs : (Finset.univ : Finset ι).Nonempty := by
    exact Finset.nonempty_of_sum_ne_zero
      (show (∑ i, p i) ≠ 0 by rw [hsum]; exact one_ne_zero)
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image Finset.univ f hs
  have havg : f i ≤ ∑ j, p j * f j := by
    calc
      f i = ∑ j, p j * f i := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ j, p j * f j := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hmin j hj) (hp j)
  exact ⟨i, hzero ▸ havg⟩

/-- The squared-distance energy defect has zero expectation under the actual
root probability measure of a critical point. No disk restriction is used. -/
theorem rootProbability_energy_defect (P : ℂ[X]) (hP : 0 < P.degree)
    (z : ℂ) (hz : P.derivative.eval z = 0) :
    (∑ w : P.roots.toFinset, DerivativeChain.rootProbability P z w *
      (‖(w : ℂ) - z‖ ^ 2 - ‖(w : ℂ)‖ ^ 2 + ‖z‖ ^ 2)) = 0 := by
  have hnorm : ∀ a : ℂ, ‖a‖ ^ 2 = a.re * a.re + a.im * a.im := fun a =>
    (RCLike.normSq_eq_def' a).symm.trans (RCLike.normSq_apply a)
  have hdefect : ∀ a : ℂ,
      ‖a - z‖ ^ 2 - ‖a‖ ^ 2 + ‖z‖ ^ 2 =
        -2 * (z.re * (a - z).re + z.im * (a - z).im) := by
    intro a
    rw [hnorm (a - z), hnorm a, hnorm z, Complex.sub_re, Complex.sub_im]
    ring
  have hcenter : (∑ w : P.roots.toFinset, DerivativeChain.rootProbability P z w *
      (z.re * ((w : ℂ) - z).re + z.im * ((w : ℂ) - z).im)) = 0 := by
    simpa only [sub_zero] using DerivativeChain.rootProbability_centered_increment hP hz 0
  calc
    _ = -2 * (∑ w : P.roots.toFinset, DerivativeChain.rootProbability P z w *
        (z.re * ((w : ℂ) - z).re + z.im * ((w : ℂ) - z).im)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [hdefect]
      ring
    _ = 0 := by rw [hcenter, mul_zero]

/-- Every critical point of a nonconstant complex polynomial admits an actual
predecessor root whose squared step is bounded by the increase of squared norm.
This is the one-step inequality that telescopes along a derivative-root chain. -/
theorem exists_root_energy (P : Polynomial ℂ) (hP : 0 < P.degree)
    (z : ℂ) (hz : P.derivative.eval z = 0) :
    ∃ a : ℂ, P.eval a = 0 ∧ ‖a - z‖ ^ 2 ≤ ‖a‖ ^ 2 - ‖z‖ ^ 2 := by
  obtain ⟨w, hw⟩ := exists_nonpos_of_probability_mean_zero
    (DerivativeChain.rootProbability P z)
    (fun w : P.roots.toFinset => ‖(w : ℂ) - z‖ ^ 2 - ‖(w : ℂ)‖ ^ 2 + ‖z‖ ^ 2)
    (DerivativeChain.rootProbability_nonneg P z)
    (DerivativeChain.sum_rootProbability hP z)
    (rootProbability_energy_defect P hP z hz)
  refine ⟨w, DerivativeChain.rootProbability_support hP w, ?_⟩
  linarith

end DerivativeChainPrivate




/- Complete frozen module: FiniteWeightedVariance.lean -/
set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

theorem finite_weighted_variance {ι : Type} [Fintype ι]
    (w : ι → ℝ) (v : ι → ℂ) (z u : ℂ) (hs : ∑ i, w i=1)
    (hm : ∑ i, (w i:ℂ)*v i=z) :
    (∑ i, w i*‖v i-u‖^2)=‖z-u‖^2+(∑ i, w i*‖v i-z‖^2) := by
  have hr := congrArg Complex.re hm
  have hi := congrArg Complex.im hm
  simp only [Complex.re_sum,Complex.im_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero] at hr hi
  have hpoint (i : ι) : w i*‖v i-u‖^2 = w i*‖v i-z‖^2 +
      2*(z.re-u.re)*(w i*(v i).re)+2*(z.im-u.im)*(w i*(v i).im)+
      (‖u‖^2-‖z‖^2)*w i := by
    simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    ring
  simp only [hpoint,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,hs,hr,hi,mul_one]
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

theorem finite_weighted_square_bound {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    (∑ i, w i*f i)^2 ≤ ∑ i, w i*(f i)^2 := by
  have h1 (i : ι) : Real.sqrt (w i)*(Real.sqrt (w i)*f i)=w i*f i := by
    rw [← mul_assoc,← pow_two,Real.sq_sqrt (hw i)]
  have h2 (i : ι) : (Real.sqrt (w i)*f i)^2=w i*(f i)^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i)*f i)
  simpa only [h1,h2,Real.sq_sqrt (hw _),hs,one_mul] using hh

theorem finite_weighted_exists_le_mean {ι : Type} [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    ∃ i, f i ≤ ∑ j, w j*f j := by
  have he : (∑ i, w i*(f i-∑ j, w j*f j))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul,sub_self]
  obtain ⟨i,hi⟩ := DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero w _ hw hs he
  exact ⟨i,by linarith⟩

end DerivativeChainContinuation


/- Complete frozen module: RealInterlacing.lean -/
set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

noncomputable def realRootProduct {n : ℕ} (a : Fin n → ℝ) : Polynomial ℝ :=
  ∏ i, (X-C (a i))

theorem realRootProduct_monic {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).Monic := Polynomial.monic_prod_X_sub_C a Finset.univ

theorem realRootProduct_degree {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).natDegree = n := by
  unfold realRootProduct
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (a i))]
  simp

theorem realRootProduct_eval {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    (realRootProduct a).eval (a i) = 0 := by
  simp only [realRootProduct, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

theorem strict_real_derivative_interlacing (n : ℕ) (a : Fin (n+2) → ℝ)
    (ha : StrictMono a) :
    ∃ b : Fin (n+1) → ℝ, StrictMono b ∧
      (∀ i, a i.castSucc < b i ∧ b i < a i.succ) ∧
      (realRootProduct a).derivative = C (n+2 : ℝ) * realRootProduct b := by
  classical
  let p := realRootProduct a
  have hd : p.natDegree = n+2 := realRootProduct_degree a
  have hp : p.Monic := realRootProduct_monic a
  have hd' : p.derivative.natDegree = n+1 := by rw [natDegree_derivative, hd]; omega
  have hp' : p.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  have ex (i : Fin (n+1)) : ∃ b : ℝ, a i.castSucc < b ∧ b < a i.succ ∧ p.derivative.eval b=0 := by
    have hi : i.castSucc < i.succ := by exact Fin.castSucc_lt_succ
    obtain ⟨b,hb,hdb⟩ := exists_deriv_eq_zero (ha hi) p.continuousOn
      ((realRootProduct_eval a i.castSucc).trans (realRootProduct_eval a i.succ).symm)
    refine ⟨b,hb.1,hb.2,?_⟩
    simpa only [p.deriv] using hdb
  choose b hb using ex
  have hmono : StrictMono b := by
    intro i j hij
    have hle : i.succ ≤ j.castSucc := by simpa using hij
    exact (hb i).2.1.trans_le ((ha.monotone hle).trans (hb j).1.le)
  let s : Multiset ℝ := Finset.univ.val.map b
  have hnodup : s.Nodup := Finset.univ.nodup.map hmono.injective
  have hsub : s ≤ p.derivative.roots := by
    apply (Multiset.le_iff_subset hnodup).mpr
    intro x hx
    obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hp').mpr (hb i).2.2
  have hcard : s.card = n+1 := by simp [s]
  have hle := p.derivative.card_roots'
  have heq : s = p.derivative.roots :=
    Multiset.eq_of_le_of_card_le hsub (by simpa [hd',hcard] using hle)
  have hc : p.derivative.roots.card = p.derivative.natDegree := by rw [←heq,hcard,hd']
  have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  have hlead : p.derivative.leadingCoeff = (n+2 : ℝ) := by
    rw [leadingCoeff_derivative, hp.leadingCoeff, one_mul,hd]; push_cast; rfl
  refine ⟨b,hmono,(fun i => ⟨(hb i).1,(hb i).2.1⟩),?_⟩
  rw [hlead,←heq] at hprod
  have hbprod : (s.map fun x => (X-C x : Polynomial ℝ)).prod = realRootProduct b := by
    simp only [s,Multiset.map_map,Function.comp_def]
    rfl
  rw [hbprod] at hprod
  change p.derivative = C (n+2 : ℝ)*realRootProduct b
  exact hprod.symm

end DerivativeChainContinuation


/- Complete frozen module: RepeatedInterlacing.lean -/
set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial Filter Topology
open scoped BigOperators

theorem realRootProduct_eval_continuous (n : ℕ) (x : ℝ) :
    Continuous (fun a : Fin n → ℝ => (realRootProduct a).eval x) := by
  simp only [realRootProduct, eval_prod, eval_sub, eval_X, eval_C]
  fun_prop

theorem realRootProduct_derivative_eval_continuous (n : ℕ) (x : ℝ) :
    Continuous (fun a : Fin n → ℝ => (realRootProduct a).derivative.eval x) := by
  simp [realRootProduct, derivative_prod_finset, eval_finsetSum, eval_prod]
  fun_prop

theorem real_derivative_interlacing (n : ℕ) (a : Fin (n+2) → ℝ)
    (ha : Monotone a) :
    ∃ b : Fin (n+1) → ℝ, Monotone b ∧
      (∀ i, a i.castSucc ≤ b i ∧ b i ≤ a i.succ) ∧
      (realRootProduct a).derivative = C (n+2 : ℝ) * realRootProduct b := by
  classical
  let eps : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hep (k : ℕ) : 0 < eps k := by dsimp [eps]; positivity
  have he1 (k : ℕ) : eps k ≤ 1 := by dsimp [eps]; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have helim : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let aa : ℕ → Fin (n+2) → ℝ := fun k i => a i + eps k * (i.val : ℝ)
  have hstrict (k : ℕ) : StrictMono (aa k) := by
    intro i j hij
    have hc : (i.val : ℝ) < j.val := by exact_mod_cast hij
    have hh := mul_lt_mul_of_pos_left hc (hep k)
    have hm := ha hij.le
    dsimp [aa]; linarith
  have halim : Tendsto aa atTop (𝓝 a) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa [aa] using tendsto_const_nhds.add (helim.mul_const (i.val : ℝ))
  choose b hb using fun k => strict_real_derivative_interlacing n (aa k) (hstrict k)
  let lo : Fin (n+1) → ℝ := fun _ => a 0
  let hi : Fin (n+1) → ℝ := fun _ => a (Fin.last (n+1)) + (n+1 : ℝ)
  have hbox (k : ℕ) : b k ∈ Set.Icc lo hi := by
    constructor <;> intro i
    · have h := (hb k).2.1 i
      have hm := ha (show (0 : Fin (n+2)) ≤ i.castSucc by exact Fin.zero_le _)
      have he : 0 ≤ eps k * (i.val : ℝ) := by positivity
      dsimp [aa] at h
      dsimp [lo]; linarith [h.1]
    · have h := (hb k).2.1 i
      have hm := ha (show i.succ ≤ Fin.last (n+1) by exact Fin.le_last _)
      have hn : ((i.succ).val : ℝ) ≤ (n+1 : ℝ) := by exact_mod_cast (show i.succ.val ≤ n+1 by omega)
      have he := mul_le_mul_of_nonneg_right (he1 k) (show (0 : ℝ) ≤ i.succ.val by positivity)
      dsimp [aa] at h
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, one_mul] at hn he
      dsimp [hi]; push_cast at h; linarith [h.2]
  obtain ⟨w,_,phi,hphi,hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc lo hi)).tendsto_subseq hbox
  have ha' := halim.comp hphi.tendsto_atTop
  have hw (i : Fin (n+1)) : Tendsto (fun k => b (phi k) i) atTop (𝓝 (w i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hlim
  have ha'coord (i : Fin (n+2)) : Tendsto (fun k => aa (phi k) i) atTop (𝓝 (a i)) :=
    (continuous_apply i).continuousAt.tendsto.comp ha'
  refine ⟨w,?_,?_,?_⟩
  · intro i j hij
    exact le_of_tendsto_of_tendsto (hw i) (hw j)
      (Eventually.of_forall fun k => (hb (phi k)).1.monotone hij)
  · intro i
    exact ⟨le_of_tendsto_of_tendsto (ha'coord i.castSucc) (hw i)
      (Eventually.of_forall fun k => ((hb (phi k)).2.1 i).1.le),
      le_of_tendsto_of_tendsto (hw i) (ha'coord i.succ)
      (Eventually.of_forall fun k => ((hb (phi k)).2.1 i).2.le)⟩
  · apply Polynomial.funext
    intro x
    have hl := (realRootProduct_derivative_eval_continuous (n+2) x).continuousAt.tendsto.comp ha'
    have hr := ((realRootProduct_eval_continuous (n+1) x).continuousAt.tendsto.comp hlim).const_mul (n+2 : ℝ)
    have heq : (fun k => (realRootProduct (aa (phi k))).derivative.eval x) =
        (fun k => (n+2 : ℝ) * (realRootProduct (b (phi k))).eval x) := by
      funext k
      rw [(hb (phi k)).2.2, eval_mul, eval_C]
    simp only [Function.comp_def] at hl hr
    rw [heq] at hl
    simpa only [eval_mul, eval_C] using tendsto_nhds_unique hl hr

end DerivativeChainContinuation


/- Complete frozen module: RealTower.lean -/
set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

abbrev RealRows := (k : ℕ) → Fin (k+1) → ℝ

def RealRowStep (r : RealRows) (k : ℕ) : Prop :=
  (∀ i : Fin (k+1), r (k+1) i.castSucc ≤ r k i ∧ r k i ≤ r (k+1) i.succ) ∧
    (realRootProduct (r (k+1))).derivative = C (k+2 : ℝ)*realRootProduct (r k)

theorem real_tower_exists (n : ℕ) (a : Fin (n+1) → ℝ) (ha : Monotone a) :
    ∃ r : RealRows, r n=a ∧ (∀ k ≤ n, Monotone (r k)) ∧ (∀ k<n, RealRowStep r k) := by
  classical
  induction n with
  | zero =>
    let r : RealRows := fun _ _ => a 0
    refine ⟨r,?_,?_,?_⟩
    · funext i
      have hi : i=0 := Fin.eq_zero i
      simp [r,hi]
    · intro k hk i j hij
      rfl
    · intro k hk
      omega
  | succ n ih =>
    obtain ⟨b,hbmono,hbinter,hbderiv⟩ := real_derivative_interlacing n a ha
    obtain ⟨r,hrtop,hrmono,hrstep⟩ := ih b hbmono
    let rr : RealRows := Function.update r (n+1) a
    have hrr (k : ℕ) (hk : k ≤ n) : rr k = r k := by
      simp [rr,Function.update_of_ne (show k ≠ n+1 by omega)]
    have htop : rr (n+1) = a := by simp [rr]
    refine ⟨rr,htop,?_,?_⟩
    · intro k hk
      by_cases he : k=n+1
      · subst k
        rw [htop]
        exact ha
      · rw [hrr k (by omega)]
        exact hrmono k (by omega)
    · intro k hk
      by_cases he : k=n
      · subst k
        simp only [RealRowStep,htop,hrr n le_rfl,hrtop]
        exact ⟨hbinter,hbderiv⟩
      · simp only [RealRowStep,hrr k (by omega),hrr (k+1) (by omega)]
        exact hrstep k (by omega)

end DerivativeChainContinuation


/- Complete frozen module: LateRealRow.lean -/

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators

/-- Actual derivative-root extension, with the disk center included in the energy. -/
theorem exists_root_centered_energy (P : Polynomial ℂ) (hP : 0 < P.degree)
    (z c : ℂ) (hz : P.derivative.eval z = 0) :
    ∃ v : ℂ, P.eval v = 0 ∧ ‖v-z‖^2 ≤ ‖v-c‖^2-‖z-c‖^2 := by
  classical
  let w : P.roots.toFinset → ℝ := DerivativeChain.rootProbability P z
  have hs : ∑ i, w i = 1 := DerivativeChain.sum_rootProbability hP z
  have hm : ∑ i, (w i : ℂ)*(i : ℂ) = z := by
    simpa only [Complex.real_smul] using DerivativeChain.rootProbability_mean hP hz
  have hv := finite_weighted_variance w (fun i => (i : ℂ)) z c hs hm
  have he : (∑ i, w i*(‖(i : ℂ)-z‖^2-‖(i : ℂ)-c‖^2+‖z-c‖^2)) = 0 := by
    simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      ← Finset.sum_mul,hs,one_mul]
    linarith
  obtain ⟨i,hi⟩ := DerivativeChainPrivate.exists_nonpos_of_probability_mean_zero w _
    (DerivativeChain.rootProbability_nonneg P z) hs he
  exact ⟨i,DerivativeChain.rootProbability_support hP i,by linarith⟩

theorem finite_tail_centered_energy (P : ℕ → Polynomial ℂ) (h : ℕ)
    (hdegree : ∀ j < h, 0 < (P (j+1)).degree)
    (hstep : ∀ j < h, ∀ w : ℂ, (P j).eval w=0 → (P (j+1)).derivative.eval w=0)
    (b c : ℂ) (hb : (P 0).eval b=0) :
    ∃ z : ℕ → ℂ, z 0=b ∧ (∀ j ≤ h, (P j).eval (z j)=0) ∧
      (∑ j ∈ Finset.range h, ‖z (j+1)-z j‖^2) ≤ ‖z h-c‖^2-‖b-c‖^2 := by
  classical
  let next (j : ℕ) (w : ℂ) := Classical.epsilon (fun v : ℂ =>
    (P (j+1)).eval v=0 ∧ ‖v-w‖^2 ≤ ‖v-c‖^2-‖w-c‖^2)
  have hn (j : ℕ) (hj : j < h) (w : ℂ) (hw : (P j).eval w=0) :
      (P (j+1)).eval (next j w)=0 ∧
        ‖next j w-w‖^2 ≤ ‖next j w-c‖^2-‖w-c‖^2 := by
    dsimp only [next]
    apply Classical.epsilon_spec (p := fun v : ℂ =>
      (P (j+1)).eval v=0 ∧ ‖v-w‖^2 ≤ ‖v-c‖^2-‖w-c‖^2)
    exact exists_root_centered_energy (P (j+1)) (hdegree j hj) w c (hstep j hj w hw)
  let z : ℕ → ℂ := Nat.rec b (fun j w => next j w)
  have hz0 : z 0=b := rfl
  have hzs (j : ℕ) : z (j+1)=next j (z j) := rfl
  have hzroot (j : ℕ) (hj : j ≤ h) : (P j).eval (z j)=0 := by
    induction j with
    | zero => exact hb
    | succ j ih =>
      rw [hzs]
      exact (hn j (by omega) (z j) (ih (by omega))).1
  refine ⟨z,hz0,hzroot,?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.range h, (‖z (j+1)-c‖^2-‖z j-c‖^2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simpa only [hzs] using (hn j hj' (z j) (hzroot j (by omega))).2
    _ = _ := by rw [Finset.sum_range_sub (fun j => ‖z j-c‖^2),hz0]

/-- The monic complex polynomial with the supplied real roots. -/
noncomputable def complexRealRow {n : ℕ} (a : Fin n → ℝ) : Polynomial ℂ :=
  (realRootProduct a).map Complex.ofRealHom

theorem complexRealRow_eval {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    (complexRealRow a).eval (a i : ℂ) = 0 := by
  classical
  simp only [complexRealRow,realRootProduct,Polynomial.map_prod,Polynomial.map_sub,
    Polynomial.map_X,Polynomial.map_C,Polynomial.eval_prod,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

theorem complexRealRow_step (r : RealRows) (j : ℕ) (hs : RealRowStep r j) :
    (complexRealRow (r (j+1))).derivative = C (j+2 : ℂ)*complexRealRow (r j) := by
  simp only [complexRealRow,Polynomial.derivative_map,hs.2,Polynomial.map_mul,
    Polynomial.map_C]
  norm_cast

/-- Both extremal Rolle branches are geodesics; choose the one pointing away
from the projection of the disk center. This constructs the entire prefix. -/
theorem real_outward_prefix (r : RealRows) (M : ℕ)
    (hstep : ∀ j < M, RealRowStep r j) (c : ℂ) :
    ∃ f : ℕ → ℂ, f 0 = (r 0 0 : ℂ) ∧
      (∀ j ≤ M, (complexRealRow (r j)).eval (f j)=0) ∧
      (∑ j ∈ Finset.range M, ‖f (j+1)-f j‖)^2 ≤
        ‖f M-c‖^2-‖f 0-c‖^2 := by
  classical
  by_cases hc : c.re ≤ r 0 0
  · let x : ℕ → ℝ := fun j => r j (Fin.last j)
    have hx0 : x 0 = r 0 0 := rfl
    have hx (j : ℕ) (hj : j<M) : x j ≤ x (j+1) := by
      exact (hstep j hj).1 (Fin.last j) |>.2
    have hnorm (j : ℕ) (hj : j<M) :
        ‖(x (j+1) : ℂ)-(x j : ℂ)‖ = x (j+1)-x j := by
      rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hx j hj))]
    have hcost : (∑ j ∈ Finset.range M, ‖(x (j+1) : ℂ)-(x j : ℂ)‖) = x M-x 0 := by
      calc
        _ = ∑ j ∈ Finset.range M, (x (j+1)-x j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hnorm j (Finset.mem_range.mp hj)
        _ = _ := Finset.sum_range_sub x M
    have hpos : 0 ≤ x M-x 0 := by
      rw [← hcost]
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    refine ⟨fun j => (x j : ℂ),by simp [hx0],?_,?_⟩
    · intro j _
      exact complexRealRow_eval (r j) (Fin.last j)
    · rw [hcost]
      simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,
        Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im]
      have hmul : 0 ≤ (x M-x 0)*(x 0-c.re) := mul_nonneg hpos (by simpa [hx0] using hc)
      nlinarith
  · let x : ℕ → ℝ := fun j => r j 0
    have hx (j : ℕ) (hj : j<M) : x (j+1) ≤ x j := by
      exact (hstep j hj).1 0 |>.1
    have hnorm (j : ℕ) (hj : j<M) :
        ‖(x (j+1) : ℂ)-(x j : ℂ)‖ = x j-x (j+1) := by
      rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (hx j hj))]
      ring
    have hcost : (∑ j ∈ Finset.range M, ‖(x (j+1) : ℂ)-(x j : ℂ)‖) = x 0-x M := by
      calc
        _ = ∑ j ∈ Finset.range M, ((-x) (j+1)-(-x) j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hnorm j (Finset.mem_range.mp hj)]
          simp only [Pi.neg_apply]
          ring
        _ = _ := by rw [Finset.sum_range_sub]; simp only [Pi.neg_apply]; ring
    have hpos : 0 ≤ x 0-x M := by
      rw [← hcost]
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    refine ⟨fun j => (x j : ℂ),rfl,?_,?_⟩
    · intro j _
      exact complexRealRow_eval (r j) 0
    · rw [hcost]
      simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,
        Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im]
      have hmul : 0 ≤ (x 0-x M)*(c.re-x 0) := mul_nonneg hpos (by dsimp [x]; linarith)
      nlinarith

/-- The real derivative tower agrees with every lower row of the actual
normalized complex polynomial tower. -/
theorem real_row_identification (P : ℕ → Polynomial ℂ) (M : ℕ)
    (hrec : ∀ j < M, (P (j+1)).derivative = C (j+2 : ℂ)*P j)
    (r : RealRows) (hstep : ∀ j < M, RealRowStep r j)
    (htop : P M = complexRealRow (r M)) :
    ∀ j ≤ M, P j = complexRealRow (r j) := by
  intro j hj
  apply Nat.decreasingInduction (motive := fun j _ => P j = complexRealRow (r j)) ?_ htop hj
  intro k hk he
  have hd := congrArg Polynomial.derivative he
  rw [hrec k hk,complexRealRow_step r k (hstep k hk)] at hd
  apply mul_left_cancel₀ _ hd
  rw [Polynomial.C_ne_zero]
  exact_mod_cast (show (k+2 : ℕ) ≠ 0 by omega)

/-- Compress one entire geodesic prefix to one Cauchy--Schwarz entry. -/
theorem late_row_compressed_cauchy (h : ℕ) (r : ℝ) (l : ℕ → ℝ) :
    (r+∑ j ∈ Finset.range h, l j)^2 ≤
      (h+1 : ℝ)*(r^2+∑ j ∈ Finset.range h, (l j)^2) := by
  let f : Fin (h+1) → ℝ := Fin.cases r (fun j => l j)
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (h+1) => (1:ℝ)) f
  have he : (∑ j : Fin h, (l j)^2) = ∑ j ∈ Finset.range h, (l j)^2 :=
    Fin.sum_univ_eq_sum_range (fun j => (l j)^2) h
  simpa [f,Fin.sum_univ_succ,Fin.sum_univ_eq_sum_range,he] using hh

/-- A late real-rooted row yields a complete chain for the actual polynomial
tower. The row indices are degrees minus one: source degree is M+K+1,
the real row degree is M+1, and K is the number of remaining parent steps.
No short prefix is supplied; repeated Rolle constructs it in the proof. -/
theorem late_real_row_chain (P : ℕ → Polynomial ℂ) (M K : ℕ)
    (hrec : ∀ j < M+K, (P (j+1)).derivative = C (j+2 : ℂ)*P j)
    (hdegree : ∀ j < M+K, 0 < (P (j+1)).degree)
    (u c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hu : (P 0).eval u=0)
    (hsource : ∀ w : ℂ, (P (M+K)).eval w=0 → ‖w-c‖ ≤ R)
    (a : Fin (M+1) → ℝ) (ha : Monotone a) (hcore : P M=complexRealRow a) :
    ∃ z : ℕ → ℂ, z 0=u ∧ (∀ j ≤ M+K, (P j).eval (z j)=0) ∧
      (∑ j ∈ Finset.range (M+K), ‖z (j+1)-z j‖)^2 ≤
        (K+1 : ℝ)*(R^2-‖u-c‖^2) := by
  classical
  obtain ⟨r,hrtop,hrmono,hrstep⟩ := real_tower_exists M a ha
  have hmatch : ∀ j ≤ M, P j=complexRealRow (r j) := by
    apply real_row_identification P M (fun j hj => hrec j (by omega)) r hrstep
    rw [hrtop]
    exact hcore
  have hu' : u = (r 0 0 : ℂ) := by
    rw [hmatch 0 (by omega)] at hu
    have he : u-(r 0 0 : ℂ)=0 := by simpa [complexRealRow,realRootProduct] using hu
    exact sub_eq_zero.mp he
  obtain ⟨f,hf0,hfroot,hfenergy⟩ := real_outward_prefix r M hrstep c
  have hf0' : f 0=u := hf0.trans hu'.symm
  have hfactual (j : ℕ) (hj : j≤M) : (P j).eval (f j)=0 := by
    rw [hmatch j hj]
    exact hfroot j hj
  obtain ⟨t,ht0,htroot,htenergy⟩ := finite_tail_centered_energy
    (fun j => P (M+j)) K
    (fun j hj => by simpa [Nat.add_assoc] using hdegree (M+j) (by omega))
    (fun j hj w hw => by
      rw [show M+(j+1)=M+j+1 by omega,hrec (M+j) (by omega)]
      simp [hw]) (f M) c (by simpa using hfactual M le_rfl)
  let z : ℕ → ℂ := fun j => if j≤M then f j else t (j-M)
  have hzprefix (j : ℕ) (hj : j≤M) : z j=f j := by simp [z,hj]
  have hztail (j : ℕ) : z (M+j)=t j := by
    by_cases hj : j=0
    · subst j
      simp [z,ht0]
    · simp [z,show ¬M+j≤M by omega]
  have hz0 : z 0=u := (hzprefix 0 (by omega)).trans hf0'
  have hzroots (j : ℕ) (hj : j≤M+K) : (P j).eval (z j)=0 := by
    by_cases hjM : j≤M
    · rw [hzprefix j hjM]
      exact hfactual j hjM
    · have he : M+(j-M)=j := by omega
      rw [← he,hztail]
      exact htroot (j-M) (by omega)
  have hcost : (∑ j ∈ Finset.range (M+K), ‖z (j+1)-z j‖) =
      (∑ j ∈ Finset.range M, ‖f (j+1)-f j‖) +
      (∑ j ∈ Finset.range K, ‖t (j+1)-t j‖) := by
    rw [Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [hzprefix j (by omega),hzprefix (j+1) (by omega)]
    · apply Finset.sum_congr rfl
      intro j _
      rw [show M+j+1=M+(j+1) by omega,hztail,hztail]
  have hlast : ‖t K-c‖ ≤ R := hsource (t K) (htroot K le_rfl)
  have henergy : (∑ j ∈ Finset.range M, ‖f (j+1)-f j‖)^2 +
      (∑ j ∈ Finset.range K, ‖t (j+1)-t j‖^2) ≤ R^2-‖u-c‖^2 := by
    rw [hf0'] at hfenergy
    have hlastsq : ‖t K-c‖^2 ≤ R^2 := by nlinarith [norm_nonneg (t K-c)]
    linarith
  refine ⟨z,hz0,hzroots,?_⟩
  rw [hcost]
  exact (late_row_compressed_cauchy K _ _).trans
    (mul_le_mul_of_nonneg_left henergy (by positivity))

/-- In particular, a real-rooted row reached after at most fifteen derivatives
gives the full four-radius bound, in arbitrary source degree. -/
theorem late_real_row_four_radius (P : ℕ → Polynomial ℂ) (M K : ℕ) (hK : K≤15)
    (hrec : ∀ j < M+K, (P (j+1)).derivative = C (j+2 : ℂ)*P j)
    (hdegree : ∀ j < M+K, 0 < (P (j+1)).degree)
    (u c : ℂ) (R : ℝ) (hR : 0 ≤ R) (hu : (P 0).eval u=0)
    (hsource : ∀ w : ℂ, (P (M+K)).eval w=0 → ‖w-c‖ ≤ R)
    (a : Fin (M+1) → ℝ) (ha : Monotone a) (hcore : P M=complexRealRow a) :
    ∃ z : ℕ → ℂ, z 0=u ∧ (∀ j ≤ M+K, (P j).eval (z j)=0) ∧
      (∑ j ∈ Finset.range (M+K), ‖z (j+1)-z j‖) ≤ 4*R := by
  obtain ⟨z,hz0,hzroot,hz⟩ := late_real_row_chain P M K hrec hdegree u c R hR hu hsource a ha hcore
  refine ⟨z,hz0,hzroot,?_⟩
  have hK' : (K+1 : ℝ) ≤ 16 := by exact_mod_cast (show K+1≤16 by omega)
  have he : (∑ j ∈ Finset.range (M+K), ‖z (j+1)-z j‖)^2 ≤ 16*R^2 := calc
    _ ≤ (K+1 : ℝ)*(R^2-‖u-c‖^2) := hz
    _ ≤ (K+1 : ℝ)*R^2 := mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (by positivity)
    _ ≤ 16*R^2 := mul_le_mul_of_nonneg_right hK' (sq_nonneg R)
  nlinarith

end DerivativeChainContinuation


/- Complete frozen module: LateRealRowActual.lean -/

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

/-- A pathwise joining lemma. The complete theorem below constructs the
prefix from the actual real-rooted derivative row. -/
theorem complete_outward_prefix (P : ℕ → Polynomial ℂ) (M K : ℕ)
    (hdegree : ∀ j < M+K, 0 < (P (j+1)).degree)
    (hstep : ∀ j < M+K, ∀ w : ℂ, (P j).eval w=0 → (P (j+1)).derivative.eval w=0)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hsource : ∀ w : ℂ, (P (M+K)).eval w=0 → ‖w-c‖≤R)
    (f : ℕ → ℂ) (hfroot : ∀ j≤M, (P j).eval (f j)=0)
    (hfenergy : (∑ j ∈ Finset.range M, ‖f (j+1)-f j‖)^2 ≤
      ‖f M-c‖^2-‖f 0-c‖^2) :
    ∃ z : ℕ → ℂ, z 0=f 0 ∧ (∀ j≤M+K, (P j).eval (z j)=0) ∧
      (∑ j ∈ Finset.range (M+K), ‖z (j+1)-z j‖)^2 ≤
        (K+1 : ℝ)*(R^2-‖f 0-c‖^2) := by
  classical
  obtain ⟨t,ht0,htroot,htenergy⟩ := finite_tail_centered_energy
    (fun j => P (M+j)) K
    (fun j hj => by simpa [Nat.add_assoc] using hdegree (M+j) (by omega))
    (fun j hj w hw => by
      simpa [Nat.add_assoc] using hstep (M+j) (by omega) w hw)
    (f M) c (by simpa using hfroot M le_rfl)
  let z : ℕ → ℂ := fun j => if j≤M then f j else t (j-M)
  have hzprefix (j : ℕ) (hj : j≤M) : z j=f j := by simp [z,hj]
  have hztail (j : ℕ) : z (M+j)=t j := by
    by_cases hj : j=0
    · subst j
      simp [z,ht0]
    · simp [z,show ¬M+j≤M by omega]
  have hzroots (j : ℕ) (hj : j≤M+K) : (P j).eval (z j)=0 := by
    by_cases hjM : j≤M
    · rw [hzprefix j hjM]
      exact hfroot j hjM
    · have he : M+(j-M)=j := by omega
      rw [← he,hztail]
      exact htroot (j-M) (by omega)
  have hcost : (∑ j ∈ Finset.range (M+K), ‖z (j+1)-z j‖) =
      (∑ j ∈ Finset.range M, ‖f (j+1)-f j‖) +
      (∑ j ∈ Finset.range K, ‖t (j+1)-t j‖) := by
    rw [Finset.sum_range_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [hzprefix j (by omega),hzprefix (j+1) (by omega)]
    · apply Finset.sum_congr rfl
      intro j _
      rw [show M+j+1=M+(j+1) by omega,hztail,hztail]
  have hlast : ‖t K-c‖ ≤ R := hsource (t K) (htroot K le_rfl)
  have henergy : (∑ j ∈ Finset.range M, ‖f (j+1)-f j‖)^2 +
      (∑ j ∈ Finset.range K, ‖t (j+1)-t j‖^2) ≤ R^2-‖f 0-c‖^2 := by
    have hlastsq : ‖t K-c‖^2 ≤ R^2 := by nlinarith [norm_nonneg (t K-c)]
    linarith
  refine ⟨z,hzprefix 0 (by omega),hzroots,?_⟩
  rw [hcost]
  exact (late_row_compressed_cauchy K _ _).trans
    (mul_le_mul_of_nonneg_left henergy (by positivity))

theorem actual_fromRoots_natDegree {n : ℕ} (a : Fin n → ℂ) :
    (fromRoots a).natDegree=n := by
  classical
  simp [fromRoots,Polynomial.natDegree_prod_of_monic,Polynomial.monic_X_sub_C]

theorem actual_iterate_derivative_natDegree (p : Polynomial ℂ) (k : ℕ) :
    (Polynomial.derivative^[k] p).natDegree=p.natDegree-k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',Polynomial.natDegree_derivative,ih]
    omega

theorem actual_row_natDegree {n : ℕ} (a : Fin n → ℂ) (m : ℕ) (hm : m≤n) :
    (row a m).natDegree=m := by
  rw [row,actual_iterate_derivative_natDegree,actual_fromRoots_natDegree]
  omega

theorem actual_row_derivative {n : ℕ} (a : Fin n → ℂ) (m : ℕ) (hm : m<n) :
    (row a (m+1)).derivative=row a m := by
  unfold row
  rw [show n-m=n-(m+1)+1 by omega,Function.iterate_succ_apply']

/-- Nonzero scalar multiples suffice: ordinary derivative rows need not be
monic. Their real Rolle tower is still uniquely identified below the core. -/
theorem actual_real_row_identification {n : ℕ} (a : Fin n → ℂ) (M : ℕ)
    (hM : M+1≤n) (r : RealRows) (hrstep : ∀ j<M, RealRowStep r j)
    (s : ℂ) (hs : s≠0) (hcore : row a (M+1)=C s*complexRealRow (r M)) :
    ∀ j≤M, ∃ t : ℂ, t≠0 ∧ row a (j+1)=C t*complexRealRow (r j) := by
  intro j hj
  apply Nat.decreasingInduction
    (motive := fun j _ => ∃ t : ℂ, t≠0 ∧ row a (j+1)=C t*complexRealRow (r j))
    ?_ ⟨s,hs,hcore⟩ hj
  intro k hk he
  obtain ⟨t,ht,he⟩ := he
  have hd := congrArg Polynomial.derivative he
  rw [actual_row_derivative a (k+1) (by omega),Polynomial.derivative_C_mul,
    complexRealRow_step r k (hrstep k hk)] at hd
  refine ⟨t*(k+2),mul_ne_zero ht ?_,?_⟩
  · exact_mod_cast (show (k+2 : ℕ)≠0 by omega)
  · simpa only [← mul_assoc,← C_mul] using hd

/-- Main exact source-root-list theorem. It uses the project's original
ordinary-derivative `row`, `IsChain`, and `chainCost` definitions. An actual
degree-(M+1) derivative row is real-rooted, up to a nonzero scalar; the proof
constructs the whole chain, with no supplied prefix or turning budget. -/
theorem actual_late_real_row_chain {n : ℕ} (a : Fin n → ℂ) (M K : ℕ)
    (hn : n=M+K+1) (c : ℂ) (R : ℝ) (hR : 0≤R)
    (ha : ∀ i, ‖a i-c‖≤R) (b : Fin (M+1) → ℝ) (hb : Monotone b)
    (s : ℂ) (hs : s≠0) (hcore : row a (M+1)=C s*complexRealRow b) :
    ∃ z : Fin n → ℂ, IsChain a z ∧
      (chainCost z)^2 ≤ (K+1 : ℝ)*(R^2-‖z ⟨0,by omega⟩-c‖^2) := by
  classical
  subst n
  obtain ⟨r,hrtop,hrmono,hrstep⟩ := real_tower_exists M b hb
  have hmatch := actual_real_row_identification a M (by omega) r hrstep s hs
    (by simpa [hrtop] using hcore)
  obtain ⟨f,hf0,hfroot,hfenergy⟩ := real_outward_prefix r M hrstep c
  have hfactual (j : ℕ) (hj : j≤M) : (row a (j+1)).eval (f j)=0 := by
    obtain ⟨t,ht,he⟩ := hmatch j hj
    rw [he,Polynomial.eval_mul,hfroot j hj,mul_zero]
  obtain ⟨z,hz0,hzroot,hzenergy⟩ := complete_outward_prefix
    (fun j => row a (j+1)) M K
    (fun j hj => by
      apply Polynomial.natDegree_pos_iff_degree_pos.mp
      rw [actual_row_natDegree a (j+1+1) (by omega)]
      omega)
    (fun j hj w hw => by
      rw [actual_row_derivative a (j+1) (by omega)]
      exact hw) c R hR
    (fun w hw => by
      simp only [row,Nat.sub_self,Function.iterate_zero_apply,fromRoots,Polynomial.eval_prod,
        Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at hw
      obtain ⟨i,hi,hwi⟩ := Finset.prod_eq_zero_iff.mp hw
      rw [sub_eq_zero.mp hwi]
      exact ha i) f hfactual hfenergy
  refine ⟨fun i => z i.val,?_,?_⟩
  · intro i
    exact hzroot i.val (by omega)
  · have hcost : chainCost (fun i : Fin (M+K+1) => z i.val) =
        ∑ j ∈ Finset.range (M+K), ‖z (j+1)-z j‖ := by
      simp only [chainCost]
      exact Fin.sum_univ_eq_sum_range (fun j => ‖z (j+1)-z j‖) (M+K)
    rw [hcost]
    dsimp only
    rw [hz0]
    exact hzenergy

/-- Four radii in every source degree, provided some row reached within
fifteen derivatives is real-rooted. -/
theorem exists_chain_cost_le_four_of_late_real_row {n : ℕ} (a : Fin n → ℂ)
    (M K : ℕ) (hn : n=M+K+1) (hK : K≤15) (c : ℂ) (R : ℝ) (hR : 0≤R)
    (ha : ∀ i, ‖a i-c‖≤R) (b : Fin (M+1) → ℝ) (hb : Monotone b)
    (s : ℂ) (hs : s≠0) (hcore : row a (M+1)=C s*complexRealRow b) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z≤4*R := by
  obtain ⟨z,hzchain,hz⟩ := actual_late_real_row_chain a M K hn c R hR ha b hb s hs hcore
  refine ⟨z,hzchain,?_⟩
  have hK' : (K+1 : ℝ)≤16 := by exact_mod_cast (show K+1≤16 by omega)
  have he : (chainCost z)^2≤16*R^2 := calc
    _ ≤ (K+1 : ℝ)*(R^2-‖z ⟨0,by omega⟩-c‖^2) := hz
    _ ≤ (K+1 : ℝ)*R^2 := mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _)) (by positivity)
    _ ≤ 16*R^2 := mul_le_mul_of_nonneg_right hK' (sq_nonneg R)
  nlinarith

end DerivativeChainContinuation


open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem solution {n : ℕ} (a : Fin n → ℂ)
    (M K : ℕ) (hn : n=M+K+1) (hK : K≤15) (c : ℂ) (R : ℝ) (hR : 0≤R)
    (ha : ∀ i, ‖a i-c‖≤R) (b : Fin (M+1) → ℝ) (hb : Monotone b)
    (s : ℂ) (hs : s≠0)
    (hcore : row a (M+1)=C s*∏ i, (X-C (b i : ℂ))) :
    ∃ z : Fin n → ℂ, IsChain a z ∧ chainCost z≤4*R := by
  have he : DerivativeChainContinuation.complexRealRow b =
      ∏ i, (X-C (b i : ℂ)) := by
    simp [DerivativeChainContinuation.complexRealRow,
      DerivativeChainContinuation.realRootProduct,Polynomial.map_prod]
  have hcore' : row a (M+1)=C s*DerivativeChainContinuation.complexRealRow b := by
    rw [he]
    exact hcore
  exact DerivativeChainContinuation.exists_chain_cost_le_four_of_late_real_row
    a M K hn hK c R hR ha b hb s hs hcore'
