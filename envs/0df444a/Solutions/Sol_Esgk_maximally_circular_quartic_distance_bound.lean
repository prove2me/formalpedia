-- Prove2me | solution 1 for Esgk.maximally_circular_quartic_distance_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-16T06:19:53.616804+00:00
-- url     : https://prove2.me/submissions/6d172033-7c10-4889-852f-5e26e59f9086

import Theorems.Thm_Esgk_maximally_circular_raw_auxiliary_incidence_bound
import Definitions.Def_Esgk_BivariateCornerNormalForm
import Definitions.Def_Esgk_CircularTangentIsotropicFaces
import Definitions.Def_Esgk_DistanceNewtonPersistentTangentRoots
import Definitions.Def_Esgk_MaximallyCircularDegreeTwoCircle
import Definitions.Def_Esgk_MaximallyCircularIsotropicBidegree
import Definitions.Def_Esgk_MaximallyCircularQuarticFromIncidence
import Definitions.Def_Esgk_PlaneAffineLinePolynomial
import Definitions.Def_Esgk_PlaneIsotropicCoordinates
import Definitions.Def_Esgk_PlaneProjectiveAffineChart
import Definitions.Def_LeanFormalizations_PachDeZeeuw_ChartBridge
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CurveSymmetries
import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Order.IntermediateValue
 

 












section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk


theorem finiteIncidenceCount_eq_card_filter_product {α β : Type*}
    (P : Finset α) (C : Finset β) (R : α → β → Prop) :
    finiteIncidenceCount P C R =
      ((P.product C).filter (fun xb : α × β ↦ R xb.1 xb.2)).card := by
  classical
  simp only [finiteIncidenceCount, Finset.card_filter]
  exact (Finset.sum_product_right P C (fun xb : α × β ↦
    if R xb.1 xb.2 then (1 : ℕ) else 0)).symm










end Esgk
end

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna.
-/


namespace Esgk


theorem fourthRootPartitionWindow
    (d N : ℝ) (hd2 : 2 ≤ d) (hN : 0 < N)
    (hthreshold : (24 : ℝ) ^ 3 * d ^ 5 ≤ N ^ 2) :
    ∃ ell : ℕ,
      24 * d ≤ (N / d) ^ ((2 : ℝ) / 3) ∧
      24 * d ≤ (ell : ℝ) ∧
      (N / d) ^ ((2 : ℝ) / 3) ≤ (ell : ℝ) ∧
      (ell : ℝ) ≤ 2 * (N / d) ^ ((2 : ℝ) / 3) := by
  have hd : 0 < d := by linarith
  let x : ℝ := N / d
  let L : ℝ := x ^ ((2 : ℝ) / 3)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hbase : (24 : ℝ) ^ 3 * d ^ 3 ≤ x ^ 2 := by
    dsimp [x]
    calc
      (24 : ℝ) ^ 3 * d ^ 3 = ((24 : ℝ) ^ 3 * d ^ 5) / d ^ 2 := by
        field_simp [ne_of_gt hd]
      _ ≤ N ^ 2 / d ^ 2 := by
        gcongr
      _ = (N / d) ^ 2 := by field_simp [ne_of_gt hd]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (24 : ℝ) ^ 3 * d ^ 3)
    hbase (by norm_num : 0 ≤ (1 / 3 : ℝ))
  have hleft : ((24 : ℝ) ^ 3 * d ^ 3) ^ ((1 : ℝ) / 3) = 24 * d := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast (24 : ℝ) 3, ← Real.rpow_mul (by positivity)]
    rw [← Real.rpow_natCast d 3, ← Real.rpow_mul (by positivity)]
    norm_num
  have hright : ((N / d) ^ 2) ^ ((1 : ℝ) / 3) = L := by
    dsimp [L]
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul (le_of_lt hx)]
    norm_num [x]
  have hL : 24 * d ≤ L := by
    dsimp [L] at hright ⊢
    rw [← hleft, ← hright]
    exact hp
  have hLpos : 0 < L := by
    dsimp [L]
    positivity
  let ell : ℕ := ⌈L⌉₊
  have hceil : L ≤ (ell : ℝ) := by
    dsimp [ell]
    exact Nat.le_ceil L
  have hceilUpper : (ell : ℝ) < L + 1 := by
    dsimp [ell]
    exact Nat.ceil_lt_add_one hLpos.le
  have hLbig : 1 ≤ L := by nlinarith [hL, hd2]
  have hupper : (ell : ℝ) ≤ 2 * L := by nlinarith [hceilUpper, hLbig]
  refine ⟨ell, hL, ?_, ?_, ?_⟩
  · exact hL.trans hceil
  · simpa [L, x] using hceil
  · simpa [L] using hupper

end Esgk

namespace Esgk


theorem fourthRootPartitionBounds
    (d N L : ℝ) (ell : ℕ)
    (hd2 : 2 ≤ d) (hN : 0 < N) (hL : 24 * d ≤ L)
    (hLcube : d ^ 2 * L ^ 3 = N ^ 2)
    (hEllL : L ≤ (ell : ℝ)) (hEllU : (ell : ℝ) ≤ 2 * L) :
    d * N ^ 3 / Real.sqrt (ell : ℝ) ≤ d ^ 2 * L * N ^ 2 ∧
    d ^ 2 * (ell : ℝ) * N ^ 2 ≤ 2 * (d ^ 2 * L * N ^ 2) ∧
    N ^ 2 ≤ d ^ 2 * L * N ^ 2 ∧
    d ^ 4 * (ell : ℝ) ^ 2 ≤ 4 * (d ^ 2 * L * N ^ 2) ∧
    d ^ 3 * N ^ 2 ≤ d ^ 2 * L * N ^ 2 := by
  have hd : 0 < d := by linarith
  have hLpos : 0 < L := by nlinarith [hL, hd]
  have hLone : 1 ≤ L := by nlinarith [hL, hd2]
  have hLnonneg : 0 ≤ L := hLpos.le
  have hdleL : d ≤ L := by nlinarith [hL, hd2]
  have hNrepr : N = d * L * Real.sqrt L := by
    have hsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    have hsqrtSq : (Real.sqrt L) ^ 2 = L := by
      simpa using Real.sq_sqrt hLnonneg
    have hsq : (d * L * Real.sqrt L) ^ 2 = N ^ 2 := by
      rw [show (d * L * Real.sqrt L) ^ 2 = d ^ 2 * L ^ 3 by
        rw [mul_pow, mul_pow, hsqrtSq]
        ring]
      exact hLcube
    exact (sq_eq_sq₀ hN.le (by positivity)).mp hsq.symm
  have hellpos : 0 < (ell : ℝ) := lt_of_lt_of_le (by nlinarith [hL, hd2]) hEllL
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hsqrtEll : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.2 hellpos
  have hsqrtLE : Real.sqrt L ≤ Real.sqrt (ell : ℝ) := by
    gcongr
  have hnum : d * N ^ 3 = (d ^ 2 * L * N ^ 2) * Real.sqrt L := by
    calc
      d * N ^ 3 = d * N ^ 2 * N := by ring
      _ = d * N ^ 2 * (d * L * Real.sqrt L) :=
        congrArg (fun n : ℝ ↦ d * N ^ 2 * n) hNrepr
      _ = (d ^ 2 * L * N ^ 2) * Real.sqrt L := by ring
  have hfirst : d * N ^ 3 / Real.sqrt (ell : ℝ) ≤ d ^ 2 * L * N ^ 2 := by
    apply (div_le_iff₀ hsqrtEll).2
    rw [hnum]
    exact mul_le_mul_of_nonneg_left hsqrtLE (by positivity)
  have hsecond : d ^ 2 * (ell : ℝ) * N ^ 2 ≤
      2 * (d ^ 2 * L * N ^ 2) := by
    have hnon : 0 ≤ d ^ 2 * N ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hEllU hnon]
  have hthird : N ^ 2 ≤ d ^ 2 * L * N ^ 2 := by
    have hcoef : 1 ≤ d ^ 2 * L := by nlinarith [hd2, hLone]
    nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg N)]
  have hfourth : d ^ 4 * (ell : ℝ) ^ 2 ≤
      4 * (d ^ 2 * L * N ^ 2) := by
    have hsqell : (ell : ℝ) ^ 2 ≤ (2 * L) ^ 2 := by
      nlinarith [hEllU, hLpos]
    have hcore : d ^ 4 * L ^ 2 ≤ d ^ 4 * L ^ 4 := by
      have hLsq : 1 ≤ L ^ 2 := by nlinarith [hLone]
      have : L ^ 2 ≤ L ^ 4 := by
        calc
          L ^ 2 = L ^ 2 * 1 := by ring
          _ ≤ L ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left hLsq (sq_nonneg L)
          _ = L ^ 4 := by ring
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hcore2 : d ^ 4 * L ^ 4 = d ^ 2 * L * N ^ 2 := by
      rw [← hLcube]
      ring
    nlinarith [mul_le_mul_of_nonneg_left hsqell (by positivity : 0 ≤ d ^ 4), hcore, hcore2]
  have hfifth : d ^ 3 * N ^ 2 ≤ d ^ 2 * L * N ^ 2 := by
    have hcoef : d ≤ L := hdleL
    have hnon : 0 ≤ d ^ 2 * N ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcoef hnon]
  exact ⟨hfirst, hsecond, hthird, hfourth, hfifth⟩

end Esgk

end




















section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open _root_.Polynomial


theorem Polynomial.roots_toFinset_card_pos_of_natDegree_pos
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : Polynomial K) (hq : 0 < q.natDegree) :
    0 < q.roots.toFinset.card := by
  have hroots_card : q.roots.card = q.natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have hroots_ne : q.roots ≠ 0 := by
    intro hzero
    rw [hzero] at hroots_card
    simp at hroots_card
    omega
  exact Finset.card_pos.mpr (Multiset.toFinset_nonempty.mpr hroots_ne)


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open _root_.Polynomial


theorem Polynomial.eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_eq_singleton
    (p : ℂ[X]) (_hp : p ≠ 0) {τ : ℂ} (hτ : p.roots.toFinset = {τ}) :
    p = C p.leadingCoeff * (X - C τ) ^ p.natDegree := by
  classical
  have hroots : p.roots = Multiset.replicate p.roots.card τ := by
    apply Multiset.eq_replicate_card.mpr
    intro z hz
    have hz' : z ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr hz
    simpa [hτ] using hz'
  calc
    p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod :=
      (IsAlgClosed.splits p).eq_prod_roots
    _ = C p.leadingCoeff * (X - C τ) ^ p.natDegree := by
      rw [hroots, Multiset.map_replicate, Multiset.prod_replicate,
        IsAlgClosed.card_roots_eq_natDegree]


theorem Polynomial.exists_eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_card_eq_one
    (p : ℂ[X]) (_hp : p ≠ 0) (hcard : p.roots.toFinset.card = 1) :
    ∃ τ : ℂ, p = C p.leadingCoeff * (X - C τ) ^ p.natDegree := by
  classical
  obtain ⟨τ, hτ⟩ := Finset.card_eq_one.mp hcard
  exact ⟨τ,
    Polynomial.eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_eq_singleton
      p _hp hτ⟩

end Esgk

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial


@[simp]
theorem bivariateCornerExponent_zero (p : ℕ) : bivariateCornerExponent p 0 = p := by
  simp [bivariateCornerExponent]

@[simp]
theorem bivariateCornerExponent_one (p : ℕ) : bivariateCornerExponent p 1 = p := by
  simp [bivariateCornerExponent]


theorem coeff_bivariateCornerRemainder (p : ℕ) (Q : BidegreePolynomial ℂ)
    (e : Fin 2 →₀ ℕ) :
    coeff e (bivariateCornerRemainder p Q) =
      if e = bivariateCornerExponent p then 0 else coeff e Q := by
  rw [bivariateCornerRemainder, coeff_sub, coeff_monomial]
  by_cases he : e = bivariateCornerExponent p
  · subst e
    simp
  · simp [he, Ne.symm he]

@[simp]
theorem coeff_bivariateCornerRemainder_corner (p : ℕ) (Q : BidegreePolynomial ℂ) :
    coeff (bivariateCornerExponent p) (bivariateCornerRemainder p Q) = 0 := by
  simp [coeff_bivariateCornerRemainder]

 
theorem coeff_bivariateCornerExponent_ne_zero (Q : BidegreePolynomial ℂ) (p : ℕ)
    (hp : 0 < p) (hbound : BidegreeBound p Q) (htotal : Q.totalDegree = 2 * p) :
    coeff (bivariateCornerExponent p) Q ≠ 0 := by
  have hQ : Q ≠ 0 := by
    intro hzero
    subst Q
    simp at htotal
    omega
  obtain ⟨e, he, hmax⟩ :=
    Finset.exists_mem_eq_sup Q.support (MvPolynomial.support_nonempty.mpr hQ)
      (fun e ↦ e.sum fun _ k ↦ k)
  have hesum : e.sum (fun _ k ↦ k) = 2 * p := by
    calc
      e.sum (fun _ k ↦ k) = Q.support.sup (fun e ↦ e.sum fun _ k ↦ k) := hmax.symm
      _ = Q.totalDegree := rfl
      _ = 2 * p := htotal
  have hesum' : e 0 + e 1 = 2 * p := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hesum
  have hezero : e 0 = p := by
    have := (hbound e he).1
    have := (hbound e he).2
    omega
  have heone : e 1 = p := by
    have := (hbound e he).1
    have := (hbound e he).2
    omega
  have hecorner : e = bivariateCornerExponent p := by
    apply Finsupp.ext
    intro i
    fin_cases i
    · simpa using hezero
    · simpa using heone
  rw [← hecorner]
  exact MvPolynomial.mem_support_iff.mp he


theorem mem_support_bivariateCornerRemainder
    (Q : BidegreePolynomial ℂ) (p : ℕ) (hbound : BidegreeBound p Q)
    (hrow : ∀ a < p,
      coeff (Finsupp.single 0 a + Finsupp.single 1 p) Q = 0)
    (hcolumn : ∀ b < p,
      coeff (Finsupp.single 0 p + Finsupp.single 1 b) Q = 0)
    {e : Fin 2 →₀ ℕ} (he : e ∈ (bivariateCornerRemainder p Q).support) :
    e ∈ Q.support ∧ e 0 < p ∧ e 1 < p := by
  have hcoeffR : coeff e (bivariateCornerRemainder p Q) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he
  have hne : e ≠ bivariateCornerExponent p := by
    intro hecorner
    subst e
    exact hcoeffR (coeff_bivariateCornerRemainder_corner p Q)
  have hcoeffQ : coeff e Q ≠ 0 := by
    rw [coeff_bivariateCornerRemainder, if_neg hne] at hcoeffR
    exact hcoeffR
  have heQ : e ∈ Q.support := MvPolynomial.mem_support_iff.mpr hcoeffQ
  have hezero_le := (hbound e heQ).1
  have heone_le := (hbound e heQ).2
  have hezero_lt : e 0 < p := by
    by_contra hnot
    have hezero : e 0 = p := by omega
    by_cases heone : e 1 = p
    · apply hne
      apply Finsupp.ext
      intro i
      fin_cases i
      · simpa using hezero
      · simpa using heone
    · have heone_lt : e 1 < p := by omega
      have hzero := hcolumn (e 1) heone_lt
      apply hcoeffQ
      rw [← hzero]
      congr 1
      apply Finsupp.ext
      intro i
      fin_cases i
      · simpa using hezero
      · simp
  have heone_lt : e 1 < p := by
    by_contra hnot
    have heone : e 1 = p := by omega
    have hzero := hrow (e 0) hezero_lt
    apply hcoeffQ
    rw [← hzero]
    congr 1
    apply Finsupp.ext
    intro i
    fin_cases i
    · simp
    · simpa using heone
  exact ⟨heQ, hezero_lt, heone_lt⟩

 
theorem bidegreeBound_bivariateCornerRemainder
    (Q : BidegreePolynomial ℂ) (p : ℕ) (hp : 0 < p) (hbound : BidegreeBound p Q)
    (hrow : ∀ a < p,
      coeff (Finsupp.single 0 a + Finsupp.single 1 p) Q = 0)
    (hcolumn : ∀ b < p,
      coeff (Finsupp.single 0 p + Finsupp.single 1 b) Q = 0) :
    BidegreeBound (p - 1) (bivariateCornerRemainder p Q) := by
  intro e he
  obtain ⟨_, hezero, heone⟩ :=
    mem_support_bivariateCornerRemainder Q p hbound hrow hcolumn he
  constructor <;> omega


theorem exists_bivariate_corner_normal_form
    (Q : BidegreePolynomial ℂ) (p : ℕ) (hp : 0 < p) (hbound : BidegreeBound p Q)
    (htotal : Q.totalDegree = 2 * p)
    (hrow : ∀ a < p,
      coeff (Finsupp.single 0 a + Finsupp.single 1 p) Q = 0)
    (hcolumn : ∀ b < p,
      coeff (Finsupp.single 0 p + Finsupp.single 1 b) Q = 0) :
    ∃ c : ℂ, ∃ R : BidegreePolynomial ℂ,
      c ≠ 0 ∧ Q = monomial (bivariateCornerExponent p) c + R ∧
        BidegreeBound (p - 1) R := by
  refine ⟨coeff (bivariateCornerExponent p) Q, bivariateCornerRemainder p Q,
    coeff_bivariateCornerExponent_ne_zero Q p hp hbound htotal, ?_,
    bidegreeBound_bivariateCornerRemainder Q p hp hbound hrow hcolumn⟩
  rw [bivariateCornerRemainder]
  abel

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open Filter Topology
open scoped Pointwise Real InnerProductSpace EuclideanSpace

variable {n : ℕ}


local notation "o" => (positiveOrientation : Orientation ℝ _root_.Point2 (Fin 2))

 
local notation "J" => Orientation.rightAngleRotation o







 



end Esgk

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna.
-/


namespace Esgk


theorem fourthRootIncidenceOptimization_of_threshold
    (d N I D K : ℝ)
    (hd2 : 2 ≤ d) (hN : 0 < N) (hK : 1 ≤ K) (hD : 0 < D)
    (hthreshold : (24 : ℝ) ^ 3 * d ^ 5 ≤ N ^ 2)
    (hraw : ∀ j : ℕ, 24 * d ≤ (j : ℝ) →
      I ≤ K * (d * N ^ 3 / Real.sqrt (j : ℝ) +
        d ^ 2 * (j : ℝ) * N ^ 2 + N ^ 2 +
        d ^ 4 * (j : ℝ) ^ 2 + d ^ 3 * N ^ 2))
    (hlower : N ^ 4 ≤ 64 * D * I) :
    I ≤ 9 * K * d ^ 2 * (N / d) ^ ((2 : ℝ) / 3) * N ^ 2 ∧
      N ^ 4 ≤ (576 * K) ^ 3 * d ^ 4 * D ^ 3 := by
  obtain ⟨ell, hLbound, hell, hLell, hellL⟩ :=
    fourthRootPartitionWindow d N hd2 hN hthreshold
  let L : ℝ := (N / d) ^ ((2 : ℝ) / 3)
  have hLcube : d ^ 2 * L ^ 3 = N ^ 2 := by
    have hd : 0 < d := by linarith
    have hx : 0 ≤ N / d := by positivity
    calc
      d ^ 2 * L ^ 3 = d ^ 2 * (N / d) ^ 2 := by
        dsimp [L]
        rw [← Real.rpow_natCast ((N / d) ^ ((2 : ℝ) / 3)) 3,
          ← Real.rpow_mul hx]
        norm_num
      _ = N ^ 2 := by
        field_simp [ne_of_gt hd]
  obtain ⟨hfirst, hsecond, hthird, hfourth, hfifth⟩ :=
    fourthRootPartitionBounds d N L ell hd2 hN hLbound hLcube hLell hellL
  have hK0 : 0 ≤ K := by linarith
  have hraw' := hraw ell hell
  let degreeRight : ℝ := d ^ 2 * L * N ^ 2
  have hsum :
      d * N ^ 3 / Real.sqrt (ell : ℝ) +
          d ^ 2 * (ell : ℝ) * N ^ 2 + N ^ 2 +
          d ^ 4 * (ell : ℝ) ^ 2 + d ^ 3 * N ^ 2 ≤ 9 * degreeRight := by
    dsimp [degreeRight]
    nlinarith
  have hI : I ≤ 9 * K * degreeRight := by
    have hs := mul_le_mul_of_nonneg_left hsum hK0
    calc
      I ≤ K * (d * N ^ 3 / Real.sqrt (ell : ℝ) +
          d ^ 2 * (ell : ℝ) * N ^ 2 + N ^ 2 +
          d ^ 4 * (ell : ℝ) ^ 2 + d ^ 3 * N ^ 2) := hraw'
      _ ≤ K * (9 * degreeRight) := hs
      _ = 9 * K * degreeRight := by ring
  have hE3 : degreeRight ^ 3 = d ^ 4 * N ^ 8 := by
    calc
      degreeRight ^ 3 = d ^ 4 * N ^ 6 * (d ^ 2 * L ^ 3) := by dsimp [degreeRight]; ring
      _ = d ^ 4 * N ^ 6 * N ^ 2 := by rw [hLcube]
      _ = d ^ 4 * N ^ 8 := by ring
  have hNI : N ^ 4 ≤ 576 * K * D * degreeRight := by
    calc
      N ^ 4 ≤ 64 * D * I := hlower
      _ ≤ 64 * D * (9 * K * degreeRight) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
      _ = 576 * K * D * degreeRight := by ring
  have hN8 : 0 < N ^ 8 := by positivity
  have hcube : (N ^ 4) ^ 3 ≤ (576 * K * D * degreeRight) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hNI 3
  have hcancel : N ^ 4 ≤ (576 * K) ^ 3 * D ^ 3 * d ^ 4 := by
    apply (mul_le_mul_iff_left₀ hN8).mp
    calc
      N ^ 4 * N ^ 8 = (N ^ 4) ^ 3 := by ring
      _ ≤ (576 * K * D * degreeRight) ^ 3 := hcube
      _ = (576 * K) ^ 3 * D ^ 3 * degreeRight ^ 3 := by ring
      _ = (576 * K) ^ 3 * D ^ 3 * (d ^ 4 * N ^ 8) := by rw [hE3]
      _ = ((576 * K) ^ 3 * D ^ 3 * d ^ 4) * N ^ 8 := by ring
  refine ⟨?_, ?_⟩
  · simpa [degreeRight, L, mul_assoc] using hI
  · simpa [mul_assoc, mul_left_comm, mul_comm] using hcancel

end Esgk

end





























section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw

open EuclideanGeometry


lemma ParallelLinePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ParallelLinePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with ⟨a, b, c₁, c₂, hab, rfl, rfl⟩
  exact Or.inl ⟨a, b, c₁, hab, rfl⟩


lemma OrthogonalLinePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : OrthogonalLinePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with ⟨a₁, b₁, c₁, a₂, b₂, c₂, hab₁, hab₂, _horth, rfl, rfl⟩
  exact Or.inl ⟨a₁, b₁, c₁, hab₁, rfl⟩


lemma ConcentricCirclePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ConcentricCirclePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with ⟨center, r₁, r₂, rfl, rfl⟩
  exact Or.inr ⟨center, r₁, rfl⟩


lemma ExceptionalCurvePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ExceptionalCurvePair C₁ C₂) : PlaneCurve.IsLineOrCircle C₁ := by
  rcases h with h | h | h
  · exact ParallelLinePair.left_controlledDegenerate h
  · exact OrthogonalLinePair.left_controlledDegenerate h
  · exact ConcentricCirclePair.left_controlledDegenerate h


lemma assumption31Data_of_not_controlledDegenerate {C₁ C₂ : Set Point2}
    {P₁ P₂ : Finset Point2}
    (h₁ : ¬ PlaneCurve.IsLineOrCircle C₁)
    (h₂ : ¬ PlaneCurve.IsLineOrCircle C₂)
    (hdisj : Disjoint (P₁ : Set Point2) (P₂ : Set Point2))
    (hexc : ¬ ExceptionalCurvePair C₁ C₂) :
    Assumption31Data C₁ C₂ P₁ P₂ where
  noVerticalComponent₁ := by
    rintro ⟨c, hc⟩
    exact h₁ (Or.inl ⟨1, 0, c, by simp, by rw [hc]; ext p; simp⟩)
  noVerticalComponent₂ := by
    rintro ⟨c, hc⟩
    exact h₂ (Or.inl ⟨1, 0, c, by simp, by rw [hc]; ext p; simp⟩)
  pointSetsDisjoint := hdisj
  circleCenterNotInPointSet :=
    ⟨fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₁,
     fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₂⟩
  sparseConcentricFibers :=
    ⟨fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₁,
     fun center r hsphere => absurd (Or.inr ⟨center, r, hsphere⟩) h₂⟩
  sparseParallelFibers :=
    ⟨fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₁,
     fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₂⟩
  sparseOrthogonalFibers :=
    ⟨fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₁,
     fun a b c hab hline => absurd (Or.inl ⟨a, b, c, hab, hline⟩) h₂⟩
  noExceptionalPair := hexc


lemma lemma37_equalDistanceQuadruple_lower {d : ℕ}
    (X : PreparedBipartiteInput d) :
    X.P₁.card ^ 2 * X.P₂.card ^ 2 ≤
      (bipartiteDistances X.P₁ X.P₂).card *
        (equalDistanceQuadruples X).card := by
  classical
  let S : Finset (Point2 × Point2) := X.P₁.product X.P₂
  let f : Point2 × Point2 → ℝ := fun pq ↦ dist pq.1 pq.2
  let fibers : ℝ → Finset (Point2 × Point2) := fun r ↦ bundle_LeanFormalizations_PachDeZeeuw_Basic_distanceFiber X.P₁ X.P₂ r
  let qfibers : ℝ → Finset ((Point2 × Point2) × (Point2 × Point2)) := fun r ↦
    fibers r ×ˢ fibers r
  have hS : S.card = X.P₁.card * X.P₂.card := by
    simp [S]
  have hsum : ∑ r ∈ S.image f, (fibers r).card = S.card := by
    have hsum0 :
        ∑ r ∈ S.image f, (fibers r).card =
          {i ∈ S | ∃ a b, (a ∈ X.P₁ ∧ b ∈ X.P₂) ∧ f (a, b) = f i}.card := by
      simpa [S, f, fibers, bundle_LeanFormalizations_PachDeZeeuw_Basic_distanceFiber] using
        (Finset.sum_card_fiberwise_eq_card_filter S (S.image f) f)
    have hfilter :
        {i ∈ S | ∃ a b, (a ∈ X.P₁ ∧ b ∈ X.P₂) ∧ f (a, b) = f i} = S := by
      apply Finset.filter_true_of_mem
      intro i hi
      rcases Finset.mem_product.mp hi with ⟨hiA, hiB⟩
      exact ⟨i.1, i.2, ⟨⟨hiA, hiB⟩, rfl⟩⟩
    simpa [hfilter] using hsum0
  have hbiUnion :
      ((S.image f).biUnion qfibers).card =
        ∑ r ∈ S.image f, (fibers r).card ^ 2 := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl ?_
      intro r hr
      simp [qfibers, pow_two, Finset.card_product]
    · intro r₁ _hr₁ r₂ _hr₂ hne
      change Disjoint (qfibers r₁) (qfibers r₂)
      rw [Finset.disjoint_left]
      intro q hq₁ hq₂
      rw [Finset.mem_product] at hq₁ hq₂
      rcases hq₁ with ⟨hq₁₁, hq₁₂⟩
      rcases hq₂ with ⟨hq₂₁, hq₂₂⟩
      simp [fibers, bundle_LeanFormalizations_PachDeZeeuw_Basic_distanceFiber] at hq₁₁ hq₂₁
      rcases hq₁₁ with ⟨_, hdist₁⟩
      rcases hq₂₁ with ⟨_, hdist₂⟩
      exact hne (hdist₁.symm.trans hdist₂)
  have hquad_ge :
      ∑ r ∈ S.image f, (fibers r).card ^ 2 ≤ (equalDistanceQuadruples X).card := by
    have hsub : (S.image f).biUnion qfibers ⊆ equalDistanceQuadruples X := by
      intro q hq
      rw [Finset.mem_biUnion] at hq
      rcases hq with ⟨r, hr, hq⟩
      rw [Finset.mem_image] at hr
      rcases hr with ⟨pq, hpq, rfl⟩
      rw [Finset.mem_product] at hq
      rcases hq with ⟨hq₁, hq₂⟩
      simp [fibers, bundle_LeanFormalizations_PachDeZeeuw_Basic_distanceFiber] at hq₁ hq₂
      rcases hq₁ with ⟨hq₁S, hq₁dist⟩
      rcases hq₂ with ⟨hq₂S, hq₂dist⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr hq₁S, Finset.mem_product.mpr hq₂S⟩, ?_⟩
      simpa [S, f] using hq₁dist.trans hq₂dist.symm
    calc
      ∑ r ∈ S.image f, (fibers r).card ^ 2 = ((S.image f).biUnion qfibers).card := by
        simpa [qfibers] using hbiUnion.symm
      _ ≤ (equalDistanceQuadruples X).card := Finset.card_le_card hsub
  have hcs :
      S.card ^ 2 ≤ (S.image f).card * ∑ r ∈ S.image f, (fibers r).card ^ 2 := by
    simpa [hsum] using
      (sq_sum_le_card_mul_sum_sq (s := S.image f) (f := fun r ↦ (fibers r).card))
  have hmain : S.card ^ 2 ≤ (S.image f).card * (equalDistanceQuadruples X).card := by
    exact hcs.trans (Nat.mul_le_mul_left _ hquad_ge)
  have hmain' : (X.P₁.card * X.P₂.card) ^ 2 ≤
      (bipartiteDistances X.P₁ X.P₂).card * (equalDistanceQuadruples X).card := by
    rw [hS] at hmain
    simpa [S, f, bipartiteDistances, equalDistanceQuadruples] using hmain
  simpa [Nat.mul_pow] using hmain'

end PachDeZeeuw

end

















section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk


@[simp]
theorem planeIsotropicCoordinateEquiv_symm_apply (p : ComplexPlanePoly) :
    planeIsotropicCoordinateEquiv.symm p = isotropicToPlaneCoordinates p :=
  rfl


@[simp]
theorem isotropicTranslationEquiv_apply (ξ : ℂ) (p : ComplexPlanePoly) :
    isotropicTranslationEquiv ξ p = isotropicTranslation ξ p :=
  rfl

@[simp]
theorem isotropicTranslationEquiv_symm_apply (ξ : ℂ) (p : ComplexPlanePoly) :
    (isotropicTranslationEquiv ξ).symm p = inverseIsotropicTranslation ξ p :=
  rfl

end Esgk
end

end








section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw

open EuclideanGeometry


private lemma inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__curveWitnessPoly₂_spec {d : ℕ}
    (X : PreparedBipartiteInput d) :
    X.C₂ = {x : Point2 | MvPolynomial.eval (fun i => x i) (bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_curveWitnessPoly₂ X) = 0} := by
  dsimp [bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_curveWitnessPoly₂]
  rcases Classical.choose_spec X.hC₂ with ⟨_, _, _, hEq⟩
  simpa using hEq


private lemma inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxPointOfPair_injective : Function.Injective bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair := by
  intro p q h
  cases p with
  | mk p1 p2 =>
    cases q with
    | mk q1 q2 =>
      have h0 := congrArg (fun z : Point4 => z 0) h
      have h1 := congrArg (fun z : Point4 => z 1) h
      have h2 := congrArg (fun z : Point4 => z 2) h
      have h3 := congrArg (fun z : Point4 => z 3) h
      simp [bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair] at h0 h1 h2 h3
      ext i <;> fin_cases i <;> simp [h0, h1, h2, h3]


private lemma inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxFirstPair_of_auxPointOfPair (pq : Point2 × Point2) :
    bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxFirstPair (bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair pq) = pq.1 := by
  ext i
  fin_cases i <;> simp [bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxFirstPair, bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair]

private lemma inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxSecondPair_of_auxPointOfPair (pq : Point2 × Point2) :
    bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxSecondPair (bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair pq) = pq.2 := by
  ext i
  fin_cases i <;> simp [bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxSecondPair, bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair]


private lemma inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxPointOfPair_mem_auxPointSet {d : ℕ}
    (X : PreparedBipartiteInput d) {p q : Point2}
    (hp : p ∈ X.P₂) (hq : q ∈ X.P₂) :
    bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair (p, q) ∈ auxPointSet X := by
  dsimp [auxPointSet]
  refine Finset.mem_image.mpr ?_
  refine ⟨(p, q), ?_, rfl⟩
  exact Finset.mem_product.mpr ⟨hp, hq⟩

private lemma inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxPointOfPair_mem_auxCurve {d : ℕ}
    (X : PreparedBipartiteInput d) (i j : X.P₁) {p q : Point2}
    (hp : p ∈ X.P₂) (hq : q ∈ X.P₂)
    (hdist : dist (i : Point2) p = dist (j : Point2) q) :
    bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair (p, q) ∈ auxCurve X i j := by
  dsimp [auxCurve]
  constructor
  · have hpC₂ : p ∈ X.C₂ := X.hP₂ hp
    rw [inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__curveWitnessPoly₂_spec] at hpC₂
    simpa [inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxFirstPair_of_auxPointOfPair] using hpC₂
  · constructor
    · have hqC₂ : q ∈ X.C₂ := X.hP₂ hq
      rw [inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__curveWitnessPoly₂_spec] at hqC₂
      simpa [inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxSecondPair_of_auxPointOfPair] using hqC₂
    · have hsq : dist (i : Point2) p ^ 2 = dist (j : Point2) q ^ 2 := by
        exact congrArg (fun t : ℝ => t ^ 2) hdist
      simpa [inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxFirstPair_of_auxPointOfPair, inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxSecondPair_of_auxPointOfPair] using hsq


theorem auxIncidenceBridge : AuxIncidenceBridgeStatement := by
  intro d X
  classical
  let S : Finset ((Point2 × Point2) × (Point2 × Point2)) := equalDistanceQuadruples X
  let f : {x // x ∈ S} → Point4 × (X.P₁ × X.P₁) := fun q =>
    let hquad : q.1 ∈ (X.P₁.product X.P₂).product (X.P₁.product X.P₂) := (Finset.mem_filter.mp q.2).1
    let hleft : q.1.1 ∈ X.P₁.product X.P₂ := (Finset.mem_product.mp hquad).1
    let hright : q.1.2 ∈ X.P₁.product X.P₂ := (Finset.mem_product.mp hquad).2
    let hi : q.1.1.1 ∈ X.P₁ := (Finset.mem_product.mp hleft).1
    let hj : q.1.2.1 ∈ X.P₁ := (Finset.mem_product.mp hright).1
    ⟨bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair (q.1.1.2, q.1.2.2), (⟨q.1.1.1, hi⟩, ⟨q.1.2.1, hj⟩)⟩
  have hf : Function.Injective f := by
    intro q1 q2 h
    cases q1 with
    | mk q1 hq1 =>
      cases q2 with
      | mk q2 hq2 =>
        have hpt : bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair (q1.1.2, q1.2.2) = bundle_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves_auxPointOfPair (q2.1.2, q2.2.2) := by
          have h' := congrArg Prod.fst h
          simpa [f] using h'
        have hidx : (q1.1.1, q1.2.1) = (q2.1.1, q2.2.1) := by
          have h' := congrArg Prod.snd h
          simpa [f] using h'
        have htarget : (q1.1.2, q1.2.2) = (q2.1.2, q2.2.2) := by
          exact inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxPointOfPair_injective hpt
        have hleft : q1.1 = q2.1 := by
          have h11 : q1.1.1 = q2.1.1 := by
            simpa using (show q1.1.1 = q2.1.1 ∧ q1.2.1 = q2.2.1 from by simpa using hidx).1
          have h12 : q1.1.2 = q2.1.2 := by
            simpa using (show q1.1.2 = q2.1.2 ∧ q1.2.2 = q2.2.2 from by simpa using htarget).1
          ext i <;> fin_cases i <;> simp [h11, h12]
        have hright : q1.2 = q2.2 := by
          have h21 : q1.2.1 = q2.2.1 := by
            simpa using (show q1.1.1 = q2.1.1 ∧ q1.2.1 = q2.2.1 from by simpa using hidx).2
          have h22 : q1.2.2 = q2.2.2 := by
            simpa using (show q1.1.2 = q2.1.2 ∧ q1.2.2 = q2.2.2 from by simpa using htarget).2
          ext i <;> fin_cases i <;> simp [h21, h22]
        apply Subtype.ext
        apply Prod.ext <;> assumption
  have hsubset : Finset.image f S.attach ⊆ auxIncidences X := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    have hquad : q.1 ∈ (X.P₁.product X.P₂).product (X.P₁.product X.P₂) := by
      exact (Finset.mem_filter.mp q.2).1
    have hdist : dist q.1.1.1 q.1.1.2 = dist q.1.2.1 q.1.2.2 := by
      exact (Finset.mem_filter.mp q.2).2
    rcases Finset.mem_product.mp hquad with ⟨hleft, hright⟩
    rcases Finset.mem_product.mp hleft with ⟨hi, hp⟩
    rcases Finset.mem_product.mp hright with ⟨hj, hq⟩
    have hpoint : (f q).1 ∈ auxPointSet X := by
      simpa [f] using inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxPointOfPair_mem_auxPointSet X hp hq
    have hcurve : (f q).1 ∈ auxCurve X ⟨q.1.1.1, hi⟩ ⟨q.1.2.1, hj⟩ := by
      simpa [f] using
        inline_LeanFormalizations_PachDeZeeuw_AuxiliaryCurves__auxPointOfPair_mem_auxCurve X ⟨q.1.1.1, hi⟩ ⟨q.1.2.1, hj⟩ hp hq hdist
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · refine Finset.mem_product.mpr ?_
      constructor
      · exact hpoint
      · simp
    · simpa [f] using hcurve
  calc
    (equalDistanceQuadruples X).card = S.attach.card := by
      simp [S]
    _ = (Finset.image f S.attach).card := by
      rw [Finset.card_image_of_injective _ hf]
    _ ≤ (auxIncidences X).card := Finset.card_le_card hsubset

end PachDeZeeuw

end








section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw

open EuclideanGeometry


end PachDeZeeuw

namespace PachDeZeeuw

open EuclideanGeometry


lemma bipartiteDistances_card_le_distinctDistances_of_subset_disjoint
    {P₁ P₂ P : Finset Point2}
    (h₁ : P₁ ⊆ P) (h₂ : P₂ ⊆ P) (hdisj : Disjoint P₁ P₂) :
    (bipartiteDistances P₁ P₂).card ≤ EuclideanGeometry.distinctDistances P := by
  unfold bipartiteDistances EuclideanGeometry.distinctDistances
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_image] at hr ⊢
  rcases hr with ⟨pq, hpq, rfl⟩
  refine ⟨(pq.1, pq.2), ?_, rfl⟩
  rw [Finset.mem_offDiag]
  rcases Finset.mem_product.mp hpq with ⟨hp₁, hp₂⟩
  refine ⟨h₁ hp₁, h₂ hp₂, ?_⟩
  intro hEq
  exact Disjoint.forall_ne_finset hdisj hp₁ hp₂ hEq


lemma split_finset_into_two_comparable_parts
    (P : Finset Point2) (hP : 2 ≤ P.card) :
    ∃ P₁ P₂ : Finset Point2,
      Disjoint P₁ P₂ ∧ P₁ ∪ P₂ = P ∧
      P.card ≤ 3 * P₁.card ∧ P.card ≤ 3 * P₂.card := by
  classical
  let k : ℕ := (P.card + 2) / 3
  have hk_le : k ≤ P.card := by
    dsimp [k]
    omega
  rcases Finset.exists_subset_card_eq hk_le with ⟨P₁, hP₁sub, hP₁card⟩
  let P₂ : Finset Point2 := P \ P₁
  have hP₂_def : P₂ = P \ P₁ := rfl
  have hdisj : Disjoint P₁ P₂ := by
    rw [hP₂_def, Finset.disjoint_left]
    intro x hx₁ hx₂
    exact (Finset.mem_sdiff.mp hx₂).2 hx₁
  have hunion : P₁ ∪ P₂ = P := by
    rw [hP₂_def, Finset.union_sdiff_of_subset hP₁sub]
  have hP₂card : P₂.card = P.card - P₁.card := by
    rw [hP₂_def, Finset.card_sdiff, Finset.inter_eq_left.2 hP₁sub]
  have hP₁big : P.card ≤ 3 * P₁.card := by
    rw [hP₁card]
    omega
  have hP₂big : P.card ≤ 3 * P₂.card := by
    rw [hP₂card]
    omega
  refine ⟨P₁, P₂, hdisj, hunion, hP₁big, hP₂big⟩


end PachDeZeeuw

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial

 
theorem bidegreeBound_iff_degreeOf_le {R : Type*} [CommSemiring R] (m : ℕ)
    (Q : BidegreePolynomial R) :
    BidegreeBound m Q ↔ degreeOf 0 Q ≤ m ∧ degreeOf 1 Q ≤ m := by
  constructor
  · intro hQ
    constructor <;> rw [degreeOf_le_iff] <;> intro e he
    · exact (hQ e he).1
    · exact (hQ e he).2
  · rintro ⟨hzero, hone⟩ e he
    exact ⟨degreeOf_le_iff.mp hzero e he, degreeOf_le_iff.mp hone e he⟩

 
theorem isotropicTranslation_monomial (ξ : ℂ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    isotropicTranslation ξ (monomial e c) =
      C c * (X 0 - C ξ) ^ e 0 * (X 1 - C (star ξ)) ^ e 1 := by
  rw [isotropicTranslation, eval₂Hom_monomial, Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two, mul_assoc]
  · intro i
    simp

 
theorem degreeOf_isotropicTranslation_monomial_le (ξ : ℂ) (e : Fin 2 →₀ ℕ) (c : ℂ)
    (i : Fin 2) : degreeOf i (isotropicTranslation ξ (monomial e c)) ≤ e i := by
  rw [isotropicTranslation_monomial]
  fin_cases i
  · have hzero : degreeOf 0 (X 0 - C ξ : BidegreePolynomial ℂ) ≤ 1 := by
      simpa using degreeOf_sub_le 0 (X 0 : BidegreePolynomial ℂ) (C ξ)
    have hone : degreeOf 0 (X 1 - C (star ξ) : BidegreePolynomial ℂ) ≤ 0 := by
      simpa [degreeOf_X, show (0 : Fin 2) ≠ 1 by decide] using
        degreeOf_sub_le 0 (X 1 : BidegreePolynomial ℂ) (C (star ξ))
    have hpowZero := degreeOf_pow_le 0 (X 0 - C ξ : BidegreePolynomial ℂ) (e 0)
    have hpowOne := degreeOf_pow_le 0 (X 1 - C (star ξ) : BidegreePolynomial ℂ) (e 1)
    have hmulLeft :=
      degreeOf_mul_le 0 (C c : BidegreePolynomial ℂ) ((X 0 - C ξ) ^ e 0)
    have hmul := degreeOf_mul_le 0
      ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0)
      ((X 1 - C (star ξ)) ^ e 1)
    have hpowZero' : degreeOf 0 ((X 0 - C ξ : BidegreePolynomial ℂ) ^ e 0) ≤ e 0 := by
      calc
        _ ≤ e 0 * degreeOf 0 (X 0 - C ξ : BidegreePolynomial ℂ) := hpowZero
        _ ≤ e 0 * 1 := Nat.mul_le_mul_left _ hzero
        _ = e 0 := Nat.mul_one _
    have hpowOne' :
        degreeOf 0 ((X 1 - C (star ξ) : BidegreePolynomial ℂ) ^ e 1) ≤ 0 := by
      calc
        _ ≤ e 1 * degreeOf 0 (X 1 - C (star ξ) : BidegreePolynomial ℂ) := hpowOne
        _ ≤ e 1 * 0 := Nat.mul_le_mul_left _ hone
        _ = 0 := Nat.mul_zero _
    have hmulLeft' :
        degreeOf 0 ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0) ≤ e 0 := by
      calc
        _ ≤ degreeOf 0 (C c : BidegreePolynomial ℂ) +
            degreeOf 0 ((X 0 - C ξ) ^ e 0) := hmulLeft
        _ ≤ 0 + e 0 := Nat.add_le_add (by simp) hpowZero'
        _ = e 0 := Nat.zero_add _
    calc
      degreeOf 0 (C c * (X 0 - C ξ) ^ e 0 * (X 1 - C (star ξ)) ^ e 1)
          ≤ degreeOf 0 (C c * (X 0 - C ξ) ^ e 0) +
              degreeOf 0 ((X 1 - C (star ξ)) ^ e 1) := hmul
      _ ≤ e 0 + 0 := Nat.add_le_add hmulLeft' hpowOne'
      _ = e 0 := Nat.add_zero _
  · have hzero : degreeOf 1 (X 0 - C ξ : BidegreePolynomial ℂ) ≤ 0 := by
      simpa [degreeOf_X, show (1 : Fin 2) ≠ 0 by decide] using
        degreeOf_sub_le 1 (X 0 : BidegreePolynomial ℂ) (C ξ)
    have hone : degreeOf 1 (X 1 - C (star ξ) : BidegreePolynomial ℂ) ≤ 1 := by
      simpa using
        degreeOf_sub_le 1 (X 1 : BidegreePolynomial ℂ) (C (star ξ))
    have hpowZero := degreeOf_pow_le 1 (X 0 - C ξ : BidegreePolynomial ℂ) (e 0)
    have hpowOne := degreeOf_pow_le 1 (X 1 - C (star ξ) : BidegreePolynomial ℂ) (e 1)
    have hmulLeft :=
      degreeOf_mul_le 1 (C c : BidegreePolynomial ℂ) ((X 0 - C ξ) ^ e 0)
    have hmul := degreeOf_mul_le 1
      ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0)
      ((X 1 - C (star ξ)) ^ e 1)
    have hpowZero' : degreeOf 1 ((X 0 - C ξ : BidegreePolynomial ℂ) ^ e 0) ≤ 0 := by
      calc
        _ ≤ e 0 * degreeOf 1 (X 0 - C ξ : BidegreePolynomial ℂ) := hpowZero
        _ ≤ e 0 * 0 := Nat.mul_le_mul_left _ hzero
        _ = 0 := Nat.mul_zero _
    have hpowOne' :
        degreeOf 1 ((X 1 - C (star ξ) : BidegreePolynomial ℂ) ^ e 1) ≤ e 1 := by
      calc
        _ ≤ e 1 * degreeOf 1 (X 1 - C (star ξ) : BidegreePolynomial ℂ) := hpowOne
        _ ≤ e 1 * 1 := Nat.mul_le_mul_left _ hone
        _ = e 1 := Nat.mul_one _
    have hmulLeft' :
        degreeOf 1 ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0) ≤ 0 := by
      calc
        _ ≤ degreeOf 1 (C c : BidegreePolynomial ℂ) +
            degreeOf 1 ((X 0 - C ξ) ^ e 0) := hmulLeft
        _ ≤ 0 + 0 := Nat.add_le_add (by simp) hpowZero'
        _ = 0 := Nat.zero_add _
    calc
      degreeOf 1 (C c * (X 0 - C ξ) ^ e 0 * (X 1 - C (star ξ)) ^ e 1)
          ≤ degreeOf 1 (C c * (X 0 - C ξ) ^ e 0) +
              degreeOf 1 ((X 1 - C (star ξ)) ^ e 1) := hmul
      _ ≤ 0 + e 1 := Nat.add_le_add hmulLeft' hpowOne'
      _ = e 1 := Nat.zero_add _

 
theorem degreeOf_isotropicTranslation_le (ξ : ℂ) (Q : BidegreePolynomial ℂ) (i : Fin 2) :
    degreeOf i (isotropicTranslation ξ Q) ≤ degreeOf i Q := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (degreeOf_sum_le i Q.support fun e ↦
    isotropicTranslation ξ (monomial e (coeff e Q))).trans ?_
  rw [degreeOf_eq_sup]
  exact Finset.sup_le fun e he ↦
    (degreeOf_isotropicTranslation_monomial_le ξ e (coeff e Q) i).trans
      (Finset.le_sup (f := fun d : Fin 2 →₀ ℕ ↦ d i) he)


theorem bidegreeBound_isotropicTranslation (ξ : ℂ) (m : ℕ) {Q : BidegreePolynomial ℂ}
    (hQ : BidegreeBound m Q) : BidegreeBound m (isotropicTranslation ξ Q) := by
  rw [bidegreeBound_iff_degreeOf_le] at hQ ⊢
  exact ⟨(degreeOf_isotropicTranslation_le ξ Q 0).trans hQ.1,
    (degreeOf_isotropicTranslation_le ξ Q 1).trans hQ.2⟩

 
theorem totalDegree_le_two_mul_of_bidegreeBound {R : Type*} [CommSemiring R] (m : ℕ)
    {Q : BidegreePolynomial R} (hQ : BidegreeBound m Q) : totalDegree Q ≤ 2 * m := by
  rw [totalDegree]
  refine Finset.sup_le fun e he ↦ ?_
  have hzero := (hQ e he).1
  have hone := (hQ e he).2
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
  simp only [Fin.sum_univ_two]
  omega


end Esgk
end

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial


theorem totalDegree_eval₂Hom_le_of_isHomogeneous_one
    {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S)
    (hf : ∀ r, (f r).IsHomogeneous 0)
    (hg : ∀ i, (g i).IsHomogeneous 1)
    (P : MvPolynomial σ R) :
    ((MvPolynomial.eval₂Hom f g) P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [← P.sum_homogeneousComponent]
  rw [map_sum (MvPolynomial.eval₂Hom f g)]
  refine MvPolynomial.totalDegree_finsetSum_le (d := P.totalDegree) ?_
  intro d hd
  have hhom :=
    (MvPolynomial.homogeneousComponent_isHomogeneous d P).eval₂ f g hf hg
  have hterm :
      ((MvPolynomial.eval₂Hom f g)
        (MvPolynomial.homogeneousComponent d P)).totalDegree ≤ d := by
    simpa only [MvPolynomial.coe_eval₂Hom, Nat.one_mul] using hhom.totalDegree_le
  have hle : d ≤ P.totalDegree := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hd
  exact hterm.trans hle

private theorem inline_Esgk_PlaneIsotropicDegree__planeToIsotropicCoordinates_image_isHomogeneous
    (i : Fin 2) :
    (![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * Complex.I)) *
          (MvPolynomial.X 0 - MvPolynomial.X 1)] i : ComplexPlanePoly).IsHomogeneous 1 := by
  fin_cases i
  · exact ((MvPolynomial.isHomogeneous_X ℂ 0).add
      (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _
  · exact ((MvPolynomial.isHomogeneous_X ℂ 0).sub
      (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _

private theorem inline_Esgk_PlaneIsotropicDegree__isotropicToPlaneCoordinates_image_isHomogeneous
    (i : Fin 2) :
    (![MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1,
        MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1] i :
      ComplexPlanePoly).IsHomogeneous 1 := by
  fin_cases i
  · exact (MvPolynomial.isHomogeneous_X ℂ 0).add
      ((MvPolynomial.isHomogeneous_X ℂ 1).C_mul _)
  · exact (MvPolynomial.isHomogeneous_X ℂ 0).sub
      ((MvPolynomial.isHomogeneous_X ℂ 1).C_mul _)

 
theorem planeToIsotropicCoordinates_totalDegree_le (P : ComplexPlanePoly) :
    (planeToIsotropicCoordinates P).totalDegree ≤ P.totalDegree := by
  exact totalDegree_eval₂Hom_le_of_isHomogeneous_one
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1)]
    (fun c ↦ MvPolynomial.isHomogeneous_C (σ := Fin 2) c)
    inline_Esgk_PlaneIsotropicDegree__planeToIsotropicCoordinates_image_isHomogeneous P

 
theorem isotropicToPlaneCoordinates_totalDegree_le (P : ComplexPlanePoly) :
    (isotropicToPlaneCoordinates P).totalDegree ≤ P.totalDegree := by
  exact totalDegree_eval₂Hom_le_of_isHomogeneous_one
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1,
      MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1]
    (fun c ↦ MvPolynomial.isHomogeneous_C (σ := Fin 2) c)
    inline_Esgk_PlaneIsotropicDegree__isotropicToPlaneCoordinates_image_isHomogeneous P

 
theorem planeToIsotropicCoordinates_totalDegree (P : ComplexPlanePoly) :
    (planeToIsotropicCoordinates P).totalDegree = P.totalDegree := by
  apply Nat.le_antisymm (planeToIsotropicCoordinates_totalDegree_le P)
  have hcomp :
      isotropicToPlaneCoordinates (planeToIsotropicCoordinates P) = P :=
    RingHom.congr_fun
      isotropicToPlaneCoordinates_comp_planeToIsotropicCoordinates P
  calc
    P.totalDegree =
        (isotropicToPlaneCoordinates (planeToIsotropicCoordinates P)).totalDegree := by
      rw [hcomp]
    _ ≤ (planeToIsotropicCoordinates P).totalDegree :=
      isotropicToPlaneCoordinates_totalDegree_le _


end Esgk
end

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology


scoped notation "E" => chartEquiv

 
@[simp] theorem chartEquiv_apply (x : PachDeZeeuw.Algebraic.Point2) : chartEquiv x = (x 0, x 1) := rfl

 
@[simp] theorem chartEquiv_fst (x : PachDeZeeuw.Algebraic.Point2) : (chartEquiv x).1 = x 0 := rfl

 
@[simp] theorem chartEquiv_snd (x : PachDeZeeuw.Algebraic.Point2) : (chartEquiv x).2 = x 1 := rfl

 
@[simp] theorem chartEquiv_symm_apply_zero (z : ℝ × ℝ) :
    (chartEquiv.symm z) 0 = z.1 := rfl

 
@[simp] theorem chartEquiv_symm_apply_one (z : ℝ × ℝ) :
    (chartEquiv.symm z) 1 = z.2 := rfl





end PachDeZeeuw.Algebraic

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna.
-/


namespace Esgk

open PachDeZeeuw


theorem balancedBipartiteIncidenceLowerBound
    {d : ℕ} (X : PreparedBipartiteInput d)
    (h₁ : X.P₁.card ≤ 2 * X.P₂.card)
    (h₂ : X.P₂.card ≤ 2 * X.P₁.card) :
    (X.P₁.card + X.P₂.card) ^ 4 ≤
      64 * (bipartiteDistances X.P₁ X.P₂).card * (auxIncidences X).card := by
  let D : ℕ := (bipartiteDistances X.P₁ X.P₂).card
  let Q : ℕ := (equalDistanceQuadruples X).card
  let I : ℕ := (auxIncidences X).card
  have hLower : X.P₁.card ^ 2 * X.P₂.card ^ 2 ≤ D * Q := by
    simpa [D, Q] using lemma37_equalDistanceQuadruple_lower X
  have hBridge : Q ≤ I := by
    simpa [Q, I] using auxIncidenceBridge d X
  have hLowerI : X.P₁.card ^ 2 * X.P₂.card ^ 2 ≤ D * I :=
    hLower.trans (Nat.mul_le_mul_left D hBridge)
  have hbal :
      (X.P₁.card + X.P₂.card) ^ 4 ≤
        64 * X.P₁.card ^ 2 * X.P₂.card ^ 2 := by
    have ha : X.P₁.card ^ 2 ≤ 2 * X.P₁.card * X.P₂.card := by
      nlinarith [Nat.mul_le_mul_left X.P₁.card h₁]
    have hb : X.P₂.card ^ 2 ≤ 2 * X.P₁.card * X.P₂.card := by
      nlinarith [Nat.mul_le_mul_left X.P₂.card h₂]
    have hsum : (X.P₁.card + X.P₂.card) ^ 2 ≤
        6 * X.P₁.card * X.P₂.card := by nlinarith
    calc
      (X.P₁.card + X.P₂.card) ^ 4 =
          ((X.P₁.card + X.P₂.card) ^ 2) ^ 2 := by ring
      _ ≤ (6 * X.P₁.card * X.P₂.card) ^ 2 := Nat.pow_le_pow_left hsum 2
      _ ≤ 64 * X.P₁.card ^ 2 * X.P₂.card ^ 2 := by nlinarith
  calc
    (X.P₁.card + X.P₂.card) ^ 4 ≤
        64 * X.P₁.card ^ 2 * X.P₂.card ^ 2 := hbal
    _ ≤ 64 * (D * I) := by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 64 hLowerI
    _ = 64 * (bipartiteDistances X.P₁ X.P₂).card * (auxIncidences X).card := by
      simp only [D, I, Nat.mul_assoc]

end Esgk

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem planeRadialQuadratic_isHomogeneous :
    MvPolynomial.IsHomogeneous planeRadialQuadratic 2 := by
  exact
    (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (0 : Fin 2) 2).add
      (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (1 : Fin 2) 2)


theorem planeSquaredDistancePolynomial_eq_radial_linear_constant (a : PachDeZeeuw.Algebraic.Point2) :
    planeSquaredDistancePolynomial a =
      planeRadialQuadratic -
        MvPolynomial.C (2 * a 0) * MvPolynomial.X 0 -
        MvPolynomial.C (2 * a 1) * MvPolynomial.X 1 +
        MvPolynomial.C (a 0 ^ 2 + a 1 ^ 2) := by
  simp only [planeSquaredDistancePolynomial, planeRadialQuadratic, map_add, map_mul, map_pow,
    map_ofNat]
  ring


theorem homogeneousComponent_two_planeSquaredDistancePolynomial (a : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.homogeneousComponent 2 (planeSquaredDistancePolynomial a) =
      planeRadialQuadratic := by
  have hlinear0 :
      MvPolynomial.IsHomogeneous
        (MvPolynomial.C (2 * a 0) * MvPolynomial.X 0 : PlanePoly) 1 :=
    (MvPolynomial.isHomogeneous_X (R := ℝ) (0 : Fin 2)).C_mul _
  have hlinear1 :
      MvPolynomial.IsHomogeneous
        (MvPolynomial.C (2 * a 1) * MvPolynomial.X 1 : PlanePoly) 1 :=
    (MvPolynomial.isHomogeneous_X (R := ℝ) (1 : Fin 2)).C_mul _
  have hconstant :
      MvPolynomial.IsHomogeneous
        (MvPolynomial.C (a 0 ^ 2 + a 1 ^ 2) : PlanePoly) 0 :=
    MvPolynomial.isHomogeneous_C _ _
  rw [planeSquaredDistancePolynomial_eq_radial_linear_constant]
  rw [map_add, map_sub, map_sub]
  rw [MvPolynomial.homogeneousComponent_of_mem planeRadialQuadratic_isHomogeneous,
    MvPolynomial.homogeneousComponent_of_mem hlinear0,
    MvPolynomial.homogeneousComponent_of_mem hlinear1,
    MvPolynomial.homogeneousComponent_of_mem hconstant]
  norm_num

private theorem inline_Esgk_PlaneRadialQuadratic__totalDegree_X_sub_C_sq_le_two (a : ℝ) (k : Fin 2) :
    ((MvPolynomial.X k - MvPolynomial.C a) ^ 2 : PlanePoly).totalDegree ≤ 2 := by
  calc
    ((MvPolynomial.X k - MvPolynomial.C a) ^ 2 : PlanePoly).totalDegree ≤
        2 * (MvPolynomial.X k - MvPolynomial.C a : PlanePoly).totalDegree :=
      MvPolynomial.totalDegree_pow _ _
    _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 (by
      simpa using
        (MvPolynomial.totalDegree_sub
          (MvPolynomial.X k : PlanePoly) (MvPolynomial.C a)))
    _ = 2 := by omega

 
theorem planeSquaredDistancePolynomial_totalDegree_le (a : PachDeZeeuw.Algebraic.Point2) :
    (planeSquaredDistancePolynomial a).totalDegree ≤ 2 := by
  rw [planeSquaredDistancePolynomial]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le (inline_Esgk_PlaneRadialQuadratic__totalDegree_X_sub_C_sq_le_two (a 0) 0)
      (inline_Esgk_PlaneRadialQuadratic__totalDegree_X_sub_C_sq_le_two (a 1) 1))

end Esgk
end

end











section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem planeRadialQuadratic_ne_zero : planeRadialQuadratic ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 2 ↦ if i = 0 then (1 : ℝ) else 0)) hzero
  simp [planeRadialQuadratic] at heval


end Esgk
end

end











section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


@[simp]
theorem affineCircularChart_X_zero (c : ℂ) :
    affineCircularChart c (MvPolynomial.X 0) = 1 := by
  simp [affineCircularChart]

@[simp]
theorem affineCircularChart_X_one (c : ℂ) :
    affineCircularChart c (MvPolynomial.X 1) = MvPolynomial.C c + circularChartU := by
  simp [affineCircularChart]

@[simp]
theorem projectiveCircularChart_X_zero (c : ℂ) :
    projectiveCircularChart c (MvPolynomial.X 0) = 1 := by
  simp [projectiveCircularChart]

@[simp]
theorem projectiveCircularChart_X_one (c : ℂ) :
    projectiveCircularChart c (MvPolynomial.X 1) = MvPolynomial.C c + circularChartU := by
  simp [projectiveCircularChart]

@[simp]
theorem projectiveCircularChart_X_two (c : ℂ) :
    projectiveCircularChart c (MvPolynomial.X 2) = circularChartZ := by
  simp [projectiveCircularChart]


theorem projectiveCircularChart_realPlanePolynomialProjectiveEmbedding
    (c : ℂ) (p : PlanePoly) :
    projectiveCircularChart c (realPlanePolynomialProjectiveEmbedding p) =
      affineCircularChart c p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [realPlanePolynomialProjectiveEmbedding, complexPlanePolynomialEmbedding,
      realToComplexPlanePolynomial, affineCircularChart, projectiveCircularChart]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [realPlanePolynomialProjectiveEmbedding, complexPlanePolynomialEmbedding,
          realToComplexPlanePolynomial]


theorem projectiveCircularChart_planeHomogenizedLayer
    (c : ℂ) (D d : ℕ) (p : PlanePoly) :
    projectiveCircularChart c (planeHomogenizedLayer D d p) =
      circularChartZ ^ (D - d) *
        affineCircularChart c (MvPolynomial.homogeneousComponent d p) := by
  rw [planeHomogenizedLayer, map_mul, map_pow,
    projectiveCircularChart_realPlanePolynomialProjectiveEmbedding]
  simp [projectivePlaneZ, mul_comm]


theorem projectiveCircularChart_planeHomogenization
    (c : ℂ) (D : ℕ) (p : PlanePoly) :
    projectiveCircularChart c (planeHomogenization D p) =
      ∑ d ∈ Finset.range (D + 1),
        circularChartZ ^ (D - d) *
          affineCircularChart c (MvPolynomial.homogeneousComponent d p) := by
  simp only [planeHomogenization, map_sum, projectiveCircularChart_planeHomogenizedLayer]


end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw










theorem encodedAuxPoint_injective : Function.Injective encodedAuxPoint := by
  intro p q hpq
  have hfirst : decodedAuxFirst (encodedAuxPoint p) =
      decodedAuxFirst (encodedAuxPoint q) := congrArg decodedAuxFirst hpq
  have hsecond : decodedAuxSecond (encodedAuxPoint p) =
      decodedAuxSecond (encodedAuxPoint q) := congrArg decodedAuxSecond hpq
  exact Prod.ext (by simpa using hfirst) (by simpa using hsecond)


























namespace AuxiliaryIncidenceDeletionCertificate


end AuxiliaryIncidenceDeletionCertificate








end Esgk

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


private theorem inline_Esgk_PlaneCircularLocalOrderDegree__homogeneousComponent_totalDegree_ne_zero
    {G : PlanePoly} (hG : G ≠ 0) :
    MvPolynomial.homogeneousComponent G.totalDegree G ≠ 0 := by
  have hsupp : G.support.Nonempty := MvPolynomial.support_nonempty.mpr hG
  have hsup := Finset.sup_mem_of_nonempty
    (f := fun d : Fin 2 →₀ ℕ => d.sum fun _ e => e) hsupp
  rw [← MvPolynomial.totalDegree] at hsup
  rcases hsup with ⟨d, hd, hdegree⟩
  rw [← MvPolynomial.support_nonempty]
  refine ⟨d, ?_⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_homogeneousComponent]
  have hdegree' : Finsupp.degree d = G.totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using hdegree
  simp only [hdegree', ↓reduceIte]
  exact MvPolynomial.mem_support_iff.mp hd

 
theorem realPlaneInfinityRestriction_ne_zero {G : PlanePoly} (hG : G ≠ 0) :
    realPlaneInfinityRestriction G ≠ 0 := by
  let q : MvPolynomial (Fin 2) ℝ :=
    (MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1))
      (MvPolynomial.homogeneousComponent G.totalDegree G)
  have hqhom : q.IsHomogeneous G.totalDegree := by
    exact
      (MvPolynomial.homogeneousComponent_isHomogeneous G.totalDegree G).rename_isHomogeneous
  have hdehom : MvPolynomial.aeval ![Polynomial.X, 1] q =
      realPlaneInfinityRestriction G := by
    dsimp only [q]
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename]
    change (MvPolynomial.aeval (![(Polynomial.X : Polynomial ℝ), 1] ∘
        (Equiv.swap (0 : Fin 2) 1)))
        (MvPolynomial.homogeneousComponent G.totalDegree G) =
      (MvPolynomial.aeval ![(1 : Polynomial ℝ), Polynomial.X])
        (MvPolynomial.homogeneousComponent G.totalDegree G)
    have hvec : (![(Polynomial.X : Polynomial ℝ), 1] ∘
        (Equiv.swap (0 : Fin 2) 1)) = ![(1 : Polynomial ℝ), Polynomial.X] := by
      funext i
      fin_cases i <;> simp
    rw [hvec]
  intro hzero
  have hqzero : q = 0 := by
    rw [← Polynomial.homogenize_eq_of_isHomogeneous hqhom hdehom, hzero]
    simp
  apply inline_Esgk_PlaneCircularLocalOrderDegree__homogeneousComponent_totalDegree_ne_zero hG
  exact (MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1)).injective
    (by simpa only [map_zero] using hqzero)

 
theorem complexPlaneInfinityRestriction_ne_zero {G : PlanePoly} (hG : G ≠ 0) :
    complexPlaneInfinityRestriction G ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr
    (realPlaneInfinityRestriction_ne_zero hG)

 
theorem realPlaneInfinityRestriction_natDegree_le (G : PlanePoly) :
    (realPlaneInfinityRestriction G).natDegree ≤ G.totalDegree := by
  change (MvPolynomial.aeval ![(1 : Polynomial ℝ), Polynomial.X]
    (MvPolynomial.homogeneousComponent G.totalDegree G)).natDegree ≤ G.totalDegree
  simpa using MvPolynomial.aeval_natDegree_le
    (m := G.totalDegree) (n := 1)
    (MvPolynomial.homogeneousComponent G.totalDegree G)
    (MvPolynomial.homogeneousComponent_isHomogeneous G.totalDegree G).totalDegree_le
    ![(1 : Polynomial ℝ), Polynomial.X]
    (fun i ↦ by fin_cases i <;> simp)

 
theorem complexPlaneInfinityRestriction_natDegree_le (G : PlanePoly) :
    (complexPlaneInfinityRestriction G).natDegree ≤ G.totalDegree :=
  Polynomial.natDegree_map_le.trans (realPlaneInfinityRestriction_natDegree_le G)


theorem projectiveInfinityRestriction_realPlanePolynomialProjectiveEmbedding (p : PlanePoly) :
    projectiveInfinityRestriction (realPlanePolynomialProjectiveEmbedding p) =
      (realPlaneOneXRestriction p).map Complex.ofRealHom := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp [projectiveInfinityRestriction, realPlanePolynomialProjectiveEmbedding,
        complexPlanePolynomialEmbedding, realToComplexPlanePolynomial,
        realPlaneOneXRestriction]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [projectiveInfinityRestriction, realPlanePolynomialProjectiveEmbedding,
          complexPlanePolynomialEmbedding, realToComplexPlanePolynomial,
          realPlaneOneXRestriction]


theorem projectiveInfinityRestriction_planeHomogenization (D : ℕ) (G : PlanePoly) :
    projectiveInfinityRestriction (planeHomogenization D G) =
      (realPlaneOneXRestriction (MvPolynomial.homogeneousComponent D G)).map
        Complex.ofRealHom := by
  rw [planeHomogenization, map_sum, Finset.sum_eq_single D]
  · simp [planeHomogenizedLayer,
      projectiveInfinityRestriction_realPlanePolynomialProjectiveEmbedding]
  · intro d hd hdD
    have hdle : d ≤ D := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hd
    have hdlt : d < D := lt_of_le_of_ne hdle hdD
    have hpow : D - d ≠ 0 := Nat.sub_ne_zero_of_lt hdlt
    simp [planeHomogenizedLayer, projectiveInfinityRestriction, projectivePlaneZ, hpow]
  · simp

 
theorem projectiveInfinityRestriction_planeHomogenization_totalDegree (G : PlanePoly) :
    projectiveInfinityRestriction (planeHomogenization G.totalDegree G) =
      complexPlaneInfinityRestriction G := by
  exact projectiveInfinityRestriction_planeHomogenization G.totalDegree G


theorem chartInfinityRestriction_coeff (p : CircularChartPoly) (n : ℕ) :
    (chartInfinityRestriction p).coeff n =
      MvPolynomial.coeff (Finsupp.cons n (0 : Fin 1 →₀ ℕ)) p := by
  change (Polynomial.map
    (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
    ((MvPolynomial.finSuccEquiv ℂ 1) p)).coeff n =
      MvPolynomial.coeff (Finsupp.cons n (0 : Fin 1 →₀ ℕ)) p
  rw [Polynomial.coeff_map]
  change MvPolynomial.coeff 0 (((MvPolynomial.finSuccEquiv ℂ 1) p).coeff n) =
    MvPolynomial.coeff (Finsupp.cons n (0 : Fin 1 →₀ ℕ)) p
  exact MvPolynomial.finSuccEquiv_coeff_coeff 0 p n

@[simp]
theorem chartInfinityRestriction_C (c : ℂ) :
    chartInfinityRestriction (MvPolynomial.C c) = Polynomial.C c := by
  change Polynomial.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
      ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.C c)) = Polynomial.C c
  rw [MvPolynomial.finSuccEquiv_apply]
  simp

@[simp]
theorem chartInfinityRestriction_circularChartU :
    chartInfinityRestriction circularChartU = Polynomial.X := by
  change Polynomial.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
      ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.X 0)) = Polynomial.X
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

@[simp]
theorem chartInfinityRestriction_circularChartZ :
    chartInfinityRestriction circularChartZ = 0 := by
  change Polynomial.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
      ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.X 1)) = 0
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp


theorem chartInfinityRestriction_projectiveCircularChart
    (c : ℂ) (P : ProjectivePlanePoly) :
    chartInfinityRestriction (projectiveCircularChart c P) =
      (projectiveInfinityRestriction P).comp (Polynomial.X + Polynomial.C c) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [projectiveCircularChart, projectiveInfinityRestriction]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [projectiveCircularChart, projectiveInfinityRestriction, add_comm]


theorem chartInfinityRestriction_projectiveCircularChart_planeHomogenization
    (c : ℂ) (G : PlanePoly) :
    chartInfinityRestriction
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) =
      (complexPlaneInfinityRestriction G).comp (Polynomial.X + Polynomial.C c) := by
  rw [chartInfinityRestriction_projectiveCircularChart,
    projectiveInfinityRestriction_planeHomogenization_totalDegree]


private theorem inline_Esgk_PlaneCircularLocalOrderDegree__localOrder_toNat_le_rootMultiplicity_of_chartInfinityRestriction_eq
    (c : ℂ) (F : CircularChartPoly) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hrestrict :
      chartInfinityRestriction F = p.comp (Polynomial.X + Polynomial.C c)) :
    (MvPolynomial.localOrder F).toNat ≤ p.rootMultiplicity c := by
  let q := p.comp (Polynomial.X + Polynomial.C c)
  have hq : q ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hp
  have hcoeffq : q.coeff q.natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq
  have hcoeff :
      MvPolynomial.coeff
        (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ)) F ≠ 0 := by
    rw [← chartInfinityRestriction_coeff, hrestrict]
    exact hcoeffq
  have hcoeffSeries :
      MvPowerSeries.coeff
        (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ))
        (F : MvPowerSeries (Fin 2) ℂ) ≠ 0 := by
    simpa using hcoeff
  have hdegree :
      Finsupp.degree (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ)) =
        q.natTrailingDegree := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.cons_zero]
    change q.natTrailingDegree +
      (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ)) (0 : Fin 1).succ =
        q.natTrailingDegree
    rw [Finsupp.cons_succ]
    simp
  have horder : MvPolynomial.localOrder F ≤ (q.natTrailingDegree : ℕ∞) := by
    simpa [MvPolynomial.localOrder, hdegree] using
      (MvPowerSeries.order_le hcoeffSeries)
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  exact ENat.toNat_le_of_le_coe horder


theorem planeCircularLocalOrder_le_rootMultiplicity
    (c : ℂ) {G : PlanePoly} (hG : G ≠ 0) :
    planeCircularLocalOrder c G ≤
      (complexPlaneInfinityRestriction G).rootMultiplicity c := by
  exact inline_Esgk_PlaneCircularLocalOrderDegree__localOrder_toNat_le_rootMultiplicity_of_chartInfinityRestriction_eq
    c (projectiveCircularChart c (planeHomogenization G.totalDegree G))
    (complexPlaneInfinityRestriction G) (complexPlaneInfinityRestriction_ne_zero hG)
    (chartInfinityRestriction_projectiveCircularChart_planeHomogenization c G)


private theorem inline_Esgk_PlaneCircularLocalOrderDegree__multiset_count_add_count_le_card_of_ne
    {R : Type*} [DecidableEq R] {a b : R} (hab : a ≠ b) (s : Multiset R) :
    s.count a + s.count b ≤ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      by_cases hxa : x = a
      · subst x
        simp only [Multiset.card_cons, Multiset.count_cons, if_neg (Ne.symm hab), add_zero,
          if_true]
        omega
      · by_cases hxb : x = b
        · subst x
          simp only [Multiset.card_cons, Multiset.count_cons, if_neg hab, add_zero, if_true]
          omega
        · have hax : a ≠ x := Ne.symm hxa
          have hbx : b ≠ x := Ne.symm hxb
          simp only [Multiset.card_cons, Multiset.count_cons, if_neg hax,
            if_neg hbx, add_zero]
          omega

 
theorem Polynomial.rootMultiplicity_add_rootMultiplicity_le_natDegree_of_ne
    {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (p : Polynomial R) {a b : R} (hab : a ≠ b) :
    p.rootMultiplicity a + p.rootMultiplicity b ≤ p.natDegree := by
  rw [← Polynomial.count_roots p, ← Polynomial.count_roots p]
  exact (inline_Esgk_PlaneCircularLocalOrderDegree__multiset_count_add_count_le_card_of_ne hab p.roots).trans
    (Polynomial.card_roots' p)


end Esgk
end

end














section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace MvPolynomial

 
theorem localOrder_map_star {σ : Type*} (p : MvPolynomial σ ℂ) :
    localOrder (map (starRingEnd ℂ) p) = localOrder p := by
  have hcoe :
      ((map (starRingEnd ℂ) p : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) =
        MvPowerSeries.map (starRingEnd ℂ) (p : MvPowerSeries σ ℂ) := by
    ext d
    exact MvPolynomial.coeff_map (starRingEnd ℂ) p d
  rw [localOrder, localOrder, hcoe]
  apply le_antisymm
  · have h := MvPowerSeries.le_order_map (starRingEnd ℂ)
      (φ := MvPowerSeries.map (starRingEnd ℂ) (p : MvPowerSeries σ ℂ))
    have hinvolution :
        MvPowerSeries.map (starRingEnd ℂ)
            (MvPowerSeries.map (starRingEnd ℂ) (p : MvPowerSeries σ ℂ)) = p := by
      ext d
      simp
    rw [hinvolution] at h
    exact h
  · exact MvPowerSeries.le_order_map (starRingEnd ℂ)

end MvPolynomial

namespace Esgk

open PachDeZeeuw.Algebraic

private theorem inline_Esgk_PlaneCircularLocalOrderConjugation__realPlanePolynomialProjectiveEmbedding_map_star (p : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ) (realPlanePolynomialProjectiveEmbedding p) =
      realPlanePolynomialProjectiveEmbedding p := by
  change
    MvPolynomial.map (starRingEnd ℂ)
        (MvPolynomial.rename Fin.castSucc (MvPolynomial.map Complex.ofRealHom p)) =
      MvPolynomial.rename Fin.castSucc (MvPolynomial.map Complex.ofRealHom p)
  rw [MvPolynomial.map_rename, MvPolynomial.map_map]
  have hcomp : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext r
    simp
  rw [hcomp]

private theorem inline_Esgk_PlaneCircularLocalOrderConjugation__planeHomogenization_map_star (D : ℕ) (G : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ) (planeHomogenization D G) = planeHomogenization D G := by
  simp only [planeHomogenization, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp [planeHomogenizedLayer, inline_Esgk_PlaneCircularLocalOrderConjugation__realPlanePolynomialProjectiveEmbedding_map_star,
    projectivePlaneZ]

private theorem inline_Esgk_PlaneCircularLocalOrderConjugation__projectiveCircularChart_map_star (c : ℂ) (P : ProjectivePlanePoly) :
    MvPolynomial.map (starRingEnd ℂ) (projectiveCircularChart c P) =
      projectiveCircularChart ((starRingEnd ℂ) c)
        (MvPolynomial.map (starRingEnd ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [projectiveCircularChart]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [projectiveCircularChart, circularChartU, circularChartZ]


theorem projectiveCircularChart_planeHomogenization_map_star (c : ℂ) (G : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ)
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) =
      projectiveCircularChart ((starRingEnd ℂ) c)
        (planeHomogenization G.totalDegree G) := by
  rw [inline_Esgk_PlaneCircularLocalOrderConjugation__projectiveCircularChart_map_star, inline_Esgk_PlaneCircularLocalOrderConjugation__planeHomogenization_map_star]

 
theorem projectiveCircularChartI_planeHomogenization_map_star (G : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ)
        (projectiveCircularChartI (planeHomogenization G.totalDegree G)) =
      projectiveCircularChartJ (planeHomogenization G.totalDegree G) := by
  simpa [projectiveCircularChartI, projectiveCircularChartJ, Complex.conj_I] using
    projectiveCircularChart_planeHomogenization_map_star Complex.I G


theorem planeCircularLocalOrderI_eq_planeCircularLocalOrderJ (G : PlanePoly) :
    planeCircularLocalOrderI G = planeCircularLocalOrderJ G := by
  change
    (MvPolynomial.localOrder
        (projectiveCircularChartI (planeHomogenization G.totalDegree G))).toNat =
      (MvPolynomial.localOrder
        (projectiveCircularChartJ (planeHomogenization G.totalDegree G))).toNat
  have h := MvPolynomial.localOrder_map_star
    (projectiveCircularChartI (planeHomogenization G.totalDegree G))
  rw [projectiveCircularChartI_planeHomogenization_map_star] at h
  exact congrArg ENat.toNat h.symm

end Esgk
end

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem IsMaximallyCircular.order_sum_eq_totalDegree
    {G : PlanePoly} (hG : IsMaximallyCircular G) :
    planeCircularLocalOrderI G + planeCircularLocalOrderJ G = G.totalDegree := by
  rcases hG with ⟨hI, hJ⟩
  omega


variable {n : ℕ}


end Esgk
end

end























section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two :
    (MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2 = 1 := by
  change MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C (2 : ℂ) = MvPolynomial.C 1
  rw [← map_mul]
  norm_num

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_I_sq :
    (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]


theorem isotropicAffineCircularChartI_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    isotropicAffineCircularChartI
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartI G := by
  change
    (((isotropicAffineCircularChartI.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartI G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [isotropicAffineCircularChartI, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [isotropicAffineCircularChartI, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two
    · calc
        _ = (MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_I_sq]
          ring
        _ = MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two, mul_one]


theorem isotropicAffineCircularChartJ_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    isotropicAffineCircularChartJ
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartJ G := by
  change
    (((isotropicAffineCircularChartJ.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartJ G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [isotropicAffineCircularChartJ, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [isotropicAffineCircularChartJ, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two
    · calc
        _ = (-MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_I_sq]
          ring
        _ = -MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two, mul_one]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__planeToIsotropicCoordinates_isHomogeneous
    {d : ℕ} {P : ComplexPlanePoly} (hP : P.IsHomogeneous d) :
    (planeToIsotropicCoordinates P).IsHomogeneous d := by
  change
    (MvPolynomial.eval₂ (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
      ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * Complex.I)) *
          (MvPolynomial.X 0 - MvPolynomial.X 1)] P).IsHomogeneous d
  have h := hP.eval₂
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1)]
    (fun c ↦ MvPolynomial.isHomogeneous_C (Fin 2) c)
    (fun i ↦ by
      fin_cases i
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).add
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).sub
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _)
  rw [Nat.one_mul] at h
  exact h

 
theorem planeToIsotropicCoordinates_homogeneousComponent
    (d : ℕ) (P : ComplexPlanePoly) :
    planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) =
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) := by
  classical
  by_cases hd : d ≤ P.totalDegree
  · have hsum :
        ∑ k ∈ Finset.range (P.totalDegree + 1),
            planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P) =
          planeToIsotropicCoordinates P := by
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    have himage (k : ℕ) :
        (planeToIsotropicCoordinates
          (MvPolynomial.homogeneousComponent k P)).IsHomogeneous k :=
      inline_Esgk_MaximallyCircularIsotropicBidegree__planeToIsotropicCoordinates_isHomogeneous
        (MvPolynomial.homogeneousComponent_isHomogeneous k P)
    symm
    calc
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) =
          MvPolynomial.homogeneousComponent d
            (∑ k ∈ Finset.range (P.totalDegree + 1),
              planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        rw [hsum]
      _ = ∑ k ∈ Finset.range (P.totalDegree + 1),
          MvPolynomial.homogeneousComponent d
            (planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        simp only [map_sum]
      _ = planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) := by
        simp_rw [MvPolynomial.homogeneousComponent_of_mem (himage _)]
        simp [hd]
  · have hPd : P.totalDegree < d := by omega
    have hTd : (planeToIsotropicCoordinates P).totalDegree < d := by
      rw [planeToIsotropicCoordinates_totalDegree]
      exact hPd
    rw [MvPolynomial.homogeneousComponent_eq_zero d P hPd, map_zero,
      MvPolynomial.homogeneousComponent_eq_zero d _ hTd]

 
theorem realToComplexPlanePolynomial_homogeneousComponent
    (d : ℕ) (G : PlanePoly) :
    realToComplexPlanePolynomial (MvPolynomial.homogeneousComponent d G) =
      MvPolynomial.homogeneousComponent d (realToComplexPlanePolynomial G) := by
  ext e
  simp only [realToComplexPlanePolynomial, MvPolynomial.coeff_map,
    MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp


theorem projectiveCircularChartI_planeHomogenization_eq_isotropic
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartI (planeHomogenization D G) =
      isotropicHomogenizedCircularChartI D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartI, projectiveCircularChart_planeHomogenization]
  rw [isotropicHomogenizedCircularChartI]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartI (MvPolynomial.homogeneousComponent d G) = _
  rw [← isotropicAffineCircularChartI_planeToIsotropic_realToComplex]
  congr 1
  rw [realToComplexPlanePolynomial_homogeneousComponent,
    planeToIsotropicCoordinates_homogeneousComponent]

 
theorem projectiveCircularChartJ_planeHomogenization_eq_isotropic
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartJ (planeHomogenization D G) =
      isotropicHomogenizedCircularChartJ D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartJ, projectiveCircularChart_planeHomogenization]
  rw [isotropicHomogenizedCircularChartJ]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartJ (MvPolynomial.homogeneousComponent d G) = _
  rw [← isotropicAffineCircularChartJ_planeToIsotropic_realToComplex]
  congr 1
  rw [realToComplexPlanePolynomial_homogeneousComponent,
    planeToIsotropicCoordinates_homogeneousComponent]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__homogenized_eval₂_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (A B : CircularChartPoly)
    (hdegree : Q.totalDegree ≤ D) :
    (∑ d ∈ Finset.range (D + 1),
      circularChartZ ^ (D - d) *
        MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly) ![A, B]
          (MvPolynomial.homogeneousComponent d Q)) =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  classical
  calc
    _ = ∑ d ∈ Finset.range (D + 1),
        ∑ e ∈ Q.support with e.degree = d,
          MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
            circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hedegree : e.degree = d := (Finset.mem_filter.mp he).2
      rw [MvPolynomial.eval₂Hom_monomial]
      rw [hedegree]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two]
      ring
    _ = ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_fiberwise_of_maps_to
      intro e he
      rw [Finsupp.degree_eq_sum]
      simp only [Finset.mem_range, Nat.lt_add_one_iff]
      calc
        ∑ i, e i = e.sum (fun _ a ↦ a) :=
          (Finsupp.sum_fintype e (fun _ a ↦ a) (fun _ ↦ rfl)).symm
        _ ≤ D := (MvPolynomial.le_totalDegree he).trans hdegree

 
theorem isotropicHomogenizedCircularChartI_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    isotropicHomogenizedCircularChartI D Q =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) *
          (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  rw [isotropicHomogenizedCircularChartI]
  exact inline_Esgk_MaximallyCircularIsotropicBidegree__homogenized_eval₂_eq_support_sum D Q _ _ hdegree

 
theorem isotropicHomogenizedCircularChartJ_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    isotropicHomogenizedCircularChartJ D Q =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) *
          (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  rw [isotropicHomogenizedCircularChartJ]
  exact inline_Esgk_MaximallyCircularIsotropicBidegree__homogenized_eval₂_eq_support_sum D Q _ _ hdegree


@[simp]
theorem isotropicILeadingExponent_zero (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicILeadingExponent D e 0 = e 0 := by
  simp [isotropicILeadingExponent]

@[simp]
theorem isotropicILeadingExponent_one (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicILeadingExponent D e 1 = D - e.degree := by
  simp [isotropicILeadingExponent]

@[simp]
theorem isotropicJLeadingExponent_zero (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicJLeadingExponent D e 0 = e 1 := by
  simp [isotropicJLeadingExponent]

@[simp]
theorem isotropicJLeadingExponent_one (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicJLeadingExponent D e 1 = D - e.degree := by
  simp [isotropicJLeadingExponent]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add (e : Fin 2 →₀ ℕ) :
    e.degree = e 0 + e 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicILeadingExponent_degree
    (D : ℕ) (e : Fin 2 →₀ ℕ) (he : e.degree ≤ D) :
    (isotropicILeadingExponent D e).degree = D - e 1 := by
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at he
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add, isotropicILeadingExponent_zero,
    isotropicILeadingExponent_one, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e]
  omega

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicJLeadingExponent_degree
    (D : ℕ) (e : Fin 2 →₀ ℕ) (he : e.degree ≤ D) :
    (isotropicJLeadingExponent D e).degree = D - e 0 := by
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at he
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add, isotropicJLeadingExponent_zero,
    isotropicJLeadingExponent_one, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e]
  omega

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support
    {P : CircularChartPoly} {m : Fin 2 →₀ ℕ} {i : Fin 2} {n : ℕ}
    (hm : m ∈ P.support) (hdvd : MvPolynomial.X i ^ n ∣ P) : n ≤ m i := by
  rcases hdvd with ⟨R, rfl⟩
  have hcoeff : MvPolynomial.coeff m (MvPolynomial.X i ^ n * R) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_monomial_mul'] at hcoeff
  split at hcoeff
  next hle =>
    have := hle i
    simpa using this
  next hnot => exact (hcoeff rfl).elim

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartITerm_degreeOf_one_le
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.degreeOf 1 (isotropicCircularChartITerm D e c) ≤ D - e.degree := by
  have hU : MvPolynomial.degreeOf 1
      (MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    simpa [circularChartU, MvPolynomial.degreeOf_X, show (1 : Fin 2) ≠ 0 by decide]
      using MvPolynomial.degreeOf_mul_le 1
        (MvPolynomial.C Complex.I : CircularChartPoly) circularChartU
  have hV : MvPolynomial.degreeOf 1
      (2 - MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    exact (MvPolynomial.degreeOf_sub_le 1 (2 : CircularChartPoly)
      (MvPolynomial.C Complex.I * circularChartU)).trans
        (max_le (by
          change MvPolynomial.degreeOf 1
            (MvPolynomial.C (2 : ℂ) : CircularChartPoly) ≤ 0
          simp) hU)
  have hUpow := MvPolynomial.degreeOf_pow_le 1
    (MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 0)
  have hVpow := MvPolynomial.degreeOf_pow_le 1
    (2 - MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 1)
  have hleft := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c : CircularChartPoly)
    ((MvPolynomial.C Complex.I * circularChartU) ^ e 0)
  have hmiddle := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0)
    ((2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1)
  have hZpow := MvPolynomial.degreeOf_pow_le 1 circularChartZ (D - e.degree)
  have hall := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1)
    (circularChartZ ^ (D - e.degree))
  have hUpowZero : MvPolynomial.degreeOf 1
      ((MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hU
    simpa [hU] using hUpow
  have hVpowZero : MvPolynomial.degreeOf 1
      ((2 - MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 1) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hV
    simpa [hV] using hVpow
  have hleftZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero] at hUpowZero ⊢
    simpa [hUpowZero] using hleft
  have hmiddleZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
        (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1) ≤ 0 := by
    rw [Nat.le_zero] at hleftZero hVpowZero ⊢
    simpa [hleftZero, hVpowZero] using hmiddle
  have hZpowBound : MvPolynomial.degreeOf 1
      (circularChartZ ^ (D - e.degree)) ≤ D - e.degree := by
    simpa [circularChartZ] using hZpow
  change MvPolynomial.degreeOf 1
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) ≤ D - e.degree
  simpa using hall.trans (Nat.add_le_add hmiddleZero hZpowBound)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coordinate_bounds
    (D : ℕ) (e m : Fin 2 →₀ ℕ) (c : ℂ)
    (hm : m ∈ (isotropicCircularChartITerm D e c).support) :
    e 0 ≤ m 0 ∧ m 1 = D - e.degree := by
  have hUdvd : circularChartU ^ e 0 ∣ isotropicCircularChartITerm D e c := by
    refine ⟨MvPolynomial.C c * MvPolynomial.C (Complex.I ^ e 0) *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree), ?_⟩
    rw [isotropicCircularChartITerm, mul_pow, ← map_pow]
    ring
  have hZdvd : circularChartZ ^ (D - e.degree) ∣ isotropicCircularChartITerm D e c := by
    refine ⟨MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1, ?_⟩
    rw [isotropicCircularChartITerm]
    ring
  have hzero : e 0 ≤ m 0 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartU] using hUdvd
  have honeLower : D - e.degree ≤ m 1 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartZ] using hZdvd
  have honeUpper : m 1 ≤ D - e.degree :=
    (MvPolynomial.le_degreeOf_of_mem_support 1 hm).trans
      (inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartITerm_degreeOf_one_le D e c)
  exact ⟨hzero, Nat.le_antisymm honeUpper honeLower⟩

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coeff_leading
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.coeff (isotropicILeadingExponent D e)
        (isotropicCircularChartITerm D e c) =
      c * Complex.I ^ e 0 * (2 : ℂ) ^ e 1 := by
  classical
  rw [isotropicCircularChartITerm]
  change MvPolynomial.coeff
    (Finsupp.single 0 (e 0) + Finsupp.single 1 (D - e.degree))
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) = _
  rw [circularChartZ, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_mul_monomial, mul_one]
  rw [mul_pow, ← map_pow, circularChartU, MvPolynomial.X_pow_eq_monomial]
  simp only [← mul_assoc, MvPolynomial.C_mul_monomial]
  rw [MvPolynomial.coeff_monomial_mul']
  simp only [le_refl, if_true, tsub_self]
  rw [← MvPolynomial.constantCoeff_eq, map_pow]
  have htwo : MvPolynomial.constantCoeff (2 : CircularChartPoly) = (2 : ℂ) := by
    change MvPolynomial.constantCoeff
      (MvPolynomial.C (2 : ℂ) : CircularChartPoly) = (2 : ℂ)
    simp
  rw [map_sub, map_mul, htwo, MvPolynomial.constantCoeff_C,
    MvPolynomial.constantCoeff_X, mul_zero, sub_zero]
  ring

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartI_coeff_extremal
    (D : ℕ) (Q : ComplexPlanePoly) (e : Fin 2 →₀ ℕ)
    (hdegree : Q.totalDegree ≤ D) (he : e ∈ Q.support)
    (hmax : ∀ f ∈ Q.support, f 1 ≤ e 1) :
    MvPolynomial.coeff (isotropicILeadingExponent D e)
        (isotropicHomogenizedCircularChartI D Q) =
      MvPolynomial.coeff e Q * Complex.I ^ e 0 * (2 : ℂ) ^ e 1 := by
  classical
  rw [isotropicHomogenizedCircularChartI_eq_support_sum D Q hdegree]
  rw [MvPolynomial.coeff_sum]
  calc
    _ = MvPolynomial.coeff (isotropicILeadingExponent D e)
        (MvPolynomial.C (MvPolynomial.coeff e Q) *
          (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree)) := by
      apply Finset.sum_eq_single e
      · intro f hf hfe
        have hfzero : MvPolynomial.coeff (isotropicILeadingExponent D e)
            (isotropicCircularChartITerm D f (MvPolynomial.coeff f Q)) = 0 := by
          by_contra hcoeff
          have hmem : isotropicILeadingExponent D e ∈
              (isotropicCircularChartITerm D f (MvPolynomial.coeff f Q)).support :=
            MvPolynomial.mem_support_iff.mpr hcoeff
          obtain ⟨hzero, hone⟩ :=
            inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coordinate_bounds D f
              (isotropicILeadingExponent D e) (MvPolynomial.coeff f Q) hmem
          have hfdegree : f.degree ≤ D :=
            (MvPolynomial.le_totalDegree hf).trans hdegree
          have hedegree : e.degree ≤ D :=
            (MvPolynomial.le_totalDegree he).trans hdegree
          have hdegreeEq : f.degree = e.degree := by
            rw [isotropicILeadingExponent_one] at hone
            omega
          have honeLe : f 1 ≤ e 1 := hmax f hf
          rw [isotropicILeadingExponent_zero] at hzero
          have hzeroEq : f 0 = e 0 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          have honeEq : f 1 = e 1 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          apply hfe
          apply Finsupp.ext
          intro i
          fin_cases i
          · exact hzeroEq
          · exact honeEq
        simpa [isotropicCircularChartITerm] using hfzero
      · intro hnot
        exact (hnot he).elim
    _ = _ := by
      simpa [isotropicCircularChartITerm] using
        inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coeff_leading D e (MvPolynomial.coeff e Q)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartJTerm_degreeOf_one_le
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.degreeOf 1 (isotropicCircularChartJTerm D e c) ≤ D - e.degree := by
  have hU : MvPolynomial.degreeOf 1
      (MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    simpa [circularChartU, MvPolynomial.degreeOf_X, show (1 : Fin 2) ≠ 0 by decide]
      using MvPolynomial.degreeOf_mul_le 1
        (MvPolynomial.C Complex.I : CircularChartPoly) circularChartU
  have hA : MvPolynomial.degreeOf 1
      (2 + MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    exact (MvPolynomial.degreeOf_add_le 1 (2 : CircularChartPoly)
      (MvPolynomial.C Complex.I * circularChartU)).trans
        (max_le (by
          change MvPolynomial.degreeOf 1
            (MvPolynomial.C (2 : ℂ) : CircularChartPoly) ≤ 0
          simp) hU)
  have hB : MvPolynomial.degreeOf 1
      (-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    have hmul := MvPolynomial.degreeOf_mul_le 1
      (-MvPolynomial.C Complex.I : CircularChartPoly) circularChartU
    simpa [circularChartU, MvPolynomial.degreeOf_X,
      show (1 : Fin 2) ≠ 0 by decide] using hmul
  have hApow := MvPolynomial.degreeOf_pow_le 1
    (2 + MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 0)
  have hBpow := MvPolynomial.degreeOf_pow_le 1
    (-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 1)
  have hleft := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c : CircularChartPoly)
    ((2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0)
  have hmiddle := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0)
    ((-MvPolynomial.C Complex.I * circularChartU) ^ e 1)
  have hZpow := MvPolynomial.degreeOf_pow_le 1 circularChartZ (D - e.degree)
  have hall := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1)
    (circularChartZ ^ (D - e.degree))
  have hApowZero : MvPolynomial.degreeOf 1
      ((2 + MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hA
    simpa [hA] using hApow
  have hBpowZero : MvPolynomial.degreeOf 1
      ((-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 1) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hU
    simpa [hU] using hBpow
  have hleftZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero] at hApowZero ⊢
    simpa [hApowZero] using hleft
  have hmiddleZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
        (-MvPolynomial.C Complex.I * circularChartU) ^ e 1) ≤ 0 := by
    simpa using hmiddle.trans (Nat.add_le_add hleftZero hBpowZero)
  have hZpowBound : MvPolynomial.degreeOf 1
      (circularChartZ ^ (D - e.degree)) ≤ D - e.degree := by
    simpa [circularChartZ] using hZpow
  change MvPolynomial.degreeOf 1
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) ≤ D - e.degree
  simpa using hall.trans (Nat.add_le_add hmiddleZero hZpowBound)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coordinate_bounds
    (D : ℕ) (e m : Fin 2 →₀ ℕ) (c : ℂ)
    (hm : m ∈ (isotropicCircularChartJTerm D e c).support) :
    e 1 ≤ m 0 ∧ m 1 = D - e.degree := by
  have hUdvd : circularChartU ^ e 1 ∣ isotropicCircularChartJTerm D e c := by
    refine ⟨MvPolynomial.C c * MvPolynomial.C ((-Complex.I) ^ e 1) *
      (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      circularChartZ ^ (D - e.degree), ?_⟩
    rw [isotropicCircularChartJTerm, mul_pow, ← map_neg, ← map_pow]
    ring
  have hZdvd : circularChartZ ^ (D - e.degree) ∣ isotropicCircularChartJTerm D e c := by
    refine ⟨MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1, ?_⟩
    rw [isotropicCircularChartJTerm]
    ring
  have hzero : e 1 ≤ m 0 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartU] using hUdvd
  have honeLower : D - e.degree ≤ m 1 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartZ] using hZdvd
  have honeUpper : m 1 ≤ D - e.degree :=
    (MvPolynomial.le_degreeOf_of_mem_support 1 hm).trans
      (inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartJTerm_degreeOf_one_le D e c)
  exact ⟨hzero, Nat.le_antisymm honeUpper honeLower⟩

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coeff_leading
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.coeff (isotropicJLeadingExponent D e)
        (isotropicCircularChartJTerm D e c) =
      c * (-Complex.I) ^ e 1 * (2 : ℂ) ^ e 0 := by
  classical
  rw [isotropicCircularChartJTerm]
  change MvPolynomial.coeff
    (Finsupp.single 0 (e 1) + Finsupp.single 1 (D - e.degree))
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) = _
  rw [circularChartZ, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_mul_monomial, mul_one]
  have hneg : (-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) =
      MvPolynomial.C (-Complex.I) * circularChartU := by
    rw [map_neg]
  rw [hneg, mul_pow, ← map_pow, circularChartU, MvPolynomial.X_pow_eq_monomial]
  have hreorder :
      (MvPolynomial.C c : CircularChartPoly) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X (0 : Fin 2)) ^ e 0 *
          (MvPolynomial.C ((-Complex.I) ^ e 1) *
            MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1)) 1) =
        MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1))
            (c * (-Complex.I) ^ e 1) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X (0 : Fin 2)) ^ e 0 := by
    calc
      _ = (MvPolynomial.C c * MvPolynomial.C ((-Complex.I) ^ e 1) *
            MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1)) 1) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X (0 : Fin 2)) ^ e 0 := by ring
      _ = _ := by
        rw [← map_mul, MvPolynomial.C_mul_monomial]
        congr 2
        ring
  calc
    _ = MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (e 1))
        (MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1))
            (c * (-Complex.I) ^ e 1) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X 0) ^ e 0) :=
      congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (e 1))) hreorder
    _ = _ := by
      rw [MvPolynomial.coeff_monomial_mul']
      simp only [le_refl, if_true, tsub_self]
      rw [← MvPolynomial.constantCoeff_eq, map_pow]
      have htwo : MvPolynomial.constantCoeff (2 : CircularChartPoly) = (2 : ℂ) := by
        change MvPolynomial.constantCoeff
          (MvPolynomial.C (2 : ℂ) : CircularChartPoly) = (2 : ℂ)
        simp
      rw [map_add, map_mul, htwo, MvPolynomial.constantCoeff_C,
        MvPolynomial.constantCoeff_X, mul_zero, add_zero]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartJ_coeff_extremal
    (D : ℕ) (Q : ComplexPlanePoly) (e : Fin 2 →₀ ℕ)
    (hdegree : Q.totalDegree ≤ D) (he : e ∈ Q.support)
    (hmax : ∀ f ∈ Q.support, f 0 ≤ e 0) :
    MvPolynomial.coeff (isotropicJLeadingExponent D e)
        (isotropicHomogenizedCircularChartJ D Q) =
      MvPolynomial.coeff e Q * (-Complex.I) ^ e 1 * (2 : ℂ) ^ e 0 := by
  classical
  rw [isotropicHomogenizedCircularChartJ_eq_support_sum D Q hdegree]
  rw [MvPolynomial.coeff_sum]
  calc
    _ = MvPolynomial.coeff (isotropicJLeadingExponent D e)
        (MvPolynomial.C (MvPolynomial.coeff e Q) *
          (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree)) := by
      apply Finset.sum_eq_single e
      · intro f hf hfe
        have hfzero : MvPolynomial.coeff (isotropicJLeadingExponent D e)
            (isotropicCircularChartJTerm D f (MvPolynomial.coeff f Q)) = 0 := by
          by_contra hcoeff
          have hmem : isotropicJLeadingExponent D e ∈
              (isotropicCircularChartJTerm D f (MvPolynomial.coeff f Q)).support :=
            MvPolynomial.mem_support_iff.mpr hcoeff
          obtain ⟨hzero, hone⟩ :=
            inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coordinate_bounds D f
              (isotropicJLeadingExponent D e) (MvPolynomial.coeff f Q) hmem
          have hfdegree : f.degree ≤ D :=
            (MvPolynomial.le_totalDegree hf).trans hdegree
          have hedegree : e.degree ≤ D :=
            (MvPolynomial.le_totalDegree he).trans hdegree
          have hdegreeEq : f.degree = e.degree := by
            rw [isotropicJLeadingExponent_one] at hone
            omega
          have hzeroLe : f 0 ≤ e 0 := hmax f hf
          rw [isotropicJLeadingExponent_zero] at hzero
          have hzeroEq : f 0 = e 0 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          have honeEq : f 1 = e 1 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          apply hfe
          apply Finsupp.ext
          intro i
          fin_cases i
          · exact hzeroEq
          · exact honeEq
        simpa [isotropicCircularChartJTerm] using hfzero
      · intro hnot
        exact (hnot he).elim
    _ = _ := by
      simpa [isotropicCircularChartJTerm] using
        inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coeff_leading D e (MvPolynomial.coeff e Q)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__planeCircularLocalOrder_le_degree_of_coeff_ne_zero
    (c : ℂ) {G : PlanePoly} {d : Fin 2 →₀ ℕ}
    (hcoeff : MvPolynomial.coeff d
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) ≠ 0) :
    planeCircularLocalOrder c G ≤ d.degree := by
  have hcoeffSeries : MvPowerSeries.coeff d
      ((projectiveCircularChart c (planeHomogenization G.totalDegree G) :
        CircularChartPoly) : MvPowerSeries (Fin 2) ℂ) ≠ 0 := by
    simpa using hcoeff
  have horder := MvPowerSeries.order_le hcoeffSeries
  have horderNat := ENat.toNat_le_toNat horder
  simpa [planeCircularLocalOrder, MvPolynomial.localOrder] using horderNat


theorem IsMaximallyCircular.bidegreeBound_planeIsotropicCoordinateEquiv
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (p : ℕ) (hdegree : G.totalDegree = 2 * p) :
    BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) := by
  classical
  let Q : ComplexPlanePoly :=
    planeToIsotropicCoordinates (realToComplexPlanePolynomial G)
  have hmapzero : realToComplexPlanePolynomial G ≠ 0 := by
    exact (MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective).ne hG
  have hQzero : Q ≠ 0 := by
    change planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G) ≠ 0
    exact planeIsotropicCoordinateEquiv.injective.ne hmapzero
  have hQdegree : Q.totalDegree ≤ G.totalDegree := by
    change (planeToIsotropicCoordinates
      (realToComplexPlanePolynomial G)).totalDegree ≤ G.totalDegree
    rw [planeToIsotropicCoordinates_totalDegree]
    change (MvPolynomial.map Complex.ofRealHom G).totalDegree ≤ G.totalDegree
    unfold MvPolynomial.totalDegree
    rw [MvPolynomial.support_map_of_injective G Complex.ofReal_injective]
  have hsupp : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr hQzero
  obtain ⟨eI, heI, heIsup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupp (fun e : Fin 2 →₀ ℕ ↦ e 1)
  have heImax : ∀ f ∈ Q.support, f 1 ≤ eI 1 := by
    intro f hf
    calc
      f 1 ≤ Q.support.sup (fun e : Fin 2 →₀ ℕ ↦ e 1) :=
        Finset.le_sup (f := fun e : Fin 2 →₀ ℕ ↦ e 1) hf
      _ = eI 1 := heIsup
  obtain ⟨eJ, heJ, heJsup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupp (fun e : Fin 2 →₀ ℕ ↦ e 0)
  have heJmax : ∀ f ∈ Q.support, f 0 ≤ eJ 0 := by
    intro f hf
    calc
      f 0 ≤ Q.support.sup (fun e : Fin 2 →₀ ℕ ↦ e 0) :=
        Finset.le_sup (f := fun e : Fin 2 →₀ ℕ ↦ e 0) hf
      _ = eJ 0 := heJsup
  have heIdegree : eI.degree ≤ G.totalDegree :=
    (MvPolynomial.le_totalDegree heI).trans hQdegree
  have heJdegree : eJ.degree ≤ G.totalDegree :=
    (MvPolynomial.le_totalDegree heJ).trans hQdegree
  have hcoeffI : MvPolynomial.coeff
      (isotropicILeadingExponent G.totalDegree eI)
      (isotropicHomogenizedCircularChartI G.totalDegree Q) ≠ 0 := by
    rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartI_coeff_extremal
      G.totalDegree Q eI hQdegree heI heImax]
    exact mul_ne_zero
      (mul_ne_zero (MvPolynomial.mem_support_iff.mp heI)
        (pow_ne_zero _ Complex.I_ne_zero))
      (pow_ne_zero _ (by norm_num))
  have hchartCoeffI : MvPolynomial.coeff
      (isotropicILeadingExponent G.totalDegree eI)
      (projectiveCircularChart Complex.I
        (planeHomogenization G.totalDegree G)) ≠ 0 := by
    change MvPolynomial.coeff (isotropicILeadingExponent G.totalDegree eI)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)) ≠ 0
    rw [projectiveCircularChartI_planeHomogenization_eq_isotropic]
    exact hcoeffI
  have hlocalI := inline_Esgk_MaximallyCircularIsotropicBidegree__planeCircularLocalOrder_le_degree_of_coeff_ne_zero
    Complex.I hchartCoeffI
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicILeadingExponent_degree G.totalDegree eI heIdegree] at hlocalI
  have horderI : planeCircularLocalOrderI G = p := by
    rcases hmax with ⟨hI, hJ⟩
    omega
  have heIbound : eI 1 ≤ p := by
    have heIcoord : eI 1 ≤ eI.degree := by
      rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add]
      omega
    change planeCircularLocalOrderI G ≤ G.totalDegree - eI 1 at hlocalI
    rw [horderI, hdegree] at hlocalI
    omega
  have hcoeffJ : MvPolynomial.coeff
      (isotropicJLeadingExponent G.totalDegree eJ)
      (isotropicHomogenizedCircularChartJ G.totalDegree Q) ≠ 0 := by
    rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartJ_coeff_extremal
      G.totalDegree Q eJ hQdegree heJ heJmax]
    exact mul_ne_zero
      (mul_ne_zero (MvPolynomial.mem_support_iff.mp heJ)
        (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)))
      (pow_ne_zero _ (by norm_num))
  have hchartCoeffJ : MvPolynomial.coeff
      (isotropicJLeadingExponent G.totalDegree eJ)
      (projectiveCircularChart (-Complex.I)
        (planeHomogenization G.totalDegree G)) ≠ 0 := by
    change MvPolynomial.coeff (isotropicJLeadingExponent G.totalDegree eJ)
      (projectiveCircularChartJ (planeHomogenization G.totalDegree G)) ≠ 0
    rw [projectiveCircularChartJ_planeHomogenization_eq_isotropic]
    exact hcoeffJ
  have hlocalJ := inline_Esgk_MaximallyCircularIsotropicBidegree__planeCircularLocalOrder_le_degree_of_coeff_ne_zero
    (-Complex.I) hchartCoeffJ
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicJLeadingExponent_degree G.totalDegree eJ heJdegree] at hlocalJ
  have horderJ : planeCircularLocalOrderJ G = p := by
    rcases hmax with ⟨hI, hJ⟩
    omega
  have heJbound : eJ 0 ≤ p := by
    have heJcoord : eJ 0 ≤ eJ.degree := by
      rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add]
      omega
    change planeCircularLocalOrderJ G ≤ G.totalDegree - eJ 0 at hlocalJ
    rw [horderJ, hdegree] at hlocalJ
    omega
  change BidegreeBound p Q
  intro e he
  exact ⟨(heJmax e he).trans heJbound, (heImax e he).trans heIbound⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

private theorem complex_I_ne_neg_I' : Complex.I ≠ -Complex.I := by
  intro h
  have him : (1 : ℝ) = -1 := congrArg Complex.im h
  have hlt : (-1 : ℝ) < 1 := lt_trans neg_one_lt_zero zero_lt_one
  exact (ne_of_gt hlt) him


theorem IsMaximallyCircular.rootMultiplicity_I_eq_localOrderI
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I =
      planeCircularLocalOrderI G := by
  have hI : planeCircularLocalOrderI G ≤
      (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I := by
    simpa [planeCircularLocalOrderI] using
      (planeCircularLocalOrder_le_rootMultiplicity Complex.I hG)
  have hJ : planeCircularLocalOrderJ G ≤
      (complexPlaneInfinityRestriction G).rootMultiplicity (-Complex.I) := by
    simpa [planeCircularLocalOrderJ] using
      (planeCircularLocalOrder_le_rootMultiplicity (-Complex.I) hG)
  have hroots :
      (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I +
          (complexPlaneInfinityRestriction G).rootMultiplicity (-Complex.I) ≤ G.totalDegree :=
    (Polynomial.rootMultiplicity_add_rootMultiplicity_le_natDegree_of_ne
      (complexPlaneInfinityRestriction G) complex_I_ne_neg_I').trans
        (complexPlaneInfinityRestriction_natDegree_le G)
  have horders := hmax.order_sum_eq_totalDegree
  omega


theorem chartInfinityRestriction_homogeneousComponent_ne_zero_of_rootMultiplicity_eq
    (c : ℂ) {G : PlanePoly} (hG : G ≠ 0)
    (hsat : (complexPlaneInfinityRestriction G).rootMultiplicity c =
      planeCircularLocalOrder c G) :
    chartInfinityRestriction
        (MvPolynomial.homogeneousComponent (planeCircularLocalOrder c G)
          (projectiveCircularChart c (planeHomogenization G.totalDegree G))) ≠ 0 := by
  let m := planeCircularLocalOrder c G
  let F := projectiveCircularChart c (planeHomogenization G.totalDegree G)
  let q := (complexPlaneInfinityRestriction G).comp (Polynomial.X + Polynomial.C c)
  have hq : q ≠ 0 := by
    exact Polynomial.comp_X_add_C_ne_zero_iff.mpr
      (complexPlaneInfinityRestriction_ne_zero hG)
  have hqcoeff : q.coeff q.natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq
  have hdegree : q.natTrailingDegree = m := by
    calc
      q.natTrailingDegree =
          (complexPlaneInfinityRestriction G).rootMultiplicity c := by
        simpa [q] using
          (Polynomial.rootMultiplicity_eq_natTrailingDegree
            (p := complexPlaneInfinityRestriction G) (t := c)).symm
      _ = m := by simpa [m] using hsat
  have hrestrict : chartInfinityRestriction F = q := by
    exact chartInfinityRestriction_projectiveCircularChart_planeHomogenization c G
  have hcoeffF :
      MvPolynomial.coeff (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) F ≠ 0 := by
    rw [← chartInfinityRestriction_coeff, hrestrict, ← hdegree]
    exact hqcoeff
  have hindexDegree :
      Finsupp.degree (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) = m := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.cons_zero]
    change m + (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) (0 : Fin 1).succ = m
    rw [Finsupp.cons_succ]
    simp
  intro hzero
  apply hcoeffF
  have hcomponentCoeff :
      MvPolynomial.coeff (Finsupp.cons m (0 : Fin 1 →₀ ℕ))
          (MvPolynomial.homogeneousComponent m F) =
        MvPolynomial.coeff (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) F := by
    simp [MvPolynomial.coeff_homogeneousComponent, hindexDegree]
  rw [← hcomponentCoeff, ← chartInfinityRestriction_coeff, hzero]
  simp


theorem IsMaximallyCircular.chartInfinityRestriction_tangentComponent_I_ne_zero
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    chartInfinityRestriction
        (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
          (projectiveCircularChartI (planeHomogenization G.totalDegree G))) ≠ 0 := by
  exact chartInfinityRestriction_homogeneousComponent_ne_zero_of_rootMultiplicity_eq
    Complex.I hG (by
      simpa [planeCircularLocalOrderI] using hmax.rootMultiplicity_I_eq_localOrderI hG)


end Esgk
end

end




















section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem circularChartDehomogenization_eq_map_finSuccEquiv (T : CircularChartPoly) :
    circularChartDehomogenization T =
      Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℂ)))
        (MvPolynomial.finSuccEquiv ℂ 1 T) := by
  let φ : CircularChartPoly →+* Polynomial ℂ :=
    (Polynomial.mapRingHom
      (MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℂ)))).comp
      (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv.toRingHom
  change circularChartDehomogenization T = φ T
  congr 1
  dsimp [φ]
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [RingHom.comp_apply, circularChartDehomogenization,
      MvPolynomial.finSuccEquiv_apply]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    ·
      simp [RingHom.comp_apply, circularChartDehomogenization,
        MvPolynomial.finSuccEquiv_apply]
    ·
      simp [RingHom.comp_apply, circularChartDehomogenization,
        MvPolynomial.finSuccEquiv_apply]

 
theorem circularChartDehomogenization_natDegree_le {T : CircularChartPoly} {p : ℕ}
    (hT : MvPolynomial.IsHomogeneous T p) :
    (circularChartDehomogenization T).natDegree ≤ p := by
  rw [circularChartDehomogenization_eq_map_finSuccEquiv]
  calc
    (Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℂ)))
          (MvPolynomial.finSuccEquiv ℂ 1 T)).natDegree ≤
        (MvPolynomial.finSuccEquiv ℂ 1 T).natDegree := Polynomial.natDegree_map_le
    _ = T.degreeOf 0 := MvPolynomial.natDegree_finSuccEquiv T
    _ ≤ T.totalDegree := MvPolynomial.degreeOf_le_totalDegree T 0
    _ ≤ p := hT.totalDegree_le


theorem circularChartDehomogenization_coeff_eq_chartInfinityRestriction_coeff
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p) :
    (circularChartDehomogenization T).coeff p = (chartInfinityRestriction T).coeff p := by
  have hhomogenize : (circularChartDehomogenization T).homogenize p = T := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hT
    rfl
  let d : Fin 2 →₀ ℕ := Finsupp.cons p (0 : Fin 1 →₀ ℕ)
  calc
    (circularChartDehomogenization T).coeff p =
        MvPolynomial.coeff d ((circularChartDehomogenization T).homogenize p) := by
      rw [Polynomial.coeff_homogenize]
      have hd0 : d 0 = p := by simp [d, Finsupp.cons_zero]
      have hd1 : d 1 = 0 := by
        change (Finsupp.cons p (0 : Fin 1 →₀ ℕ)) (Fin.succ 0) = 0
        exact Finsupp.cons_succ (0 : Fin 1) p (0 : Fin 1 →₀ ℕ)
      simp [hd0, hd1]
    _ = MvPolynomial.coeff d T := by rw [hhomogenize]
    _ = (chartInfinityRestriction T).coeff p := by
      rw [chartInfinityRestriction_coeff]

private theorem inline_Esgk_CircularTangentDehomogenization__chartInfinityRestriction_coeff_ne_zero_of_isHomogeneous
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p)
    (hrestriction : chartInfinityRestriction T ≠ 0) :
    (chartInfinityRestriction T).coeff p ≠ 0 := by
  intro hp
  apply hrestriction
  ext k
  by_cases hkp : k = p
  · simpa [hkp] using hp
  · rw [chartInfinityRestriction_coeff]
    apply hT.coeff_eq_zero
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.cons_zero]
    change k + (Finsupp.cons k (0 : Fin 1 →₀ ℕ)) (Fin.succ 0) ≠ p
    rw [Finsupp.cons_succ, Finsupp.zero_apply, add_zero]
    exact hkp


theorem circularChartDehomogenization_ne_zero_of_isHomogeneous
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p)
    (hrestriction : chartInfinityRestriction T ≠ 0) :
    circularChartDehomogenization T ≠ 0 := by
  intro hzero
  have hcoeff := inline_Esgk_CircularTangentDehomogenization__chartInfinityRestriction_coeff_ne_zero_of_isHomogeneous hT hrestriction
  apply hcoeff
  rw [← circularChartDehomogenization_coeff_eq_chartInfinityRestriction_coeff hT, hzero]
  simp


theorem circularChartDehomogenization_natDegree_eq_of_isHomogeneous
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p)
    (hrestriction : chartInfinityRestriction T ≠ 0) :
    (circularChartDehomogenization T).natDegree = p := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (circularChartDehomogenization_natDegree_le hT)
  rw [circularChartDehomogenization_coeff_eq_chartInfinityRestriction_coeff hT]
  exact inline_Esgk_CircularTangentDehomogenization__chartInfinityRestriction_coeff_ne_zero_of_isHomogeneous hT hrestriction


theorem IsMaximallyCircular.circularChartDehomogenization_tangentComponent_I_ne_zero
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    circularChartDehomogenization
        (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
          (projectiveCircularChartI (planeHomogenization G.totalDegree G))) ≠ 0 := by
  exact circularChartDehomogenization_ne_zero_of_isHomogeneous
    (T := MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (p := planeCircularLocalOrderI G)
    (MvPolynomial.homogeneousComponent_isHomogeneous
      (n := planeCircularLocalOrderI G)
      (φ := projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (hmax.chartInfinityRestriction_tangentComponent_I_ne_zero hG)


theorem IsMaximallyCircular.circularChartDehomogenization_tangentComponent_I_natDegree
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    (circularChartDehomogenization
      (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
        (projectiveCircularChartI
          (planeHomogenization G.totalDegree G)))).natDegree = planeCircularLocalOrderI G := by
  exact circularChartDehomogenization_natDegree_eq_of_isHomogeneous
    (T := MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (p := planeCircularLocalOrderI G)
    (MvPolynomial.homogeneousComponent_isHomogeneous
      (n := planeCircularLocalOrderI G)
      (φ := projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (hmax.chartInfinityRestriction_tangentComponent_I_ne_zero hG)

end Esgk
end

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem circleEquationPolynomial_totalDegree_eq (c : _root_.Point2) (r : ℝ) :
    (circleEquationPolynomial c r).totalDegree = 2 := by
  apply le_antisymm
  · have hconstant :
        (MvPolynomial.C (r ^ 2) : PlanePoly).totalDegree ≤ 2 := by
      rw [MvPolynomial.totalDegree_C]
      omega
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (planeSquaredDistancePolynomial_totalDegree_le c) hconstant)
  · have htop :
        MvPolynomial.homogeneousComponent 2 (circleEquationPolynomial c r) ≠ 0 := by
      have hconstant :
          MvPolynomial.homogeneousComponent 2
              (MvPolynomial.C (r ^ 2) : PlanePoly) = 0 := by
        apply MvPolynomial.homogeneousComponent_eq_zero
        rw [MvPolynomial.totalDegree_C]
        omega
      rw [circleEquationPolynomial, map_sub,
        homogeneousComponent_two_planeSquaredDistancePolynomial, hconstant, sub_zero]
      exact planeRadialQuadratic_ne_zero
    by_contra hdegree
    apply htop
    apply MvPolynomial.homogeneousComponent_eq_zero
    omega


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem IsMaximallyCircular.circularITangentPolynomial_ne_zero
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    circularITangentPolynomial G ≠ 0 := by
  exact hmax.circularChartDehomogenization_tangentComponent_I_ne_zero hG


theorem IsMaximallyCircular.circularITangentPolynomial_natDegree
    {G : PlanePoly} {pdeg : ℕ} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (hdegree : G.totalDegree = 2 * pdeg) :
    (circularITangentPolynomial G).natDegree = pdeg := by
  have hI := hmax.1
  have hlocal : planeCircularLocalOrderI G = pdeg := by
    omega
  rw [circularITangentPolynomial,
    hmax.circularChartDehomogenization_tangentComponent_I_natDegree hG, hlocal]


end Esgk
end

end











section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace MvPolynomial

 
theorem homogeneousComponent_map_star {σ : Type*} (m : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (map (starRingEnd ℂ) P) =
      map (starRingEnd ℂ) (homogeneousComponent m P) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_map]
  split <;> simp_all

end MvPolynomial

namespace Esgk

open PachDeZeeuw.Algebraic _root_.Polynomial

variable {n : ℕ}

 
theorem circularChartDehomogenization_map_star (T : CircularChartPoly) :
    circularChartDehomogenization (MvPolynomial.map (starRingEnd ℂ) T) =
      Polynomial.map (starRingEnd ℂ) (circularChartDehomogenization T) := by
  induction T using MvPolynomial.induction_on with
  | C r => simp [circularChartDehomogenization]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [circularChartDehomogenization]


theorem circularJTangentPolynomial_eq_map_star (G : PlanePoly) :
    circularJTangentPolynomial G =
      Polynomial.map (starRingEnd ℂ) (circularITangentPolynomial G) := by
  rw [circularJTangentPolynomial, circularITangentPolynomial,
    ← planeCircularLocalOrderI_eq_planeCircularLocalOrderJ G,
    ← projectiveCircularChartI_planeHomogenization_map_star G,
    MvPolynomial.homogeneousComponent_map_star,
    circularChartDehomogenization_map_star]


end Esgk
end

end











section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open _root_.Polynomial
open PachDeZeeuw.Algebraic


theorem exists_simultaneously_centered_circular_tangent_polynomials
    {G : PlanePoly} {p : ℕ}
    (hI : circularITangentPolynomial G ≠ 0)
    (hdegree : (circularITangentPolynomial G).natDegree = p)
    (hroots : (circularITangentPolynomial G).roots.toFinset.card = 1) :
    ∃ ξ : ℂ,
      (circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ)) =
        Polynomial.C (circularITangentPolynomial G).leadingCoeff * Polynomial.X ^ p ∧
      (circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star ξ)) =
        Polynomial.C (star (circularITangentPolynomial G).leadingCoeff) *
          Polynomial.X ^ p := by
  obtain ⟨τ, hfactor⟩ :=
    Polynomial.exists_eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_card_eq_one
      (circularITangentPolynomial G) hI hroots
  refine ⟨-Complex.I * τ, ?_, ?_⟩
  · nth_rewrite 1 [hfactor]
    rw [hdegree]
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    have hshift : Complex.I * (-Complex.I * τ) = τ := by
      calc
        Complex.I * (-Complex.I * τ) = -(Complex.I * Complex.I) * τ := by ring
        _ = τ := by rw [Complex.I_mul_I]; ring
    rw [hshift]
    ring
  · rw [circularJTangentPolynomial_eq_map_star]
    nth_rewrite 1 [hfactor]
    rw [hdegree, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp]
    have hshift : -Complex.I * star (-Complex.I * τ) = star τ := by
      have hconj : star (-Complex.I * τ) = Complex.I * star τ := by
        simp
      rw [hconj]
      calc
        -Complex.I * (Complex.I * star τ) =
            -(Complex.I * Complex.I) * star τ := by ring
        _ = star τ := by rw [Complex.I_mul_I]; ring
    rw [hshift]
    simp only [Polynomial.map_C, starRingEnd_apply]
    rw [Polynomial.C_comp]
    ring

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

private theorem inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two :
    (MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2 = 1 := by
  change MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C (2 : ℂ) = MvPolynomial.C 1
  rw [← map_mul]
  norm_num

private theorem inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_I_sq :
    (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]


private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartIForFaces_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartI G := by
  change
    (((bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartI G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two
    · calc
        _ = (MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_I_sq]
          ring
        _ = MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two, mul_one]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartJForFaces_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartJ G := by
  change
    (((bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartJ G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two
    · calc
        _ = (-MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_I_sq]
          ring
        _ = -MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two, mul_one]

private theorem inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_isHomogeneousForFaces
    {d : ℕ} {P : ComplexPlanePoly} (hP : P.IsHomogeneous d) :
    (planeToIsotropicCoordinates P).IsHomogeneous d := by
  change
    (MvPolynomial.eval₂ (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
      ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * Complex.I)) *
          (MvPolynomial.X 0 - MvPolynomial.X 1)] P).IsHomogeneous d
  have h := hP.eval₂
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1)]
    (fun c ↦ MvPolynomial.isHomogeneous_C (Fin 2) c)
    (fun i ↦ by
      fin_cases i
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).add
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).sub
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _)
  rw [Nat.one_mul] at h
  exact h

private theorem inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_homogeneousComponentForFaces
    (d : ℕ) (P : ComplexPlanePoly) :
    planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) =
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) := by
  classical
  by_cases hd : d ≤ P.totalDegree
  · have hsum :
        ∑ k ∈ Finset.range (P.totalDegree + 1),
            planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P) =
          planeToIsotropicCoordinates P := by
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    have himage (k : ℕ) :
        (planeToIsotropicCoordinates
          (MvPolynomial.homogeneousComponent k P)).IsHomogeneous k :=
      inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_isHomogeneousForFaces
        (MvPolynomial.homogeneousComponent_isHomogeneous k P)
    symm
    calc
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) =
          MvPolynomial.homogeneousComponent d
            (∑ k ∈ Finset.range (P.totalDegree + 1),
              planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        rw [hsum]
      _ = ∑ k ∈ Finset.range (P.totalDegree + 1),
          MvPolynomial.homogeneousComponent d
            (planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        simp only [map_sum]
      _ = planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) := by
        simp_rw [MvPolynomial.homogeneousComponent_of_mem (himage _)]
        simp [hd]
  · have hPd : P.totalDegree < d := by omega
    have hTd : (planeToIsotropicCoordinates P).totalDegree < d := by
      rw [planeToIsotropicCoordinates_totalDegree]
      exact hPd
    rw [MvPolynomial.homogeneousComponent_eq_zero d P hPd, map_zero,
      MvPolynomial.homogeneousComponent_eq_zero d _ hTd]

private theorem inline_Esgk_CircularTangentIsotropicFaces__realToComplexPlanePolynomial_homogeneousComponentForFaces
    (d : ℕ) (G : PlanePoly) :
    realToComplexPlanePolynomial (MvPolynomial.homogeneousComponent d G) =
      MvPolynomial.homogeneousComponent d (realToComplexPlanePolynomial G) := by
  ext e
  simp only [realToComplexPlanePolynomial, MvPolynomial.coeff_map,
    MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp


private theorem inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartI_planeHomogenization_eq_isotropicForFaces
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartI (planeHomogenization D G) =
      bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartI, projectiveCircularChart_planeHomogenization]
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartI (MvPolynomial.homogeneousComponent d G) = _
  rw [← inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartIForFaces_planeToIsotropic_realToComplex]
  congr 1
  rw [inline_Esgk_CircularTangentIsotropicFaces__realToComplexPlanePolynomial_homogeneousComponentForFaces,
    inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_homogeneousComponentForFaces]

private theorem inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartJ_planeHomogenization_eq_isotropicForFaces
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartJ (planeHomogenization D G) =
      bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartJ, projectiveCircularChart_planeHomogenization]
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartJ (MvPolynomial.homogeneousComponent d G) = _
  rw [← inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartJForFaces_planeToIsotropic_realToComplex]
  congr 1
  rw [inline_Esgk_CircularTangentIsotropicFaces__realToComplexPlanePolynomial_homogeneousComponentForFaces,
    inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_homogeneousComponentForFaces]


@[simp]
theorem isotropicFaceExponent_zero (a b : ℕ) : isotropicFaceExponent a b 0 = a := by
  simp [isotropicFaceExponent]

@[simp]
theorem isotropicFaceExponent_one (a b : ℕ) : isotropicFaceExponent a b 1 = b := by
  simp [isotropicFaceExponent]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicFaceExponent_eq_iff {a b c d : ℕ} :
    isotropicFaceExponent a b = isotropicFaceExponent c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using DFunLike.congr_fun h 0,
      by simpa using DFunLike.congr_fun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff {e : Fin 2 →₀ ℕ} {a b : ℕ} :
    e = isotropicFaceExponent a b ↔ e 0 = a ∧ e 1 = b := by
  constructor
  · intro h
    exact ⟨by simpa using DFunLike.congr_fun h 0,
      by simpa using DFunLike.congr_fun h 1⟩
  · rintro ⟨hzero, hone⟩
    apply Finsupp.ext
    intro i
    fin_cases i
    · simp [hzero]
    · simp [hone]


theorem circularChartDehomogenization_homogeneousComponent_coeff
    (F : CircularChartPoly) (p a : ℕ) (ha : a ≤ p) :
    (circularChartDehomogenization (MvPolynomial.homogeneousComponent p F)).coeff a =
      MvPolynomial.coeff (isotropicFaceExponent a (p - a)) F := by
  let T := MvPolynomial.homogeneousComponent p F
  have hT : MvPolynomial.IsHomogeneous T p :=
    MvPolynomial.homogeneousComponent_isHomogeneous p F
  have hhomogenize : (circularChartDehomogenization T).homogenize p = T := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hT
    rfl
  let e := isotropicFaceExponent a (p - a)
  calc
    (circularChartDehomogenization T).coeff a =
        MvPolynomial.coeff e ((circularChartDehomogenization T).homogenize p) := by
      rw [Polynomial.coeff_homogenize]
      simp [e, Nat.add_sub_of_le ha]
    _ = MvPolynomial.coeff e T := by rw [hhomogenize]
    _ = MvPolynomial.coeff e F := by
      have hedegree : Finsupp.degree e = p := by
        rw [Finsupp.degree_eq_sum]
        simp [e, Fin.sum_univ_two, Nat.add_sub_of_le ha]
      rw [MvPolynomial.coeff_homogeneousComponent, if_pos hedegree]

private theorem inline_Esgk_CircularTangentIsotropicFaces__coeff_circularChartZ_pow_mul_toMvPolynomial
    (P : Polynomial ℂ) (a b k : ℕ) :
    MvPolynomial.coeff (isotropicFaceExponent a b)
        (circularChartZ ^ k * Polynomial.toMvPolynomial 0 P) =
      if b = k then P.coeff a else 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, mul_add, MvPolynomial.coeff_add, Polynomial.coeff_add, hP, hQ]
      by_cases hbk : b = k <;> simp [hbk]
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, Polynomial.toMvPolynomial_C, map_pow,
        Polynomial.toMvPolynomial_X]
      have hpoly :
          circularChartZ ^ k *
              ((MvPolynomial.C c : CircularChartPoly) * MvPolynomial.X 0 ^ n) =
            MvPolynomial.monomial (isotropicFaceExponent n k) c := by
        rw [MvPolynomial.monomial_eq]
        simp [isotropicFaceExponent, Finsupp.prod_fintype, Fin.prod_univ_two,
          circularChartZ]
        ring
      rw [hpoly, MvPolynomial.coeff_monomial]
      simp only [inline_Esgk_CircularTangentIsotropicFaces__isotropicFaceExponent_eq_iff, Polynomial.coeff_C_mul_X_pow]
      by_cases hbk : b = k
      · subst b
        by_cases han : a = n
        · subst a
          simp
        · simp [han, Ne.symm han]
      · have hkb : k ≠ b := Ne.symm hbk
        by_cases han : a = n
        · subst a
          simp [hbk, hkb]
        · simp [hbk, hkb, Ne.symm han]

private theorem inline_Esgk_CircularTangentIsotropicFaces__homogenized_eval₂_eq_support_sumForFaces
    (D : ℕ) (Q : ComplexPlanePoly) (A B : CircularChartPoly)
    (hdegree : Q.totalDegree ≤ D) :
    (∑ d ∈ Finset.range (D + 1),
      circularChartZ ^ (D - d) *
        MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly) ![A, B]
          (MvPolynomial.homogeneousComponent d Q)) =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  classical
  calc
    _ = ∑ d ∈ Finset.range (D + 1),
        ∑ e ∈ Q.support with e.degree = d,
          MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
            circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hedegree : e.degree = d := (Finset.mem_filter.mp he).2
      rw [MvPolynomial.eval₂Hom_monomial]
      rw [hedegree]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two]
      ring
    _ = ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_fiberwise_of_maps_to
      intro e he
      rw [Finsupp.degree_eq_sum]
      simp only [Finset.mem_range, Nat.lt_add_one_iff]
      calc
        ∑ i, e i = e.sum (fun _ a ↦ a) :=
          (Finsupp.sum_fintype e (fun _ a ↦ a) (fun _ ↦ rfl)).symm
        _ ≤ D := (MvPolynomial.le_totalDegree he).trans hdegree


private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces D Q =
      ∑ e ∈ Q.support,
        bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces D e (MvPolynomial.coeff e Q) := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__homogenized_eval₂_eq_support_sumForFaces D Q _ _ hdegree

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces D Q =
      ∑ e ∈ Q.support,
        bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces D e (MvPolynomial.coeff e Q) := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__homogenized_eval₂_eq_support_sumForFaces D Q _ _ hdegree


private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_eq_toMvPolynomial
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces D e c =
      circularChartZ ^ (D - e.degree) *
        Polynomial.toMvPolynomial 0 (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces e c) := by
  simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces, bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces,
    circularChartU, map_ofNat]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_eq_toMvPolynomial
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces D e c =
      circularChartZ ^ (D - e.degree) *
        Polynomial.toMvPolynomial 0 (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces e c) := by
  simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces, bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces,
    circularChartU, map_ofNat]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces (e : Fin 2 →₀ ℕ) :
    e.degree = e 0 + e 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartIPolynomialForFaces_eq
    (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces e c =
      Polynomial.C (c * Complex.I ^ e 0) * Polynomial.X ^ e 0 *
        (2 - Polynomial.C Complex.I * Polynomial.X) ^ e 1 := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces, mul_pow, ← map_pow, map_mul]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJPolynomialForFaces_eq
    (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces e c =
      Polynomial.C (c * (-Complex.I) ^ e 1) * Polynomial.X ^ e 1 *
        (2 + Polynomial.C Complex.I * Polynomial.X) ^ e 0 := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces, mul_pow, ← map_neg, ← map_pow,
    map_mul]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face
    (p a : ℕ) (ha : a ≤ p) (e : Fin 2 →₀ ℕ) (c : ℂ)
    (hebound : e 0 ≤ p ∧ e 1 ≤ p) :
    MvPolynomial.coeff (isotropicFaceExponent a (p - a))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces (2 * p) e c) =
      if e = isotropicFaceExponent a p
      then c * Complex.I ^ a * (2 : ℂ) ^ p
      else 0 := by
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_eq_toMvPolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__coeff_circularChartZ_pow_mul_toMvPolynomial]
  by_cases hz : p - a = 2 * p - e.degree
  · rw [if_pos hz]
    have hedegree_le : e.degree ≤ 2 * p := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
      omega
    have hedegree : e.degree = p + a := by omega
    have hae : a ≤ e 0 := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
      omega
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartIPolynomialForFaces_eq]
    by_cases he : e = isotropicFaceExponent a p
    · subst e
      simp only [isotropicFaceExponent_zero, isotropicFaceExponent_one]
      simp only [if_true]
      rw [mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      simp [Polynomial.coeff_zero_eq_eval_zero]
    · rw [if_neg he, mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      have hene : e 0 ≠ a := by
        intro hezero
        apply he
        apply Finsupp.ext
        intro i
        fin_cases i
        · simp [hezero]
        · rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
          simp
          omega
      have hlt : a < e 0 := lt_of_le_of_ne hae (Ne.symm hene)
      simp [not_le.mpr hlt]
  · rw [if_neg hz, if_neg]
    intro he
    subst e
    apply hz
    rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
    simp
    omega

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face
    (p b : ℕ) (hb : b ≤ p) (e : Fin 2 →₀ ℕ) (c : ℂ)
    (hebound : e 0 ≤ p ∧ e 1 ≤ p) :
    MvPolynomial.coeff (isotropicFaceExponent b (p - b))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces (2 * p) e c) =
      if e = isotropicFaceExponent p b
      then c * (-Complex.I) ^ b * (2 : ℂ) ^ p
      else 0 := by
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_eq_toMvPolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__coeff_circularChartZ_pow_mul_toMvPolynomial]
  by_cases hz : p - b = 2 * p - e.degree
  · rw [if_pos hz]
    have hedegree_le : e.degree ≤ 2 * p := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
      omega
    have hedegree : e.degree = p + b := by omega
    have hbe : b ≤ e 1 := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
      omega
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJPolynomialForFaces_eq]
    by_cases he : e = isotropicFaceExponent p b
    · subst e
      simp only [isotropicFaceExponent_zero, isotropicFaceExponent_one]
      simp only [if_true]
      rw [mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      simp [Polynomial.coeff_zero_eq_eval_zero]
    · rw [if_neg he, mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      have hene : e 1 ≠ b := by
        intro heone
        apply he
        apply Finsupp.ext
        intro i
        fin_cases i
        · rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
          simp
          omega
        · simp [heone]
      have hlt : b < e 1 := lt_of_le_of_ne hbe (Ne.symm hene)
      simp [not_le.mpr hlt]
  · rw [if_neg hz, if_neg]
    intro he
    subst e
    apply hz
    rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
    simp
    omega

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_coeff_face
    (Q : ComplexPlanePoly) (p a : ℕ) (ha : a ≤ p) (hbound : BidegreeBound p Q) :
    MvPolynomial.coeff (isotropicFaceExponent a (p - a))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces (2 * p) Q) =
      (2 : ℂ) ^ p * Complex.I ^ a *
        MvPolynomial.coeff (isotropicFaceExponent a p) Q := by
  classical
  have hdegree : Q.totalDegree ≤ 2 * p :=
    totalDegree_le_two_mul_of_bidegreeBound p hbound
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_eq_support_sum _ _ hdegree]
  rw [MvPolynomial.coeff_sum]
  by_cases he : isotropicFaceExponent a p ∈ Q.support
  · rw [Finset.sum_eq_single (isotropicFaceExponent a p)]
    · rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face p a ha _ _ (hbound _ he),
        if_pos rfl]
      ring
    · intro e heQ hne
      rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face p a ha _ _ (hbound _ heQ),
        if_neg hne]
    · intro hnot
      exact (hnot he).elim
  · have hcoeff : MvPolynomial.coeff (isotropicFaceExponent a p) Q = 0 := by
      rwa [← MvPolynomial.notMem_support_iff]
    rw [hcoeff, mul_zero]
    apply Finset.sum_eq_zero
    intro e heQ
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face p a ha _ _ (hbound _ heQ),
      if_neg]
    intro heq
    subst e
    exact he heQ

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_coeff_face
    (Q : ComplexPlanePoly) (p b : ℕ) (hb : b ≤ p) (hbound : BidegreeBound p Q) :
    MvPolynomial.coeff (isotropicFaceExponent b (p - b))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces (2 * p) Q) =
      (2 : ℂ) ^ p * (-Complex.I) ^ b *
        MvPolynomial.coeff (isotropicFaceExponent p b) Q := by
  classical
  have hdegree : Q.totalDegree ≤ 2 * p :=
    totalDegree_le_two_mul_of_bidegreeBound p hbound
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_eq_support_sum _ _ hdegree]
  rw [MvPolynomial.coeff_sum]
  by_cases he : isotropicFaceExponent p b ∈ Q.support
  · rw [Finset.sum_eq_single (isotropicFaceExponent p b)]
    · rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face p b hb _ _ (hbound _ he),
        if_pos rfl]
      ring
    · intro e heQ hne
      rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face p b hb _ _ (hbound _ heQ),
        if_neg hne]
    · intro hnot
      exact (hnot he).elim
  · have hcoeff : MvPolynomial.coeff (isotropicFaceExponent p b) Q = 0 := by
      rwa [← MvPolynomial.notMem_support_iff]
    rw [hcoeff, mul_zero]
    apply Finset.sum_eq_zero
    intro e heQ
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face p b hb _ _ (hbound _ heQ),
      if_neg]
    intro heq
    subst e
    exact he heQ


theorem circularITangentPolynomial_coeff_eq_isotropic_second_face
    {G : PlanePoly} {p a : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))
    (ha : a ≤ p) :
    (circularITangentPolynomial G).coeff a =
      (2 : ℂ) ^ p * Complex.I ^ a *
        MvPolynomial.coeff (isotropicFaceExponent a p)
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) := by
  have hlocal : planeCircularLocalOrderI G = p := by
    have hI := hmax.1
    omega
  rw [circularITangentPolynomial, hlocal,
    circularChartDehomogenization_homogeneousComponent_coeff _ p a ha,
    hdegree, inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartI_planeHomogenization_eq_isotropicForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_coeff_face _ p a ha hbound


theorem circularJTangentPolynomial_coeff_eq_isotropic_first_face
    {G : PlanePoly} {p b : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))
    (hb : b ≤ p) :
    (circularJTangentPolynomial G).coeff b =
      (2 : ℂ) ^ p * (-Complex.I) ^ b *
        MvPolynomial.coeff (isotropicFaceExponent p b)
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) := by
  have hlocal : planeCircularLocalOrderJ G = p := by
    have hJ := hmax.2
    omega
  rw [circularJTangentPolynomial, hlocal,
    circularChartDehomogenization_homogeneousComponent_coeff _ p b hb,
    hdegree, inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartJ_planeHomogenization_eq_isotropicForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_coeff_face _ p b hb hbound


private theorem inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsSecondVariablePolynomial
    (Q : ComplexPlanePoly) (a b : ℕ) :
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q).coeff b).coeff a =
      MvPolynomial.coeff (isotropicFaceExponent a b) Q := by
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial e c =>
      rw [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial, MvPolynomial.eval₂Hom_monomial]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two, MvPolynomial.coeff_monomial]
      rw [← map_pow, Polynomial.coeff_C_mul_X_pow]
      by_cases hzero : e 0 = a
      · subst a
        by_cases hone : e 1 = b
        · subst b
          simp [inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hone, Ne.symm hone, inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
      · have hzero' : a ≠ e 0 := Ne.symm hzero
        by_cases hone : e 1 = b
        · subst b
          simp [hzero, hzero', inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hzero, hone, Ne.symm hone,
            inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]

private theorem inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsFirstVariablePolynomial
    (Q : ComplexPlanePoly) (a b : ℕ) :
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q).coeff a).coeff b =
      MvPolynomial.coeff (isotropicFaceExponent a b) Q := by
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial e c =>
      rw [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial, MvPolynomial.eval₂Hom_monomial]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two, MvPolynomial.coeff_monomial]
      rw [mul_comm (Polynomial.X ^ e 0), ← map_pow,
        Polynomial.coeff_C_mul_X_pow]
      by_cases hzero : e 0 = a
      · subst a
        by_cases hone : e 1 = b
        · subst b
          simp [inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hone, Ne.symm hone, inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
      · have hzero' : a ≠ e 0 := Ne.symm hzero
        by_cases hone : e 1 = b
        · subst b
          simp [hzero, hzero', inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hzero, hzero', hone,
            inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]


@[simp]
theorem isotropicSecondFacePolynomial_coeff (p : ℕ) (Q : ComplexPlanePoly) (a : ℕ) :
    (isotropicSecondFacePolynomial p Q).coeff a =
      MvPolynomial.coeff (isotropicFaceExponent a p) Q := by
  exact inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsSecondVariablePolynomial Q a p

@[simp]
theorem isotropicFirstFacePolynomial_coeff (p : ℕ) (Q : ComplexPlanePoly) (b : ℕ) :
    (isotropicFirstFacePolynomial p Q).coeff b =
      MvPolynomial.coeff (isotropicFaceExponent p b) Q := by
  exact inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsFirstVariablePolynomial Q p b

private theorem inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_add_C_of_natDegree_le
    {R : Type*} [CommSemiring R] [Nontrivial R]
    (P : Polynomial R) (r : R) {p : ℕ} (hdegree : P.natDegree ≤ p) :
    (P.comp (Polynomial.X + Polynomial.C r)).coeff p = P.coeff p := by
  rw [← Polynomial.taylor_apply]
  by_cases hdeg : P.natDegree = p
  · subst p
    rw [Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]
  · have hlt : P.natDegree < p := lt_of_le_of_ne hdegree hdeg
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    simpa using hlt

private theorem inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_sub_C_of_natDegree_le
    {R : Type*} [CommRing R] [Nontrivial R]
    (P : Polynomial R) (r : R) {p : ℕ} (hdegree : P.natDegree ≤ p) :
    (P.comp (Polynomial.X - Polynomial.C r)).coeff p = P.coeff p := by
  simpa [sub_eq_add_neg] using
    inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_add_C_of_natDegree_le P (-r) hdegree


private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_isotropicTranslation
    (c : ℂ) (Q : ComplexPlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial (isotropicTranslation c Q) =
      bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation c (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q) := by
  change
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial.comp (isotropicTranslation c)) Q) =
      (((bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation c).comp
        bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial) Q)
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial, isotropicTranslation,
      bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial, isotropicTranslation,
        bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_isotropicTranslation
    (c : ℂ) (Q : ComplexPlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial (isotropicTranslation c Q) =
      bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation c (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q) := by
  change
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial.comp (isotropicTranslation c)) Q) =
      (((bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation c).comp
        bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial) Q)
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial, isotropicTranslation,
      bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial, isotropicTranslation,
        bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro b hb
  ext a
  rw [Polynomial.coeff_zero, inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsSecondVariablePolynomial]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).2
  simp only [isotropicFaceExponent_one] at hle
  exact (not_le_of_gt hb) hle

private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  ext b
  rw [Polynomial.coeff_zero, inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsFirstVariablePolynomial]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).1
  simp only [isotropicFaceExponent_zero] at hle
  exact (not_le_of_gt ha) hle


theorem isotropicSecondFacePolynomial_isotropicTranslation
    (c : ℂ) (p : ℕ) {Q : ComplexPlanePoly} (hbound : BidegreeBound p Q) :
    isotropicSecondFacePolynomial p (isotropicTranslation c Q) =
      (isotropicSecondFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C c) := by
  rw [isotropicSecondFacePolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_isotropicTranslation]
  let R := bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q
  let S := Polynomial.map (bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation c) R
  have hR : R.natDegree ≤ p := inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_natDegree_le hbound
  have hS : S.natDegree ≤ p := Polynomial.natDegree_map_le.trans hR
  change
    (S.comp (Polynomial.X - Polynomial.C (Polynomial.C (star c)))).coeff p = _
  rw [inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_sub_C_of_natDegree_le S _ hS]
  simp [S, R, isotropicSecondFacePolynomial, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]


theorem isotropicFirstFacePolynomial_isotropicTranslation
    (c : ℂ) (p : ℕ) {Q : ComplexPlanePoly} (hbound : BidegreeBound p Q) :
    isotropicFirstFacePolynomial p (isotropicTranslation c Q) =
      (isotropicFirstFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C (star c)) := by
  rw [isotropicFirstFacePolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_isotropicTranslation]
  let R := bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q
  let S := Polynomial.map (bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation (star c)) R
  have hR : R.natDegree ≤ p := inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_natDegree_le hbound
  have hS : S.natDegree ≤ p := Polynomial.natDegree_map_le.trans hR
  change
    (S.comp (Polynomial.X - Polynomial.C (Polynomial.C c))).coeff p = _
  rw [inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_sub_C_of_natDegree_le S _ hS]
  simp [S, R, isotropicFirstFacePolynomial, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicSecondFacePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (isotropicSecondFacePolynomial p Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [isotropicSecondFacePolynomial_coeff]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).1
  simp only [isotropicFaceExponent_zero] at hle
  exact (not_le_of_gt ha) hle

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicFirstFacePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (isotropicFirstFacePolynomial p Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro b hb
  rw [isotropicFirstFacePolynomial_coeff]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).2
  simp only [isotropicFaceExponent_one] at hle
  exact (not_le_of_gt hb) hle


theorem circularITangentPolynomial_eq_isotropicSecondFace
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) :
    circularITangentPolynomial G =
      Polynomial.C ((2 : ℂ) ^ p) *
        (isotropicSecondFacePolynomial p
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))).comp
            (Polynomial.C Complex.I * Polynomial.X) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  have hlocal : planeCircularLocalOrderI G = p := by
    have hI := hmax.1
    omega
  have hTdegree : (circularITangentPolynomial G).natDegree ≤ p := by
    rw [circularITangentPolynomial, hlocal]
    exact circularChartDehomogenization_natDegree_le
      (MvPolynomial.homogeneousComponent_isHomogeneous p
        (projectiveCircularChartI (planeHomogenization G.totalDegree G)))
  have hFdegree : (isotropicSecondFacePolynomial p Q).natDegree ≤ p :=
    inline_Esgk_CircularTangentIsotropicFaces__isotropicSecondFacePolynomial_natDegree_le hbound
  ext a
  by_cases ha : a ≤ p
  · rw [circularITangentPolynomial_coeff_eq_isotropic_second_face hmax hdegree hbound ha,
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      isotropicSecondFacePolynomial_coeff]
    ring
  · have hpa : p < a := lt_of_not_ge ha
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hTdegree.trans_lt hpa),
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hFdegree.trans_lt hpa)]
    simp


theorem circularJTangentPolynomial_eq_isotropicFirstFace
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) :
    circularJTangentPolynomial G =
      Polynomial.C ((2 : ℂ) ^ p) *
        (isotropicFirstFacePolynomial p
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))).comp
            (Polynomial.C (-Complex.I) * Polynomial.X) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  have hlocal : planeCircularLocalOrderJ G = p := by
    have hJ := hmax.2
    omega
  have hTdegree : (circularJTangentPolynomial G).natDegree ≤ p := by
    rw [circularJTangentPolynomial, hlocal]
    exact circularChartDehomogenization_natDegree_le
      (MvPolynomial.homogeneousComponent_isHomogeneous p
        (projectiveCircularChartJ (planeHomogenization G.totalDegree G)))
  have hFdegree : (isotropicFirstFacePolynomial p Q).natDegree ≤ p :=
    inline_Esgk_CircularTangentIsotropicFaces__isotropicFirstFacePolynomial_natDegree_le hbound
  ext b
  by_cases hb : b ≤ p
  · rw [circularJTangentPolynomial_coeff_eq_isotropic_first_face hmax hdegree hbound hb,
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      isotropicFirstFacePolynomial_coeff]
    ring
  · have hpb : p < b := lt_of_not_ge hb
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hTdegree.trans_lt hpb),
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hFdegree.trans_lt hpb)]
    simp

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicTranslation_neg_eq_inverseIsotropicTranslation (c : ℂ) :
    isotropicTranslation (-c) = inverseIsotropicTranslation c := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i <;>
      simp [isotropicTranslation, inverseIsotropicTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__bidegreeBound_of_isotropicTranslation
    (c : ℂ) (p : ℕ) {Q : ComplexPlanePoly}
    (hbound : BidegreeBound p (isotropicTranslation c Q)) :
    BidegreeBound p Q := by
  have hneg := bidegreeBound_isotropicTranslation (-c) p hbound
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicTranslation_neg_eq_inverseIsotropicTranslation] at hneg
  have hinv : inverseIsotropicTranslation c (isotropicTranslation c Q) = Q := by
    simpa [RingHom.comp_apply] using
      RingHom.congr_fun (inverseIsotropicTranslation_comp_isotropicTranslation c) Q
  rw [hinv] at hneg
  exact hneg


theorem circularITangentPolynomial_comp_centered_coeff_eq_isotropic_second_face
    {G : PlanePoly} {p a : ℕ} (c : ℂ) (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (isotropicTranslationEquiv c
        (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))) :
    ((circularITangentPolynomial G).comp
      (Polynomial.X + Polynomial.C (Complex.I * c))).coeff a =
        (2 : ℂ) ^ p * Complex.I ^ a *
          MvPolynomial.coeff (isotropicFaceExponent a p)
            (isotropicTranslationEquiv c
              (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  let Qc := isotropicTranslationEquiv c Q
  have hboundQ : BidegreeBound p Q := by
    apply inline_Esgk_CircularTangentIsotropicFaces__bidegreeBound_of_isotropicTranslation c p
    simpa [Q, Qc] using hbound
  have hface : isotropicSecondFacePolynomial p Qc =
      (isotropicSecondFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C c) := by
    simpa [Qc, Q] using isotropicSecondFacePolynomial_isotropicTranslation c p hboundQ
  have hbase := circularITangentPolynomial_eq_isotropicSecondFace hmax hdegree hboundQ
  have hpoly :
      (circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * c)) =
        Polynomial.C ((2 : ℂ) ^ p) *
          (isotropicSecondFacePolynomial p Qc).comp
            (Polynomial.C Complex.I * Polynomial.X) := by
    rw [hbase]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc]
    rw [hface, Polynomial.comp_assoc]
    congr 2
    simp
    ring_nf
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
    ring
  rw [hpoly, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
    isotropicSecondFacePolynomial_coeff]
  ring


theorem circularJTangentPolynomial_comp_centered_coeff_eq_isotropic_first_face
    {G : PlanePoly} {p b : ℕ} (c : ℂ) (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (isotropicTranslationEquiv c
        (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))) :
    ((circularJTangentPolynomial G).comp
      (Polynomial.X + Polynomial.C (-Complex.I * star c))).coeff b =
        (2 : ℂ) ^ p * (-Complex.I) ^ b *
          MvPolynomial.coeff (isotropicFaceExponent p b)
            (isotropicTranslationEquiv c
              (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  let Qc := isotropicTranslationEquiv c Q
  have hboundQ : BidegreeBound p Q := by
    apply inline_Esgk_CircularTangentIsotropicFaces__bidegreeBound_of_isotropicTranslation c p
    simpa [Q, Qc] using hbound
  have hface : isotropicFirstFacePolynomial p Qc =
      (isotropicFirstFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C (star c)) := by
    simpa [Qc, Q] using isotropicFirstFacePolynomial_isotropicTranslation c p hboundQ
  have hbase := circularJTangentPolynomial_eq_isotropicFirstFace hmax hdegree hboundQ
  have hpoly :
      (circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star c)) =
        Polynomial.C ((2 : ℂ) ^ p) *
          (isotropicFirstFacePolynomial p Qc).comp
            (Polynomial.C (-Complex.I) * Polynomial.X) := by
    rw [hbase]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc]
    rw [hface, Polynomial.comp_assoc]
    congr 2
    simp
    ring_nf
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
    ring
  rw [hpoly, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
    isotropicFirstFacePolynomial_coeff]
  ring

end Esgk
end

end











section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


theorem IsMaximallyCircular.centered_isotropic_corner_normal_form_of_tangent_identities
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (hdegree : G.totalDegree = 2 * p) (hp : 0 < p) (ξ : ℂ)
    (hcenterI :
      (circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ)) =
        Polynomial.C (circularITangentPolynomial G).leadingCoeff * Polynomial.X ^ p)
    (hcenterJ :
      (circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star ξ)) =
        Polynomial.C (star (circularITangentPolynomial G).leadingCoeff) *
          Polynomial.X ^ p) :
    ∃ c : ℂ, ∃ R : BidegreePolynomial ℂ,
      c ≠ 0 ∧
        isotropicTranslationEquiv ξ
            (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) =
          MvPolynomial.monomial (bivariateCornerExponent p) c + R ∧
        BidegreeBound (p - 1) R := by
  let Q : ComplexPlanePoly :=
    planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  have hI : circularITangentPolynomial G ≠ 0 :=
    hmax.circularITangentPolynomial_ne_zero hG
  let Qc : ComplexPlanePoly := isotropicTranslationEquiv ξ Q
  have hboundQ : BidegreeBound p Q := by
    simpa only [Q] using
      hmax.bidegreeBound_planeIsotropicCoordinateEquiv hG p hdegree
  have hbound : BidegreeBound p Qc := by
    simpa only [Qc, isotropicTranslationEquiv_apply] using
      bidegreeBound_isotropicTranslation ξ p hboundQ
  have hrow : ∀ a < p, MvPolynomial.coeff (isotropicFaceExponent a p) Qc = 0 := by
    intro a ha
    have hcenterCoeff :
        ((circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ))).coeff a = 0 := by
      rw [hcenterI, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [ne_of_lt ha]
    have hface :=
      circularITangentPolynomial_comp_centered_coeff_eq_isotropic_second_face
        (G := G) (p := p) (a := a) ξ hmax hdegree hbound
    rw [hcenterCoeff] at hface
    have hscalar : (2 : ℂ) ^ p * Complex.I ^ a ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ Complex.I_ne_zero)
    exact (mul_eq_zero.mp hface.symm).resolve_left hscalar
  have hcolumn : ∀ b < p, MvPolynomial.coeff (isotropicFaceExponent p b) Qc = 0 := by
    intro b hb
    have hcenterCoeff :
        ((circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star ξ))).coeff b = 0 := by
      rw [hcenterJ, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [ne_of_lt hb]
    have hface :=
      circularJTangentPolynomial_comp_centered_coeff_eq_isotropic_first_face
        (G := G) (p := p) (b := b) ξ hmax hdegree hbound
    rw [hcenterCoeff] at hface
    have hscalar : (2 : ℂ) ^ p * (-Complex.I) ^ b ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
    exact (mul_eq_zero.mp hface.symm).resolve_left hscalar
  have hcorner : MvPolynomial.coeff (bivariateCornerExponent p) Qc ≠ 0 := by
    have hcenterCoeff :
        ((circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ))).coeff p ≠ 0 := by
      rw [hcenterI, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
      exact Polynomial.leadingCoeff_ne_zero.mpr hI
    have hface :=
      circularITangentPolynomial_comp_centered_coeff_eq_isotropic_second_face
        (G := G) (p := p) (a := p) ξ hmax hdegree hbound
    have hproduct :
        (2 : ℂ) ^ p * Complex.I ^ p *
          MvPolynomial.coeff (isotropicFaceExponent p p) Qc ≠ 0 := by
      rw [← hface]
      exact hcenterCoeff
    have hcornerFace : MvPolynomial.coeff (isotropicFaceExponent p p) Qc ≠ 0 :=
      (mul_ne_zero_iff.mp hproduct).2
    simpa only [bivariateCornerExponent, isotropicFaceExponent] using hcornerFace
  have htotal : Qc.totalDegree = 2 * p := by
    apply Nat.le_antisymm (totalDegree_le_two_mul_of_bidegreeBound p hbound)
    have hmem : bivariateCornerExponent p ∈ Qc.support :=
      MvPolynomial.mem_support_iff.mpr hcorner
    have hle := MvPolynomial.le_totalDegree hmem
    simpa [bivariateCornerExponent, Finsupp.degree_eq_sum, Finsupp.sum_fintype,
      Fin.sum_univ_two, two_mul] using hle
  obtain ⟨c, R, hc, hform, hR⟩ :=
    exists_bivariate_corner_normal_form Qc p hp hbound htotal
      (by simpa only [isotropicFaceExponent] using hrow)
      (by simpa only [isotropicFaceExponent] using hcolumn)
  refine ⟨c, R, hc, ?_, hR⟩
  simpa only [Qc, Q] using hform


theorem IsMaximallyCircular.exists_centered_isotropic_corner_normal_form
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (hdegree : G.totalDegree = 2 * p) (hp : 0 < p)
    (hroots : (circularITangentPolynomial G).roots.toFinset.card = 1) :
    ∃ ξ c : ℂ, ∃ R : BidegreePolynomial ℂ,
      c ≠ 0 ∧
        isotropicTranslationEquiv ξ
            (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) =
          MvPolynomial.monomial (bivariateCornerExponent p) c + R ∧
        BidegreeBound (p - 1) R := by
  have hI : circularITangentPolynomial G ≠ 0 :=
    hmax.circularITangentPolynomial_ne_zero hG
  have hIdegree : (circularITangentPolynomial G).natDegree = p :=
    hmax.circularITangentPolynomial_natDegree hG hdegree
  obtain ⟨ξ, hcenterI, hcenterJ⟩ :=
    exists_simultaneously_centered_circular_tangent_polynomials hI hIdegree hroots
  obtain ⟨c, R, hc, hform, hR⟩ :=
    hmax.centered_isotropic_corner_normal_form_of_tangent_identities
      hG hdegree hp ξ hcenterI hcenterJ
  exact ⟨ξ, c, R, hc, hform, hR⟩

end Esgk
end

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__bivariateCornerMonomial_one (c : ℂ) :
    MvPolynomial.monomial (bivariateCornerExponent 1) c =
      MvPolynomial.C c * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [MvPolynomial.monomial_eq]
  simp [bivariateCornerExponent, Finsupp.prod_fintype, Fin.prod_univ_two]

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__bidegreeBound_zero_eq_C (R : BidegreePolynomial ℂ)
    (hR : BidegreeBound 0 R) :
    R = MvPolynomial.C (R.coeff 0) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  have hdegree := totalDegree_le_two_mul_of_bidegreeBound 0 hR
  omega

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__isotropicTranslationCenter_zw (ξ : ℂ) :
    planeIsotropicCoordinateEquiv.symm
        ((isotropicTranslationEquiv ξ).symm
          (MvPolynomial.X 0 * MvPolynomial.X 1)) =
      realToComplexPlanePolynomial
        (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) := by
  rcases ξ with ⟨a, b⟩
  simp [planeIsotropicCoordinateEquiv_symm_apply, isotropicTranslationEquiv_symm_apply,
    inverseIsotropicTranslation, isotropicToPlaneCoordinates, planeSquaredDistancePolynomial,
    realToComplexPlanePolynomial, bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter]
  have hmk : ({ re := a, im := b } : ℂ) = (a : ℂ) + b * Complex.I := by
    apply Complex.ext <;> simp
  have hstar : (starRingEnd ℂ) ({ re := a, im := b } : ℂ) =
      (a : ℂ) - b * Complex.I := by
    apply Complex.ext <;> simp
  rw [hstar, hmk]
  simp only [map_add, map_sub, map_mul]
  ring_nf
  rw [show (MvPolynomial.C Complex.I : ComplexPlanePoly) ^ 2 = -1 by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]]
  ring

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__realToComplex_eq_centered_corner_one
    {G : PachDeZeeuw.Algebraic.PlanePoly} {ξ c : ℂ} {R : BidegreePolynomial ℂ}
    (hform :
      isotropicTranslationEquiv ξ
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) =
        MvPolynomial.monomial (bivariateCornerExponent 1) c + R)
    (hR : BidegreeBound 0 R) :
    realToComplexPlanePolynomial G =
      MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C (R.coeff 0) := by
  have hRconst : R = MvPolynomial.C (R.coeff 0) :=
    inline_Esgk_MaximallyCircularDegreeTwoCircle__bidegreeBound_zero_eq_C R hR
  calc
    realToComplexPlanePolynomial G =
        planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm
            (isotropicTranslationEquiv ξ
              (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))) := by
                rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    _ = planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm
            (MvPolynomial.monomial (bivariateCornerExponent 1) c + R)) := by rw [hform]
    _ = planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm
            (MvPolynomial.C c * (MvPolynomial.X 0 * MvPolynomial.X 1) +
              MvPolynomial.C (R.coeff 0))) := by
            nth_rewrite 1 [hRconst]
            congr 3
            exact inline_Esgk_MaximallyCircularDegreeTwoCircle__bivariateCornerMonomial_one c
    _ = planeIsotropicCoordinateEquiv.symm
            ((isotropicTranslationEquiv ξ).symm (MvPolynomial.C c)) *
          planeIsotropicCoordinateEquiv.symm
            ((isotropicTranslationEquiv ξ).symm
              (MvPolynomial.X 0 * MvPolynomial.X 1)) +
        planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm (MvPolynomial.C (R.coeff 0))) := by
            rw [map_add, map_add, map_mul, map_mul]
    _ = MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C (R.coeff 0) := by
          rw [inline_Esgk_MaximallyCircularDegreeTwoCircle__isotropicTranslationCenter_zw]
          simp [planeIsotropicCoordinateEquiv_symm_apply, isotropicTranslationEquiv_symm_apply]

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__centered_map_scalar_eq
    {G : PachDeZeeuw.Algebraic.PlanePoly} {ξ c d : ℂ}
    (hmap : realToComplexPlanePolynomial G =
      MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C d) :
    Complex.ofReal (G.coeff (Finsupp.single 0 2)) = c := by
  have hdistcoeff :
      (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)).coeff
          (Finsupp.single (0 : Fin 2) 2) = 1 := by
    have htop := congrArg
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2))
      (homogeneousComponent_two_planeSquaredDistancePolynomial
        (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ))
    rw [MvPolynomial.coeff_homogeneousComponent] at htop
    have hsingle : Finsupp.single (1 : Fin 2) 2 ≠ Finsupp.single 0 2 := by
      intro h
      have hzero := DFunLike.congr_fun h 0
      simp at hzero
    simpa [planeRadialQuadratic, MvPolynomial.coeff_add,
      MvPolynomial.coeff_X_pow, hsingle] using htop
  have hcoeff := congrArg
    (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)) hmap
  change MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)
      (MvPolynomial.map Complex.ofRealHom G) =
    MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)
      (MvPolynomial.C c * MvPolynomial.map Complex.ofRealHom
        (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
          MvPolynomial.C d) at hcoeff
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, hdistcoeff, MvPolynomial.coeff_C] at hcoeff
  have he : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 := by
    intro h
    have hzero := DFunLike.congr_fun h 0
    simp at hzero
  simpa [he] using hcoeff

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__isCircleFactor_of_centered_map
    {G : PlanePoly} {ξ c d : ℂ} (hc : c ≠ 0)
    (hmap : realToComplexPlanePolynomial G =
      MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C d)
    {x : _root_.Point2} (hx : x ∈ PlaneCurveZeroSet G) :
    IsCircleFactor G := by
  let center : _root_.Point2 := bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ
  let scalar : ℝ := G.coeff (Finsupp.single 0 2)
  have hcReal : Complex.ofReal scalar = c := by
    simpa only [scalar] using inline_Esgk_MaximallyCircularDegreeTwoCircle__centered_map_scalar_eq hmap
  have hxzero : MvPolynomial.eval (fun i : Fin 2 ↦ x i) G = 0 :=
    mem_PlaneCurveZeroSet.mp hx
  have hevalComplexification (F : PlanePoly) :
      MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))
          (realToComplexPlanePolynomial F) =
        Complex.ofReal (MvPolynomial.eval (fun i : Fin 2 ↦ x i) F) := by
    have hfun : (fun i : Fin 2 ↦ Complex.ofReal (x i)) =
        (Complex.ofRealHom ∘ fun i : Fin 2 ↦ x i) := by
      rfl
    rw [realToComplexPlanePolynomial, MvPolynomial.eval_map, hfun,
      ← MvPolynomial.eval_map]
    exact (MvPolynomial.map_eval Complex.ofRealHom (fun i : Fin 2 ↦ x i) F).symm
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))) hmap
  have hleft :
      MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))
          (realToComplexPlanePolynomial G) = 0 := by
    simpa [hxzero] using hevalComplexification G
  have hdistEval :
      MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))
          (realToComplexPlanePolynomial (planeSquaredDistancePolynomial center)) =
        Complex.ofReal (dist x center ^ 2) := by
    rw [hevalComplexification, eval_planeSquaredDistancePolynomial]
  have heval' :
      0 = c * Complex.ofReal (dist x center ^ 2) + d := by
    simpa only [center, hleft, map_add, map_mul, MvPolynomial.eval_C,
      hdistEval] using heval
  have hd : d = -c * Complex.ofReal (dist x center ^ 2) := by
    calc
      d = (c * Complex.ofReal (dist x center ^ 2) + d) -
          c * Complex.ofReal (dist x center ^ 2) := by ring
      _ = 0 - c * Complex.ofReal (dist x center ^ 2) := by rw [← heval']
      _ = -c * Complex.ofReal (dist x center ^ 2) := by ring
  have hscalar : scalar ≠ 0 := by
    intro hzero
    apply hc
    simpa [hzero] using hcReal.symm
  have hreal :
      G = MvPolynomial.C scalar * circleEquationPolynomial center (dist x center) := by
    apply MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
    change MvPolynomial.map Complex.ofRealHom G = MvPolynomial.map Complex.ofRealHom
      (MvPolynomial.C scalar * circleEquationPolynomial center (dist x center))
    rw [map_mul, MvPolynomial.map_C, circleEquationPolynomial, map_sub,
      MvPolynomial.map_C]
    have hmap' : MvPolynomial.map Complex.ofRealHom G =
        MvPolynomial.C c * MvPolynomial.map Complex.ofRealHom
            (planeSquaredDistancePolynomial center) + MvPolynomial.C d := by
      simpa only [realToComplexPlanePolynomial, center] using hmap
    have hcReal' : Complex.ofRealHom scalar = c := hcReal
    rw [hmap', hcReal', hd]
    simp only [map_neg, map_mul]
    have hofRealHom_apply (t : ℝ) : Complex.ofRealHom t = (t : ℂ) := rfl
    rw [hofRealHom_apply]
    rw [Complex.ofReal_pow]
    ring
  refine ⟨center, dist x center, dist_nonneg, ?_⟩
  rw [hreal]
  exact associated_unit_mul_left _ _
    ((isUnit_iff_ne_zero.mpr hscalar).map (MvPolynomial.C : ℝ →+* PlanePoly))

 
theorem isCircleFactor_of_maximallyCircular_degree_two_of_real_zero
    {H : PlanePoly} (hH : H ≠ 0) (hmax : IsMaximallyCircular H)
    (hdegree : H.totalDegree = 2) {x : _root_.Point2}
    (hx : x ∈ PlaneCurveZeroSet H) :
    IsCircleFactor H := by
  have hdegreeOne : H.totalDegree = 2 * 1 := by omega
  have hqdegree : (circularITangentPolynomial H).natDegree = 1 :=
    hmax.circularITangentPolynomial_natDegree hH hdegreeOne
  have hrootpos : 0 < (circularITangentPolynomial H).roots.toFinset.card := by
    apply Polynomial.roots_toFinset_card_pos_of_natDegree_pos
    rw [hqdegree]
    omega
  have hrootle : (circularITangentPolynomial H).roots.toFinset.card ≤ 1 := by
    calc
      (circularITangentPolynomial H).roots.toFinset.card ≤
          (circularITangentPolynomial H).roots.card :=
        (circularITangentPolynomial H).roots.toFinset_card_le
      _ = (circularITangentPolynomial H).natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      _ = 1 := hqdegree
  have hrootcard : (circularITangentPolynomial H).roots.toFinset.card = 1 := by omega
  obtain ⟨ξ, c, R, hc, hform, hR⟩ :=
    hmax.exists_centered_isotropic_corner_normal_form hH hdegreeOne (by omega) hrootcard
  exact inline_Esgk_MaximallyCircularDegreeTwoCircle__isCircleFactor_of_centered_map hc
    (inline_Esgk_MaximallyCircularDegreeTwoCircle__realToComplex_eq_centered_corner_one hform hR) hx

end Esgk
end

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


namespace Esgk

open EuclideanGeometry
open PachDeZeeuw.Algebraic

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_totalDegree_le_one
    (x v : PachDeZeeuw.Algebraic.Point2) :
    (affineLinePolynomial x v).totalDegree ≤ 1 := by
  have hsub0 :
      (MvPolynomial.X 0 - MvPolynomial.C (x 0) : PlanePoly).totalDegree ≤ 1 := by
    simpa using
      (MvPolynomial.totalDegree_sub_C_le
        (MvPolynomial.X 0 : PlanePoly) (x 0))
  have hsub1 :
      (MvPolynomial.X 1 - MvPolynomial.C (x 1) : PlanePoly).totalDegree ≤ 1 := by
    simpa using
      (MvPolynomial.totalDegree_sub_C_le
        (MvPolynomial.X 1 : PlanePoly) (x 1))
  have hterm0 :
      (MvPolynomial.C (v 1) *
        (MvPolynomial.X 0 - MvPolynomial.C (x 0)) : PlanePoly).totalDegree ≤ 1 := by
    calc
      _ ≤ (MvPolynomial.C (v 1) : PlanePoly).totalDegree +
          (MvPolynomial.X 0 - MvPolynomial.C (x 0) : PlanePoly).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simpa using hsub0
  have hterm1 :
      (MvPolynomial.C (v 0) *
        (MvPolynomial.X 1 - MvPolynomial.C (x 1)) : PlanePoly).totalDegree ≤ 1 := by
    calc
      _ ≤ (MvPolynomial.C (v 0) : PlanePoly).totalDegree +
          (MvPolynomial.X 1 - MvPolynomial.C (x 1) : PlanePoly).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simpa using hsub1
  have hsub := MvPolynomial.totalDegree_sub
      (MvPolynomial.C (v 1) * (MvPolynomial.X 0 - MvPolynomial.C (x 0)) : PlanePoly)
      (MvPolynomial.C (v 0) * (MvPolynomial.X 1 - MvPolynomial.C (x 1)))
  simpa [affineLinePolynomial] using hsub.trans (max_le hterm0 hterm1)

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_zeroSet_infinite
    {x v : PachDeZeeuw.Algebraic.Point2} (hv : v ≠ 0) :
    (PlaneCurveZeroSet (affineLinePolynomial x v)).Infinite := by
  let f : ℝ → PachDeZeeuw.Algebraic.Point2 := fun t ↦ x + t • v
  have hf : Function.Injective f := by
    intro s t hst
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1
        apply hv
        ext i
        fin_cases i <;> assumption
      have hcoord := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 1) hst
      change x 1 + s * v 1 = x 1 + t * v 1 at hcoord
      have hst' : (s - t) * v 1 = 0 := by linarith
      rcases mul_eq_zero.mp hst' with hst' | hv1'
      · linarith
      · exact (hv1 hv1').elim
    · have hcoord := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hst
      change x 0 + s * v 0 = x 0 + t * v 0 at hcoord
      have hst' : (s - t) * v 0 = 0 := by linarith
      rcases mul_eq_zero.mp hst' with hst' | hv0'
      · linarith
      · exact (hv0 hv0').elim
  have hmem : ∀ t : ℝ, f t ∈ PlaneCurveZeroSet (affineLinePolynomial x v) := by
    intro t
    change MvPolynomial.eval (fun i ↦ (f t) i)
      (affineLinePolynomial x v) = 0
    rw [affineLinePolynomial_eval]
    change v 1 * (x 0 + t * v 0 - x 0) -
      v 0 * (x 1 + t * v 1 - x 1) = 0
    ring
  refine (Set.infinite_range_of_injective hf).mono ?_
  rintro z ⟨t, rfl⟩
  exact hmem t

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__line_set_eq_affineLinePolynomial_zeroSet
    {a b c : ℝ} (hab : (a, b) ≠ (0, 0)) :
    ∃ x v : PachDeZeeuw.Algebraic.Point2, v ≠ 0 ∧
      {p : PachDeZeeuw.Algebraic.Point2 | a * p 0 + b * p 1 = c} =
        PlaneCurveZeroSet (affineLinePolynomial x v) := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      exact hab (by simp [ha, hb])
    let x : PachDeZeeuw.Algebraic.Point2 := !₂[0, c / b]
    let v : PachDeZeeuw.Algebraic.Point2 := !₂[-b, 0]
    refine ⟨x, v, ?_, ?_⟩
    · intro hv
      have h0 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hv
      have h1 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 1) hv
      simp [v] at h0 h1
      exact hb (by simpa using h0)
    · rw [affineLinePolynomial_zeroSet_eq_line]
      ext p
      simp [x, v, ha, hb, sub_eq_zero, eq_div_iff hb, mul_comm]
  · let x : PachDeZeeuw.Algebraic.Point2 := !₂[c / a, 0]
    let v : PachDeZeeuw.Algebraic.Point2 := !₂[-b, a]
    refine ⟨x, v, ?_, ?_⟩
    · intro hv
      have h0 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hv
      have h1 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 1) hv
      simp [v] at h0 h1
      exact ha (by simpa using h1)
    · rw [affineLinePolynomial_zeroSet_eq_line]
      ext p
      simp only [Set.mem_ofPred_eq]
      simp [x, v]
      constructor <;> intro h
      · field_simp [ha] at h ⊢
        linarith
      · field_simp [ha] at h ⊢
        linarith

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__irreducible_totalDegree_pos
    {G : PlanePoly} (hG : Irreducible G) : 0 < G.totalDegree := by
  apply Nat.pos_of_ne_zero
  intro hdegree
  apply hG.not_isUnit
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨G.coeff 0, ?_, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree⟩
  rw [isUnit_iff_ne_zero]
  intro hcoeff
  apply hG.ne_zero
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree, hcoeff, map_zero]

theorem IsMaximallyCircular.two_le_totalDegree_of_irreducible
    {G : PlanePoly} (hmax : IsMaximallyCircular G)
    (hG : Irreducible G) : 2 ≤ G.totalDegree := by
  have hpos := inline_Esgk_MaximallyCircularRealCarrierNondegenerate__irreducible_totalDegree_pos hG
  have heven := hmax.1
  omega

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__totalDegree_le_of_dvd
    {G q : PlanePoly} (hG : G ∣ q) (hq : q ≠ 0) :
    G.totalDegree ≤ q.totalDegree :=
  MvPolynomial.totalDegree_le_of_dvd_of_isDomain hG hq


theorem maximallyCircular_realCarrier_not_isLineOrCircle
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    {a b : PachDeZeeuw.Algebraic.Point2} (ha : a ∈ PlaneCurveZeroSet G)
    (hb : b ∈ PlaneCurveZeroSet G) (hab : a ≠ b) :
    ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet G) := by
  intro hcontrolled
  have hGdegree : 2 ≤ G.totalDegree :=
    hmax.two_le_totalDegree_of_irreducible hGirreducible
  rcases hcontrolled with hline | hcircle
  · rcases hline with ⟨α, β, γ, habcoeff, hcarrier⟩
    obtain ⟨x, v, hv, hlinezero⟩ :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__line_set_eq_affineLinePolynomial_zeroSet habcoeff
    have hcarrier' : PlaneCurveZeroSet G =
        PlaneCurveZeroSet (affineLinePolynomial x v) :=
      hcarrier.trans hlinezero
    have hinf :
        (PlaneCurveZeroSet G ∩
          PlaneCurveZeroSet (affineLinePolynomial x v)).Infinite := by
      rw [hcarrier']
      simpa using inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_zeroSet_infinite hv
    have hdiv : G ∣ affineLinePolynomial x v :=
      dvd_of_infinite_irreducible_zeroSet_intersection hGirreducible hinf
    have hqzero : affineLinePolynomial x v ≠ 0 :=
      (affineLinePolynomial_irreducible hv).ne_zero
    have hGle : G.totalDegree ≤
        (affineLinePolynomial x v).totalDegree :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__totalDegree_le_of_dvd hdiv hqzero
    have hqle : (affineLinePolynomial x v).totalDegree ≤ 1 :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_totalDegree_le_one x v
    have hGleOne : G.totalDegree ≤ 1 := hGle.trans hqle
    omega
  · rcases hcircle with ⟨center, r, hcarrier⟩
    have haSphere : a ∈ Metric.sphere center r := hcarrier ▸ ha
    have hbSphere : b ∈ Metric.sphere center r := hcarrier ▸ hb
    have hrnonneg : 0 ≤ r := by
      have hdist := Metric.mem_sphere.mp haSphere
      linarith [dist_nonneg (x := a) (y := center)]
    have hr : 0 < r := by
      rcases lt_or_eq_of_le hrnonneg with hr | rfl
      · exact hr
      · have haa : a = center := by
          apply dist_eq_zero.mp
          simpa using (Metric.mem_sphere.mp haSphere)
        have hbb : b = center := by
          apply dist_eq_zero.mp
          simpa using (Metric.mem_sphere.mp hbSphere)
        exact False.elim (hab (haa.trans hbb.symm))
    have hqzero :
        PlaneCurveZeroSet (circleEquationPolynomial center r) = Metric.sphere center r :=
      circleEquationPolynomial_zeroSet center hr.le
    have hinf :
        (PlaneCurveZeroSet G ∩
          PlaneCurveZeroSet (circleEquationPolynomial center r)).Infinite := by
      rw [hcarrier, hqzero]
      simpa using sphere_infinite center hr
    have hdiv : G ∣ circleEquationPolynomial center r :=
      dvd_of_infinite_irreducible_zeroSet_intersection hGirreducible hinf
    have hqzero' : circleEquationPolynomial center r ≠ 0 :=
      circleEquationPolynomial_ne_zero center (ne_of_gt hr)
    have hGle : G.totalDegree ≤
        (circleEquationPolynomial center r).totalDegree :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__totalDegree_le_of_dvd hdiv hqzero'
    have hqdegree : (circleEquationPolynomial center r).totalDegree = 2 :=
      circleEquationPolynomial_totalDegree_eq center r
    have hGdegree_le_two : G.totalDegree ≤ 2 := by
      rw [hqdegree] at hGle
      exact hGle
    have hGdegree_eq_two : G.totalDegree = 2 := by
      have heven : 2 * planeCircularLocalOrderI G = G.totalDegree := hmax.1
      omega
    exact hnotCircle
      (isCircleFactor_of_maximallyCircular_degree_two_of_real_zero
        hGirreducible.ne_zero hmax hGdegree_eq_two ha)

end Esgk

end



































section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput Point4 auxCurve auxPointSet)

theorem finiteIncidenceCount_univ_auxPointPairCurveIncidence_eq_auxIncidences_card
    {d : ℕ} (X : PreparedBipartiteInput d) :
    finiteIncidenceCount
        (Finset.univ : Finset (X.P₂ × X.P₂))
        (Finset.univ : Finset (X.P₁ × X.P₁))
        (auxPointPairCurveIncidence X) =
      (PachDeZeeuw.auxIncidences X).card := by
  classical
  rw [finiteIncidenceCount_eq_card_filter_product, PachDeZeeuw.auxIncidences]
  refine Finset.card_bij
    (fun (a : (X.P₂ × X.P₂) × (X.P₁ × X.P₁)) _ ↦ (encodedAuxPoint
      ((a.1.1 : PachDeZeeuw.Algebraic.Point2),
        (a.1.2 : PachDeZeeuw.Algebraic.Point2)), a.2)) ?_ ?_ ?_
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    let pq : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 :=
      (a.1.1, a.1.2)
    have hpq : pq ∈ X.P₂.product X.P₂ :=
      Finset.mem_product.mpr ⟨a.1.1.property, a.1.2.property⟩
    have hpoint : encodedAuxPoint pq ∈ auxPointSet X := by
      dsimp [auxPointSet]
      exact Finset.mem_image.mpr ⟨pq, hpq, rfl⟩
    have hlabel : a.2 ∈ (Finset.univ : Finset (X.P₁ × X.P₁)) :=
      Finset.mem_univ _
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hpoint, hlabel⟩
    · exact ha'.2
  · intro a₁ ha₁ a₂ ha₂ hEq
    have hpq :
        ((a₁.1.1 : PachDeZeeuw.Algebraic.Point2),
          (a₁.1.2 : PachDeZeeuw.Algebraic.Point2)) =
        ((a₂.1.1 : PachDeZeeuw.Algebraic.Point2),
          (a₂.1.2 : PachDeZeeuw.Algebraic.Point2)) :=
      encodedAuxPoint_injective (congrArg Prod.fst hEq)
    apply Prod.ext
    · exact Prod.ext (Subtype.ext (congrArg Prod.fst hpq))
        (Subtype.ext (congrArg Prod.snd hpq))
    · exact congrArg (fun z : Point4 × (X.P₁ × X.P₁) ↦ z.2) hEq
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hpoint : b.1 ∈ auxPointSet X :=
      (Finset.mem_product.mp hb'.1).1
    obtain ⟨pq, hpq, hencode⟩ :=
      exists_encodedAuxPoint_eq_of_mem_auxPointSet X hpoint
    have hpq' := Finset.mem_product.mp hpq
    let pqlabel : X.P₂ × X.P₂ :=
      (⟨pq.1, hpq'.1⟩, ⟨pq.2, hpq'.2⟩)
    have hbcurve : encodedAuxPoint pq ∈ auxCurve X b.2.1 b.2.2 := by
      rw [hencode]
      exact hb'.2
    have hrel : auxPointPairCurveIncidence X pqlabel b.2 := by
      simpa [auxPointPairCurveIncidence, pqlabel] using hbcurve
    have hsource :
        ((pqlabel, b.2) :
          (X.P₂ × X.P₂) × (X.P₁ × X.P₁)) ∈
          ((Finset.univ : Finset (X.P₂ × X.P₂)).product
            (Finset.univ : Finset (X.P₁ × X.P₁))).filter
            (fun a ↦ auxPointPairCurveIncidence X a.1 a.2) := by
      refine Finset.mem_filter.mpr ⟨?_, hrel⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    refine ⟨⟨pqlabel, b.2⟩, hsource, ?_⟩
    apply Prod.ext
    · simpa [pqlabel] using hencode
    · rfl

end Esgk
end

end














section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput bipartiteDistances auxIncidences
  bipartiteDistances_card_le_distinctDistances_of_subset_disjoint)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)

theorem maximallyCircular_exists_balancedPreparedInput
    {G : PlanePoly} (hG : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2)
    (hS : (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G)
    (hcard : 2 ≤ S.card) :
    ∃ X : PreparedBipartiteInput G.totalDegree,
      SelfCurvePreparedInput X ∧
      X.C₂ = PlaneCurveZeroSet G ∧
      Disjoint X.P₁ X.P₂ ∧ X.P₁ ∪ X.P₂ = S ∧
      X.P₁.card ≤ 2 * X.P₂.card ∧
      X.P₂.card ≤ 2 * X.P₁.card ∧
      0 < X.P₁.card * X.P₂.card ∧
      S.card ^ 4 ≤ 64 * EuclideanGeometry.distinctDistances S *
        finiteIncidenceCount (Finset.univ : Finset (X.P₂ × X.P₂))
          (Finset.univ : Finset (X.P₁ × X.P₁))
          (auxPointPairCurveIncidence X) := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet G) :=
    maximallyCircular_realCarrier_not_isLineOrCircle hG hmax hnotCircle
      (hS ha) (hS hb) hab
  have hnotPlane : ¬ PlaneCurve.IsLineOrCircle (PlaneCurveZeroSet G) := by
    intro hcontrolled
    exact hnot (by simpa [PlaneCurve.IsLineOrCircle,
      CurveSymmetries.IsLineOrCircle] using hcontrolled)
  obtain ⟨P₁, P₂, hdisj, hunion, hP₁big, hP₂big⟩ :=
    PachDeZeeuw.split_finset_into_two_comparable_parts S hcard
  have hP₁ : (P₁ : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G := by
    intro p hp
    apply hS
    rw [← hunion]
    exact Finset.mem_union.mpr (Or.inl hp)
  have hP₂ : (P₂ : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G := by
    intro p hp
    apply hS
    rw [← hunion]
    exact Finset.mem_union.mpr (Or.inr hp)
  have hnotExceptional : ¬ PachDeZeeuw.ExceptionalCurvePair
      (PlaneCurveZeroSet G) (PlaneCurveZeroSet G) := by
    intro hExc
    exact hnotPlane (PachDeZeeuw.ExceptionalCurvePair.left_controlledDegenerate hExc)
  let X : PreparedBipartiteInput G.totalDegree :=
    { C₁ := PlaneCurveZeroSet G
      C₂ := PlaneCurveZeroSet G
      P₁ := P₁
      P₂ := P₂
      hC₁ := ⟨G, hG.ne_zero, le_rfl, hG, rfl⟩
      hC₂ := ⟨G, hG.ne_zero, le_rfl, hG, rfl⟩
      hP₁ := hP₁
      hP₂ := hP₂
      notExceptional := hnotExceptional
      assumption31 := PachDeZeeuw.assumption31Data_of_not_controlledDegenerate
        hnotPlane hnotPlane (by simpa using hdisj) hnotExceptional }
  have hsum : S.card = P₁.card + P₂.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hcmp₁ : P₁.card ≤ 2 * P₂.card := by omega
  have hcmp₂ : P₂.card ≤ 2 * P₁.card := by omega
  have hpos₁ : 0 < P₁.card := by omega
  have hpos₂ : 0 < P₂.card := by omega
  have hP₁sub : P₁ ⊆ S := by
    intro p hp
    rw [← hunion]
    exact Finset.mem_union.mpr (Or.inl hp)
  have hP₂sub : P₂ ⊆ S := by
    intro p hp
    rw [← hunion]
    exact Finset.mem_union.mpr (Or.inr hp)
  have hdist : (bipartiteDistances P₁ P₂).card ≤ EuclideanGeometry.distinctDistances S :=
    bipartiteDistances_card_le_distinctDistances_of_subset_disjoint hP₁sub hP₂sub hdisj
  have hlower : S.card ^ 4 ≤
      64 * (bipartiteDistances P₁ P₂).card * (auxIncidences X).card := by
    rw [hsum]
    exact balancedBipartiteIncidenceLowerBound X hcmp₁ hcmp₂
  refine ⟨X, rfl, rfl, hdisj, hunion, hcmp₁, hcmp₂,
    Nat.mul_pos hpos₁ hpos₂, ?_⟩
  rw [finiteIncidenceCount_univ_auxPointPairCurveIncidence_eq_auxIncidences_card]
  exact hlower.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 64 hdist))

end Esgk
end

end














section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open Filter PachDeZeeuw.Algebraic
open PachDeZeeuw (PreparedBipartiteInput)


theorem maximallyCircularQuarticDistinctDistances_of_raw_auxiliary
    (hRaw : MaximallyCircularRawAuxiliaryIncidenceStatement) :
    MaximallyCircularQuarticDistinctDistancesStatement := by
  classical
  rcases hRaw with ⟨K, hK, hEstimate⟩
  have hKpos : 0 < K := by omega
  have hCpos : 0 < (576 * K) ^ 3 := by positivity
  refine ⟨24 ^ 3, (576 * K) ^ 3, by norm_num, hCpos, ?_⟩
  intro G S hG hGabs hNotCircle hMax hS hThreshold
  have hdeg : 2 ≤ G.totalDegree :=
    hMax.two_le_totalDegree_of_irreducible hG
  have hScard2 : 2 ≤ S.card := by
    by_contra hsmall
    have hle : S.card ≤ 1 := by omega
    have hsquare : S.card ^ 2 ≤ 1 := by nlinarith
    have hdeg1 : 1 ≤ G.totalDegree := by omega
    have hdegpow : 1 ≤ G.totalDegree ^ 5 := by
      simpa using Nat.pow_le_pow_left hdeg1 5
    have hleft : 2 ≤ (24 : ℕ) ^ 3 * G.totalDegree ^ 5 := by nlinarith
    have hone : 2 ≤ S.card ^ 2 := hleft.trans hThreshold
    omega
  obtain ⟨X, hSelf, hC₂, hDisjoint, hUnion, hP₁, hP₂, hPos, hNatLower⟩ :=
    maximallyCircular_exists_balancedPreparedInput hG hMax hNotCircle S hS hScard2
  have hRawJ : ∀ j : ℕ, 24 * (G.totalDegree : ℝ) ≤ (j : ℝ) →
      (finiteIncidenceCount
        (Finset.univ : Finset (X.P₂ × X.P₂))
        (Finset.univ : Finset (X.P₁ × X.P₁))
        (auxPointPairCurveIncidence X) : ℝ) ≤
        (K : ℝ) * ((G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 /
            Real.sqrt (j : ℝ) +
          (G.totalDegree : ℝ) ^ 2 * (j : ℝ) * (S.card : ℝ) ^ 2 +
          (S.card : ℝ) ^ 2 +
          (G.totalDegree : ℝ) ^ 4 * (j : ℝ) ^ 2 +
          (G.totalDegree : ℝ) ^ 3 * (S.card : ℝ) ^ 2) := by
    intro j hj
    exact hEstimate G S X hG hGabs hNotCircle hMax hS hSelf hC₂
      hDisjoint hUnion hP₁ hP₂ hPos j (by exact_mod_cast hj)
  have hSpos : 0 < S.card := by
    omega
  let d : ℝ := G.totalDegree
  let N : ℝ := S.card
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast hSpos
  let I : ℝ := finiteIncidenceCount
    (Finset.univ : Finset (X.P₂ × X.P₂))
    (Finset.univ : Finset (X.P₁ × X.P₁))
    (auxPointPairCurveIncidence X)
  let D : ℝ := EuclideanGeometry.distinctDistances S
  have hthresholdR : (24 : ℝ) ^ 3 * d ^ 5 ≤ N ^ 2 := by
    dsimp [d, N]
    exact_mod_cast hThreshold
  have hlowerN : N ^ 4 ≤ 64 * D * I := by
    dsimp [N, D, I]
    exact_mod_cast hNatLower
  have hD : 0 < D := by
    by_contra hzero
    have hD0 : D = 0 := le_antisymm (le_of_not_gt hzero) (by positivity)
    have hLower := hlowerN
    rw [hD0] at hLower
    have hN4 : 0 < N ^ 4 := by positivity
    nlinarith
  have hOpt := fourthRootIncidenceOptimization_of_threshold
    (d := d) (N := N) (I := I) (D := D) (K := (K : ℝ))
    (by dsimp [d]; exact_mod_cast hdeg) hNpos
      (by exact_mod_cast hK) hD hthresholdR hRawJ hlowerN
  have hNat : S.card ^ 4 ≤ (576 * K) ^ 3 * G.totalDegree ^ 4 *
      (EuclideanGeometry.distinctDistances S) ^ 3 := by
    have hOpt2 := hOpt.2
    dsimp [d, N, D] at hOpt2
    exact_mod_cast hOpt2
  exact hNat

end Esgk
end

end























/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


open Esgk
section


theorem solution :
    MaximallyCircularQuarticDistinctDistancesStatement := by
  exact maximallyCircularQuarticDistinctDistances_of_raw_auxiliary
    maximally_circular_raw_auxiliary_incidence_bound

end
