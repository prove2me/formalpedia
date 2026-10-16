-- Prove2me | solution 1 for Esgk.distinct_distances_one_fourth_excess
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-16T06:26:51.344486+00:00
-- url     : https://prove2.me/submissions/ae053c63-0789-415c-a3d9-62b3519bd45f

import Theorems.Thm_Esgk_maximally_circular_quartic_distance_bound
import Definitions.Def_Esgk_ComplexPlaneConjugationDescent
import Definitions.Def_Esgk_ConnectedLocalHomeomorphReal
import Definitions.Def_Esgk_DistanceNewtonElementaryPolynomial
import Definitions.Def_Esgk_IrreduciblePlaneDistanceImageField
import Definitions.Def_Esgk_IrreduciblePlanePolynomialAlgEquivTransport
import Definitions.Def_Esgk_MaximallyCircularQuarticBootstrap
import Definitions.Def_Esgk_MultivariateEliminationResultant
import Definitions.Def_Esgk_NonabsolutePlanePointBound
import Definitions.Def_Esgk_PlaneHorizontalReflection
import Definitions.Def_Esgk_PlaneIsotropicCoordinates
import Definitions.Def_Esgk_PlaneRadialFiltration
import Definitions.Def_Esgk_RadialFiltrationCircularMultiplicity
import Definitions.Def_Esgk_SelfCurveCompleteSymmetryFamily
import Definitions.Def_Esgk_SharpResultantFiniteSetCount
import Definitions.Def_LeanFormalizations_PachDeZeeuw_ChartBridge
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearExists
import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
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
Authors: Adam McKenna
-/


open Filter

namespace Esgk

private lemma inline_Esgk_DeficiencyFourthRoot__fourth_root_le_mul {n s A : ℕ} (hA : 0 < A)
    (hn : n ≤ A * (s + 1) ^ 4) :
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (A + 1 : ℕ) * (s + 1) := by
  let B : ℕ := A + 1
  have hAB : A ≤ B := by simp [B]
  have hBpow : B ≤ B ^ 4 := Nat.le_pow (by norm_num)
  have hApow : A ≤ B ^ 4 := hAB.trans hBpow
  have hmul : A * (s + 1) ^ 4 ≤ B ^ 4 * (s + 1) ^ 4 :=
    Nat.mul_le_mul_right _ hApow
  have hpow : B ^ 4 * (s + 1) ^ 4 = (B * (s + 1)) ^ 4 := by
    rw [Nat.mul_pow]
  have hnat : n ≤ (B * (s + 1)) ^ 4 := hn.trans (hmul.trans_eq hpow)
  have hreal : (n : ℝ) ≤ ((B * (s + 1)) ^ 4 : ℕ) := by exact_mod_cast hnat
  have hroot := Real.rpow_le_rpow (show 0 ≤ (n : ℝ) by positivity) hreal
    (by norm_num : 0 ≤ (1 / 4 : ℝ))
  rw [Nat.cast_pow] at hroot
  rw [show (1 / 4 : ℝ) = (↑(4 : ℕ))⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at hroot
  simpa [B] using hroot


theorem eventually_fourth_root_excess_of_quartic_bound
    {P : ℕ → Type} {Q : ∀ n, P n → Prop} {K : ∀ n, P n → ℕ}
    (hA : ∃ A : ℕ, 0 < A ∧
      ∀ᶠ n : ℕ in Filter.atTop, ∀ p : P n, Q n p → ∃ σ : ℕ,
        (n - 1) + σ = 3 * K n p ∧ n ≤ A * (σ + 1) ^ 4) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ p : P n, Q n p →
      (n : ℝ) / 3 + c * (n : ℝ) ^ (1 / 4 : ℝ) ≤ K n p := by
  obtain ⟨A, hA, hbound⟩ := hA
  let B : ℕ := A + 1
  let c : ℝ := 1 / (6 * (B : ℝ))
  have hBpos : 0 < B := by simp [B]
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound, (Filter.eventually_ge_atTop ((4 * B) ^ 4 : ℕ))] with n hn hlarge p hp
  obtain ⟨σ, hsigma, hquartic⟩ := hn p hp
  let s : ℕ := σ + 1
  have hsroot : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (B : ℝ) * s := by
    simpa [B, s] using inline_Esgk_DeficiencyFourthRoot__fourth_root_le_mul hA hquartic
  have hlarge' : (4 * (B : ℝ)) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    have hncast : ((4 * B) ^ 4 : ℕ) ≤ n := hlarge
    have hnr : (((4 * B) ^ 4 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hncast
    have hpowroot := Real.rpow_le_rpow (show 0 ≤ (((4 * B) ^ 4 : ℕ) : ℝ) by positivity)
      hnr (by norm_num : 0 ≤ (1 / 4 : ℝ))
    rw [Nat.cast_pow] at hpowroot
    rw [show (1 / 4 : ℝ) = (↑(4 : ℕ))⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at hpowroot
    simpa [mul_pow] using hpowroot
  have hsroot_comm : (n : ℝ) ^ (1 / 4 : ℝ) ≤ (s : ℝ) * (B : ℝ) := by
    simpa [mul_comm] using hsroot
  have hsexcess : (2 : ℝ) + (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) ≤ (s : ℝ) := by
    have hsroot' : (n : ℝ) ^ (1 / 4 : ℝ) / (B : ℝ) ≤ s :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < B)).2 hsroot_comm
    have hhalf : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * B)).2
      linarith [hlarge']
    have haux : 2 + (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) ≤
        (n : ℝ) ^ (1 / 4 : ℝ) / (B : ℝ) := by
      calc
        2 + (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) ≤
            (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) +
              (n : ℝ) ^ (1 / 4 : ℝ) / (2 * (B : ℝ)) := by linarith
        _ = (n : ℝ) ^ (1 / 4 : ℝ) / (B : ℝ) := by ring
    exact haux.trans hsroot'
  have hrelr0 : ((n - 1 : ℕ) : ℝ) + (σ : ℝ) = ((3 * K n p : ℕ) : ℝ) := by
    exact_mod_cast hsigma
  have hrelr : ((n : ℝ) - 1) + (σ : ℝ) = 3 * (K n p : ℝ) := by
    have hbasepos : 0 < 4 * B := by omega
    have hbase : 1 ≤ (4 * B) ^ 4 :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hbasepos))
    have hn1 : 1 ≤ n := hbase.trans hlarge
    rw [Nat.cast_sub hn1] at hrelr0
    norm_num at hrelr0 ⊢
    exact hrelr0
  have hmain : (n : ℝ) / 3 + c * (n : ℝ) ^ (1 / 4 : ℝ) ≤ (K n p : ℝ) := by
    dsimp [c, s] at hsexcess ⊢
    norm_num [div_eq_mul_inv] at hsexcess ⊢
    linarith
  exact hmain

end Esgk

end

















section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

attribute [local instance] MvPolynomial.gradedAlgebra


theorem homogeneousComponent_mul_eq_sum_antidiagonal
    (d : ℕ) (f g : MvPolynomial σ R) :
    homogeneousComponent d (f * g) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal d,
        homogeneousComponent ij.1 f * homogeneousComponent ij.2 g := by
  classical
  have h := DirectSum.coe_mul_apply_eq_sum_antidiagonal (homogeneousSubmodule σ R)
    (DirectSum.decompose (homogeneousSubmodule σ R) f)
    (DirectSum.decompose (homogeneousSubmodule σ R) g) d
  rw [← DirectSum.decompose_mul (𝒜 := homogeneousSubmodule σ R) f g] at h
  simpa only [← DirectSum.Decomposition.decompose'_eq,
    decomposition.decompose'_apply] using h


end MvPolynomial
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

variable {σ R : Type*} [CommSemiring R]

attribute [local instance] MvPolynomial.gradedAlgebra


theorem homogeneousComponent_mul_of_totalDegree_le
    {f g : MvPolynomial σ R} {d e : ℕ}
    (hf : f.totalDegree ≤ d) (hg : g.totalDegree ≤ e) :
    homogeneousComponent (d + e) (f * g) =
      homogeneousComponent d f * homogeneousComponent e g := by
  classical
  have hcomponents :
      homogeneousComponent (d + e) (f * g) =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (d + e),
          homogeneousComponent ij.1 f * homogeneousComponent ij.2 g := by
    have h := DirectSum.coe_mul_apply_eq_sum_antidiagonal (homogeneousSubmodule σ R)
      (DirectSum.decompose (homogeneousSubmodule σ R) f)
      (DirectSum.decompose (homogeneousSubmodule σ R) g) (d + e)
    rw [← DirectSum.decompose_mul (𝒜 := homogeneousSubmodule σ R) f g] at h
    simpa only [← DirectSum.Decomposition.decompose'_eq,
      decomposition.decompose'_apply] using h
  rw [hcomponents]
  refine Finset.sum_eq_single (d, e) ?_ ?_
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    by_cases hdi : d < i
    · rw [homogeneousComponent_eq_zero i f (lt_of_le_of_lt hf hdi), zero_mul]
    · rw [not_lt_iff_eq_or_lt] at hdi
      rcases hdi with hdi | hid
      · subst i
        have hje : j = e := Nat.add_left_cancel hij
        subst j
        exact (hne rfl).elim
      · have hej : e < j := by
          have h := Nat.add_lt_add_right hid e
          rw [← hij] at h
          exact Nat.lt_of_add_lt_add_left h
        rw [homogeneousComponent_eq_zero j g (lt_of_le_of_lt hg hej), mul_zero]
  · simp


theorem homogeneousComponent_pow_of_totalDegree_le
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.totalDegree ≤ d) (t : ℕ) :
    homogeneousComponent (d * t) (f ^ t) = (homogeneousComponent d f) ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hpow : (f ^ t).totalDegree ≤ d * t := by
        calc
          (f ^ t).totalDegree ≤ t * f.totalDegree := totalDegree_pow f t
          _ ≤ t * d := Nat.mul_le_mul_left t hf
          _ = d * t := Nat.mul_comm _ _
      simpa [pow_succ, Nat.mul_succ, ih] using
        (homogeneousComponent_mul_of_totalDegree_le (f := f ^ t) (g := f)
          (d := d * t) (e := d) hpow hf)

end MvPolynomial
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


theorem eval_eq_eval_specializeRemainingVariables {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (z : Fin (n + 1) → ℝ) :
    MvPolynomial.eval z p =
      Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) p) := by
  have hcons : Fin.cons (z 0) (fun i : Fin n ↦ z i.succ) = z := by
    funext i
    exact Fin.cases (by simp) (fun j ↦ by simp) i
  calc
    MvPolynomial.eval z p =
        MvPolynomial.eval (Fin.cons (z 0) (fun i : Fin n ↦ z i.succ)) p := by rw [hcons]
    _ = Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) p) := by
      simpa [specializeRemainingVariables, headCurry] using
        (MvPolynomial.eval_eq_eval_mv_eval'
          (s := fun i : Fin n ↦ z i.succ) (y := z 0) p)

 
theorem resultant_specializeRemainingVariables {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) :
    Polynomial.resultant (specializeRemainingVariables x p) (specializeRemainingVariables x q)
        (headCurry p).natDegree (headCurry q).natDegree =
      MvPolynomial.eval x (headResultant p q) := by
  rw [specializeRemainingVariables, headResultant]
  exact Polynomial.resultant_map_map (headCurry p) (headCurry q)
    (headCurry p).natDegree (headCurry q).natDegree (MvPolynomial.eval x)

 
theorem eval_headResultant_eq_zero_of_common_zero {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (z : Fin (n + 1) → ℝ)
    (hpDegree : 0 < (headCurry p).natDegree)
    (hp : MvPolynomial.eval z p = 0) (hq : MvPolynomial.eval z q = 0) :
    MvPolynomial.eval (fun i ↦ z i.succ) (headResultant p q) = 0 := by
  have hpSpecialized :
      Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) p) = 0 := by
    rw [← eval_eq_eval_specializeRemainingVariables]
    exact hp
  have hqSpecialized :
      Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) q) = 0 := by
    rw [← eval_eq_eval_specializeRemainingVariables]
    exact hq
  have hpDegreeLe :
      (specializeRemainingVariables (fun i ↦ z i.succ) p).natDegree ≤
        (headCurry p).natDegree := by
    simpa [specializeRemainingVariables] using
      (Polynomial.natDegree_map_le
        (f := MvPolynomial.eval (fun i ↦ z i.succ)) (p := headCurry p))
  have hqDegreeLe :
      (specializeRemainingVariables (fun i ↦ z i.succ) q).natDegree ≤
        (headCurry q).natDegree := by
    simpa [specializeRemainingVariables] using
      (Polynomial.natDegree_map_le
        (f := MvPolynomial.eval (fun i ↦ z i.succ)) (p := headCurry q))
  obtain ⟨u, v, _, _, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      (f := specializeRemainingVariables (fun i ↦ z i.succ) p)
      (g := specializeRemainingVariables (fun i ↦ z i.succ) q)
      hpDegreeLe hqDegreeLe (Or.inl (Nat.ne_of_gt hpDegree))
  have hresultant :
      Polynomial.resultant
          (specializeRemainingVariables (fun i ↦ z i.succ) p)
          (specializeRemainingVariables (fun i ↦ z i.succ) q)
          (headCurry p).natDegree (headCurry q).natDegree = 0 := by
    have hzero :
        Polynomial.eval (z 0)
            (Polynomial.C
              (Polynomial.resultant
                (specializeRemainingVariables (fun i ↦ z i.succ) p)
                (specializeRemainingVariables (fun i ↦ z i.succ) q)
                (headCurry p).natDegree (headCurry q).natDegree)) = 0 := by
      rw [← hbezout]
      simp [hpSpecialized, hqSpecialized]
    simpa using hzero
  rw [← resultant_specializeRemainingVariables]
  exact hresultant

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

variable {R σ : Type*} [CommSemiring R]

 
theorem X_mem_idealOfVars (i : σ) : X i ∈ idealOfVars σ R :=
  Ideal.subset_span (Set.mem_range_self i)

 
theorem X_pow_mem_pow_idealOfVars (i : σ) (a : ℕ) :
    X i ^ a ∈ idealOfVars σ R ^ a :=
  Ideal.pow_mem_pow (X_mem_idealOfVars (R := R) i) a


theorem X_pow_mul_X_pow_mul_mem_pow_idealOfVars (i j : σ) (a b m : ℕ)
    (q : MvPolynomial σ R) (hm : m ≤ a + b) :
    X i ^ a * X j ^ b * q ∈ idealOfVars σ R ^ m := by
  apply (idealOfVars σ R ^ m).mul_mem_right q
  apply Ideal.pow_le_pow_right hm
  rw [pow_add]
  exact Ideal.mul_mem_mul (X_pow_mem_pow_idealOfVars (R := R) i a)
    (X_pow_mem_pow_idealOfVars (R := R) j b)


theorem X_pow_mul_mem_pow_idealOfVars_of_X_pow_dvd (i j : σ) (a b m : ℕ)
    (q : MvPolynomial σ R) (hm : m ≤ a + b) (hq : X i ^ a ∣ q) :
    X j ^ b * q ∈ idealOfVars σ R ^ m := by
  obtain ⟨r, rfl⟩ := hq
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    X_pow_mul_X_pow_mul_mem_pow_idealOfVars (R := R) i j a b m r hm

end MvPolynomial
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace MvPolynomial

noncomputable section

variable {R σ : Type*} [CommSemiring R]


theorem mem_pow_idealOfVars_iff_le_localOrder (m : ℕ) (p : MvPolynomial σ R) :
    p ∈ idealOfVars σ R ^ m ↔ (m : ℕ∞) ≤ localOrder p := by
  rw [mem_pow_idealOfVars_iff']
  constructor
  · intro h
    exact MvPowerSeries.nat_le_order fun d hd ↦ by simpa using h d hd
  · intro h d hd
    have hd' : ((Finsupp.degree d : ℕ) : ℕ∞) < localOrder p := by
      apply lt_of_lt_of_le _ h
      exact_mod_cast hd
    simpa [localOrder] using
      (MvPowerSeries.coeff_of_lt_order (f := (p : MvPowerSeries σ R)) hd')

 
theorem localOrder_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) :
    localOrder (p * q) = localOrder p + localOrder q := by
  simpa only [localOrder, coe_mul] using
    (MvPowerSeries.order_mul (p : MvPowerSeries σ R) (q : MvPowerSeries σ R))


end

end MvPolynomial

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open scoped BigOperators


theorem map_newtonElementaryFromPowerSums_of_succ
    {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →ₐ[ℚ] B) (P : ℕ → A) (Q : ℕ → B)
    (hP : ∀ t, f (P (t + 1)) = Q (t + 1)) (m : ℕ) :
    f (newtonElementaryFromPowerSums P m) = newtonElementaryFromPowerSums Q m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      cases m with
      | zero => simp [newtonElementaryFromPowerSums]
      | succ m =>
          rw [newtonElementaryFromPowerSums.eq_2, newtonElementaryFromPowerSums.eq_2]
          simp only [map_smul, map_mul, map_pow, map_neg, map_one, map_sum]
          apply congrArg (fun x : B ↦ ((m + 1 : ℚ)⁻¹) • x)
          apply congrArg (fun x : B ↦ (-1 : B) ^ (m + 2) * x)
          apply Finset.sum_congr rfl
          intro a _ha
          rw [ih (m - a.2) (Nat.lt_succ_of_le (Nat.sub_le _ _)), hP a.2]

private theorem inline_Esgk_NewtonElementaryFromPowerSums__multiset_mul_esymm_eq_sum_positive_power {A : Type*} [CommRing A]
    (s : Multiset A) (k : ℕ) :
    (k : A) * s.esymm k =
      (-1 : A) ^ (k + 1) *
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
          (-1 : A) ^ a.1 * s.esymm a.1 * (s.map fun x ↦ x ^ a.2).sum := by
  classical
  let value : s → A := fun x ↦ (x : A)
  have hesymm (i : ℕ) :
      MvPolynomial.eval value (MvPolynomial.esymm s A i) = s.esymm i := by
    simpa [MvPolynomial.aeval_def, value] using
      (MvPolynomial.aeval_esymm_eq_multiset_esymm (σ := s) (R := A) (S := A) i value)
  have hpsum (i : ℕ) :
      MvPolynomial.eval value (MvPolynomial.psum s A i) =
        (s.map fun x ↦ x ^ i).sum := by
    simp only [MvPolynomial.psum, map_sum, MvPolynomial.eval_X, map_pow]
    change ((Finset.univ : Finset s).val.map fun x : s ↦ (x : A) ^ i).sum = _
    exact congrArg Multiset.sum (Multiset.map_univ s fun x : A ↦ x ^ i)
  have hnewton := MvPolynomial.mul_esymm_eq_sum s A k
  have := congrArg (MvPolynomial.eval value) hnewton
  simpa [hesymm, hpsum] using this

private theorem inline_Esgk_NewtonElementaryFromPowerSums__multiset_mul_esymm_succ_eq_sum_positive_power {A : Type*} [CommRing A]
    (s : Multiset A) (m : ℕ) :
    (m + 1 : A) * s.esymm (m + 1) =
      (-1 : A) ^ (m + 2) *
        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
          (-1 : A) ^ a.1 * s.esymm a.1 * (s.map fun x ↦ x ^ (a.2 + 1)).sum := by
  simpa [Nat.lt_succ_iff] using
    (inline_Esgk_NewtonElementaryFromPowerSums__multiset_mul_esymm_eq_sum_positive_power s (m + 1))

private theorem inline_Esgk_NewtonElementaryFromPowerSums__inv_succ_smul_succ_mul {A : Type*} [CommRing A] [Algebra ℚ A]
    (m : ℕ) (x : A) :
    ((m + 1 : ℚ)⁻¹) • ((m + 1 : A) * x) = x := by
  calc
    ((m + 1 : ℚ)⁻¹) • ((m + 1 : A) * x) =
        ((m + 1 : ℚ)⁻¹) • ((m + 1 : ℚ) • x) := by
      simp [Algebra.smul_def]
    _ = ((m + 1 : ℚ)⁻¹ * (m + 1 : ℚ)) • x := (mul_smul _ _ _).symm
    _ = x := by
      have hm : (m + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      rw [inv_mul_cancel₀ hm, one_smul]


theorem newtonElementaryFromPowerSums_eq_esymm {A : Type*} [CommRing A] [Algebra ℚ A]
    (s : Multiset A) (m : ℕ) :
    newtonElementaryFromPowerSums (fun t ↦ (s.map fun x ↦ x ^ t).sum) m = s.esymm m := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
      cases m with
      | zero => rw [newtonElementaryFromPowerSums.eq_1, Multiset.esymm]; simp
      | succ m =>
          rw [newtonElementaryFromPowerSums.eq_2]
          have hsum :
              (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                  (-1 : A) ^ (m - a.2) *
                    newtonElementaryFromPowerSums
                      (fun t ↦ (s.map fun x ↦ x ^ t).sum) (m - a.2) *
                    (s.map fun x ↦ x ^ (a.2 + 1)).sum) =
                ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                  (-1 : A) ^ a.1 * s.esymm a.1 *
                    (s.map fun x ↦ x ^ (a.2 + 1)).sum := by
            apply Finset.sum_congr rfl
            intro a ha
            have haeq : m - a.2 = a.1 := by
              rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
              omega
            rw [haeq]
            rw [ih a.1]
            exact Finset.Nat.antidiagonal.fst_lt ha
          rw [hsum, ← inline_Esgk_NewtonElementaryFromPowerSums__multiset_mul_esymm_succ_eq_sum_positive_power]
          exact inline_Esgk_NewtonElementaryFromPowerSums__inv_succ_smul_succ_mul m (s.esymm (m + 1))

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

open scoped BigOperators

namespace Esgk

lemma fin_sum_val_add (a b : ℕ) :
    (∑ i : Fin (a + b), (i : ℕ)) =
      (∑ i : Fin a, (i : ℕ)) + (∑ i : Fin b, (i : ℕ)) + a * b := by
  rw [Fin.sum_univ_add]
  simp_rw [Fin.val_castAdd, Fin.val_natAdd, Nat.add_comm a]
  rw [Finset.sum_add_distrib]
  simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

lemma sylvester_selected_index_sum {m n : ℕ} (σ : Fin (m + n) → Fin (m + n))
    (hσ : Function.Bijective σ)
    (hl : ∀ i : Fin m, i.val ≤ (σ (Fin.castAdd n i)).val ∧
      (σ (Fin.castAdd n i)).val ≤ i.val + n)
    (hr : ∀ j : Fin n, j.val ≤ (σ (Fin.natAdd m j)).val ∧
      (σ (Fin.natAdd m j)).val ≤ j.val + m) :
    (∑ i : Fin m, ((σ (Fin.castAdd n i)).val - i.val)) +
      (∑ j : Fin n, ((σ (Fin.natAdd m j)).val - j.val)) = m * n := by
  have hsigma : (∑ x : Fin (m + n), (σ x).val) = ∑ x : Fin (m + n), x.val := by
    let e : Fin (m + n) ≃ Fin (m + n) := Equiv.ofBijective σ hσ
    simpa [e] using (e.sum_comp (fun x : Fin (m + n) => x.val))
  have hleft := Finset.sum_tsub_distrib (s := (Finset.univ : Finset (Fin m)))
    (f := fun i : Fin m => (σ (Fin.castAdd n i)).val) (g := fun i => i.val)
    (fun i _ => (hl i).1)
  have hright := Finset.sum_tsub_distrib (s := (Finset.univ : Finset (Fin n)))
    (f := fun j : Fin n => (σ (Fin.natAdd m j)).val) (g := fun j => j.val)
    (fun j _ => (hr j).1)
  rw [hleft, hright]
  have hAB : (∑ i : Fin m, i.val) ≤ ∑ i : Fin m, (σ (Fin.castAdd n i)).val :=
    Finset.sum_le_sum (fun i _ => (hl i).1)
  have hCD : (∑ j : Fin n, j.val) ≤ ∑ j : Fin n, (σ (Fin.natAdd m j)).val :=
    Finset.sum_le_sum (fun j _ => (hr j).1)
  have hcombine :
      (∑ i : Fin m, (σ (Fin.castAdd n i)).val) - ∑ i : Fin m, i.val +
        ((∑ j : Fin n, (σ (Fin.natAdd m j)).val) - ∑ j : Fin n, j.val) =
        ((∑ i : Fin m, (σ (Fin.castAdd n i)).val) +
          ∑ j : Fin n, (σ (Fin.natAdd m j)).val) -
        ((∑ i : Fin m, i.val) + ∑ j : Fin n, j.val) := by omega
  rw [hcombine]
  rw [← Fin.sum_univ_add (fun x : Fin (m + n) => (σ x).val)]
  rw [hsigma]
  rw [fin_sum_val_add]
  omega

lemma nat_sub_add_sub_le {a b c x y : ℕ} (hx : x ≤ a) (hy : y ≤ b) (hxy : x + y = c) :
    a - x + (b - y) ≤ a + b - c := by omega


theorem headResultant_totalDegree_le_weighted {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (d₁ d₂ : ℕ)
    (hpHead : (headCurry p).natDegree ≤ d₁)
    (hqHead : (headCurry q).natDegree ≤ d₂)
    (hp : ∀ k, ((headCurry p).coeff k).totalDegree ≤ d₁ - k)
    (hq : ∀ k, ((headCurry q).coeff k).totalDegree ≤ d₂ - k) :
    (headResultant p q).totalDegree ≤
      (headCurry q).natDegree * d₁ + (headCurry p).natDegree * d₂ -
        (headCurry p).natDegree * (headCurry q).natDegree := by
  classical
  rw [headResultant, Polynomial.resultant, Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  by_cases hterm : ∏ i : Fin ((headCurry p).natDegree + (headCurry q).natDegree),
      Polynomial.sylvester (headCurry p) (headCurry q)
        (headCurry p).natDegree (headCurry q).natDegree (σ i) i = 0
  · rw [hterm]
    change 0 ≤ _
    omega
  · apply (MvPolynomial.totalDegree_smul_le _ _).trans
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    rw [Fin.sum_univ_add]
    let m := (headCurry p).natDegree
    let k := (headCurry q).natDegree
    have hprod (i : Fin (m + k)) :
        Polynomial.sylvester (headCurry p) (headCurry q) m k (σ i) i ≠ 0 := by
      exact (Finset.prod_ne_zero_iff.mp hterm) i (Finset.mem_univ i)
    have hl (i : Fin m) :
        i.val ≤ (σ (Fin.castAdd k i)).val ∧
          (σ (Fin.castAdd k i)).val ≤ i.val + k := by
      have hi := hprod (Fin.castAdd k i)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hi
      split_ifs at hi with h
      · exact h
      · simp_all
    have hr (j : Fin k) :
        j.val ≤ (σ (Fin.natAdd m j)).val ∧
          (σ (Fin.natAdd m j)).val ≤ j.val + m := by
      have hi := hprod (Fin.natAdd m j)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hi
      split_ifs at hi with h
      · exact h
      · simp_all
    have hsel := sylvester_selected_index_sum σ σ.bijective hl hr
    have hleft : ∀ i : Fin m,
        (Polynomial.sylvester (headCurry p) (headCurry q) m k
          (σ (Fin.castAdd k i)) (Fin.castAdd k i)).totalDegree ≤
          d₂ - ((σ (Fin.castAdd k i)).val - i.val) := by
      intro i
      have hi := hprod (Fin.castAdd k i)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hi ⊢
      split_ifs with h
      · exact hq _
      · simp_all
    have hright : ∀ j : Fin k,
        (Polynomial.sylvester (headCurry p) (headCurry q) m k
          (σ (Fin.natAdd m j)) (Fin.natAdd m j)).totalDegree ≤
          d₁ - ((σ (Fin.natAdd m j)).val - j.val) := by
      intro j
      have hj := hprod (Fin.natAdd m j)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hj ⊢
      split_ifs with h
      · exact hp _
      · simp_all
    apply Nat.le_trans (Nat.add_le_add
      (Finset.sum_le_sum fun i _ => hleft i)
      (Finset.sum_le_sum fun j _ => hright j))
    have hqidx : ∀ i : Fin m, (σ (Fin.castAdd k i)).val - i.val ≤ d₂ := by
      intro i
      have hc : (headCurry q).coeff ((σ (Fin.castAdd k i)).val - i.val) ≠ 0 := by
        have hi := hprod (Fin.castAdd k i)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hi
        split_ifs at hi with h
        · exact hi
        · simp at hi
      exact (Polynomial.le_natDegree_of_ne_zero hc).trans hqHead
    have hpidx : ∀ j : Fin k, (σ (Fin.natAdd m j)).val - j.val ≤ d₁ := by
      intro j
      have hc : (headCurry p).coeff ((σ (Fin.natAdd m j)).val - j.val) ≠ 0 := by
        have hj := hprod (Fin.natAdd m j)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hj
        split_ifs at hj with h
        · exact hj
        · simp at hj
      exact (Polynomial.le_natDegree_of_ne_zero hc).trans hpHead
    rw [Finset.sum_tsub_distrib _ (fun i _ => hqidx i)]
    rw [Finset.sum_tsub_distrib _ (fun j _ => hpidx j)]
    have hc : (∑ _ : Fin m, d₂) = m * d₂ := by simp
    have hc' : (∑ _ : Fin k, d₁) = k * d₁ := by simp
    rw [hc, hc']
    have hQ : (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) ≤ m * d₂ := by
      calc
        (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) ≤ ∑ _ : Fin m, d₂ :=
          Finset.sum_le_sum fun i _ => hqidx i
        _ = m * d₂ := hc
    have hP : (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) ≤ k * d₁ := by
      calc
        (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) ≤ ∑ _ : Fin k, d₁ :=
          Finset.sum_le_sum fun j _ => hpidx j
        _ = k * d₁ := hc'
    have hsel' :
        (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) +
            (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) = m * k := by
      change (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) +
          (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) = m * k at hsel
      exact hsel
    rw [Nat.add_comm ((headCurry q).natDegree * d₁) ((headCurry p).natDegree * d₂)]
    exact nat_sub_add_sub_le hQ hP hsel'

theorem headResultant_totalDegree_le_weighted_mul {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (d₁ d₂ : ℕ)
    (hpHead : (headCurry p).natDegree ≤ d₁)
    (hqHead : (headCurry q).natDegree ≤ d₂)
    (hp : ∀ k, ((headCurry p).coeff k).totalDegree ≤ d₁ - k)
    (hq : ∀ k, ((headCurry q).coeff k).totalDegree ≤ d₂ - k) :
    (headResultant p q).totalDegree ≤ d₁ * d₂ := by
  apply (headResultant_totalDegree_le_weighted p q d₁ d₂ hpHead hqHead hp hq).trans
  let m := (headCurry p).natDegree
  let k := (headCurry q).natDegree
  have hmk : m * k ≤ k * d₁ := by
    simpa [m, k, Nat.mul_comm] using Nat.mul_le_mul_left k hpHead
  have hsplit : k * d₁ + m * d₂ - m * k = m * d₂ + (k * d₁ - m * k) := by
    rw [Nat.add_comm (k * d₁) (m * d₂), Nat.add_sub_assoc hmk]
  have hdiff : k * d₁ - m * k ≤ d₂ * (d₁ - m) := by
    calc
      k * d₁ - m * k = (d₁ - m) * k := by
        rw [Nat.mul_sub_right_distrib]
        ac_rfl
      _ ≤ d₂ * (d₁ - m) := by
        simpa [m, k, Nat.mul_comm] using Nat.mul_le_mul_right (d₁ - m) hqHead
  have hsplit_le : m * d₂ + (k * d₁ - m * k) ≤ d₁ * d₂ := by
    calc
      m * d₂ + (k * d₁ - m * k) ≤ m * d₂ + d₂ * (d₁ - m) :=
        Nat.add_le_add_left hdiff _
      _ = d₁ * d₂ := by
        have hd : m + (d₁ - m) = d₁ := Nat.add_sub_of_le hpHead
        rw [show m * d₂ = d₂ * m by ac_rfl]
        rw [← Nat.mul_add, hd]
        ac_rfl
  rw [show (headCurry q).natDegree * d₁ + (headCurry p).natDegree * d₂ -
      (headCurry p).natDegree * (headCurry q).natDegree =
      m * d₂ + (k * d₁ - m * k) by simpa [m, k] using hsplit]
  exact hsplit_le

theorem headResultant_totalDegree_le_totalDegree_mul {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) :
    (headResultant p q).totalDegree ≤ p.totalDegree * q.totalDegree := by
  have hpHead : (headCurry p).natDegree ≤ p.totalDegree := by
    change (MvPolynomial.finSuccEquiv ℝ n p).natDegree ≤ p.totalDegree
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree p 0
  have hqHead : (headCurry q).natDegree ≤ q.totalDegree := by
    change (MvPolynomial.finSuccEquiv ℝ n q).natDegree ≤ q.totalDegree
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree q 0
  have hp : ∀ k, ((headCurry p).coeff k).totalDegree ≤ p.totalDegree - k := by
    intro k
    change ((MvPolynomial.finSuccEquiv ℝ n p).coeff k).totalDegree ≤ p.totalDegree - k
    by_cases hk : (MvPolynomial.finSuccEquiv ℝ n p).coeff k = 0
    · simp [hk]
    · have hdegree := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le p k hk
      omega
  have hq : ∀ k, ((headCurry q).coeff k).totalDegree ≤ q.totalDegree - k := by
    intro k
    change ((MvPolynomial.finSuccEquiv ℝ n q).coeff k).totalDegree ≤ q.totalDegree - k
    by_cases hk : (MvPolynomial.finSuccEquiv ℝ n q).coeff k = 0
    · simp [hk]
    · have hdegree := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le q k hk
      omega
  exact headResultant_totalDegree_le_weighted_mul p q p.totalDegree q.totalDegree
    hpHead hqHead hp hq

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

open scoped BigOperators

private theorem inline_Esgk_NewtonConstantPowerSums__sum_range_neg_one_pow_mul_ringChoose {A : Type*}
    [CommRing A] [Algebra ℚ A] [BinomialRing A] (r : A) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (-1 : A) ^ k * Ring.choose r k) =
      (-1 : A) ^ m * Ring.choose (r - 1) m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hpascal :
          Ring.choose r (m + 1) =
            Ring.choose (r - 1) m + Ring.choose (r - 1) (m + 1) := by
        simpa only [sub_add_cancel] using (Ring.choose_succ_succ (r - 1) m)
      rw [hpascal]
      simp only [pow_succ]
      ring

private theorem inline_Esgk_NewtonConstantPowerSums__inv_succ_smul_succ_mul_const {A : Type*} [CommRing A] [Algebra ℚ A]
    (m : ℕ) (x : A) :
    ((m + 1 : ℚ)⁻¹) • ((m + 1 : A) * x) = x := by
  calc
    ((m + 1 : ℚ)⁻¹) • ((m + 1 : A) * x) =
        ((m + 1 : ℚ)⁻¹) • ((m + 1 : ℚ) • x) := by
      simp [Algebra.smul_def]
    _ = ((m + 1 : ℚ)⁻¹ * (m + 1 : ℚ)) • x := (mul_smul _ _ _).symm
    _ = x := by
      have hm : (m + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      rw [inv_mul_cancel₀ hm, one_smul]


theorem newtonElementaryFromPowerSums_const_eq_ringChoose {A : Type*}
    [CommRing A] [Algebra ℚ A] [BinomialRing A] (r : A) (m : ℕ) :
    newtonElementaryFromPowerSums (fun _ : ℕ ↦ r) m = Ring.choose r m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      cases m with
      | zero => simp [newtonElementaryFromPowerSums]
      | succ m =>
          rw [newtonElementaryFromPowerSums.eq_2]
          have hsum :
              (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                  (-1 : A) ^ (m - a.2) *
                    newtonElementaryFromPowerSums (fun _ : ℕ ↦ r) (m - a.2) * r) =
                (∑ k ∈ Finset.range (m + 1), (-1 : A) ^ k * Ring.choose r k) * r := by
            calc
              _ = ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                    (-1 : A) ^ a.1 * Ring.choose r a.1 * r := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  have haeq : m - a.2 = a.1 := by
                    rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
                    omega
                  rw [haeq, ih a.1 (Finset.Nat.antidiagonal.fst_lt ha)]
              _ = ∑ k ∈ Finset.range (m + 1),
                    ((-1 : A) ^ k * Ring.choose r k) * r := by
                  simpa using
                    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                      (fun i _ ↦ (-1 : A) ^ i * Ring.choose r i * r) m)
              _ = (∑ k ∈ Finset.range (m + 1),
                    (-1 : A) ^ k * Ring.choose r k) * r := by
                  rw [Finset.sum_mul]
          rw [hsum, inline_Esgk_NewtonConstantPowerSums__sum_range_neg_one_pow_mul_ringChoose]
          have hsign :
              (-1 : A) ^ (m + 2) *
                  (((-1 : A) ^ m * Ring.choose (r - 1) m) * r) =
                Ring.choose (r - 1) m * r := by
            have heven : Even (m + 2 + m) := ⟨m + 1, by omega⟩
            have hpow : (-1 : A) ^ (m + 2) * (-1 : A) ^ m = 1 := by
              rw [← pow_add, heven.neg_one_pow]
            calc
              _ = ((-1 : A) ^ (m + 2) * (-1 : A) ^ m) *
                    Ring.choose (r - 1) m * r := by ring
              _ = Ring.choose (r - 1) m * r := by rw [hpow, one_mul]
          rw [hsign]
          have hchoose :
              (m + 1 : A) * Ring.choose r (m + 1) =
                r * Ring.choose (r - 1) m := by
            simpa [Ring.choose_one_right, nsmul_eq_mul] using
              (Ring.choose_smul_choose r (n := m + 1) (k := 1) (by omega))
          rw [mul_comm (Ring.choose (r - 1) m) r, ← hchoose]
          exact inline_Esgk_NewtonConstantPowerSums__inv_succ_smul_succ_mul_const m (Ring.choose r (m + 1))


theorem ringChoose_neg_natCast_ne_zero {n m : ℕ} (hn : 0 < n) :
    Ring.choose (-(n : ℝ)) m ≠ 0 := by
  have hnm : 1 ≤ n + m := by omega
  have hcast :
      (n : ℝ) + (m : ℝ) - 1 = ((n + m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hnm]
    push_cast
    ring
  rw [Ring.choose_neg, hcast, Ring.choose_natCast, Units.smul_def, zsmul_eq_mul,
    Int.cast_negOnePow_natCast]
  apply mul_ne_zero
  · exact pow_ne_zero _ (by norm_num)
  · exact_mod_cast Nat.choose_ne_zero (by omega : m ≤ n + m - 1)

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

open PachDeZeeuw.Algebraic


theorem realIrreducibleNotAbsolutelyIrreduciblePointBound_indexed
    (hBound : RealIrreducibleNotAbsolutelyIrreduciblePointBoundStatement)
    {I : Type*} [DecidableEq I] (indices : Finset I) (point : I → PachDeZeeuw.Algebraic.Point2)
    {G : PlanePoly} (hG : Irreducible G) (hNonabsolute : ¬ IsAbsolutelyIrreducible G)
    (hInjective : Set.InjOn point (indices : Set I))
    (hZero : ∀ i ∈ indices, point i ∈ PlaneCurveZeroSet G) :
    4 * indices.card ≤ G.totalDegree ^ 2 := by
  classical
  have hImageSubset :
      ((indices.image point : Finset PachDeZeeuw.Algebraic.Point2) : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G := by
    intro x hx
    change x ∈ indices.image point at hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact hZero i hi
  have hImageBound := hBound G (indices.image point) hG hNonabsolute hImageSubset
  simpa [Finset.card_image_of_injOn hInjective] using hImageBound


theorem n_le_sq_of_degree_point_bounds {n s N d : ℕ}
    (hd : 0 < d) (hSelection : n * d ≤ 2 * s * N)
    (hPointBound : 4 * N ≤ d ^ 2) (hDegreeBound : d ≤ 2 * s) :
    n ≤ s ^ 2 := by
  have hCancelInput : (4 * n) * d ≤ (2 * s * d) * d := by
    calc
      (4 * n) * d = 4 * (n * d) := by ring
      _ ≤ 4 * (2 * s * N) := Nat.mul_le_mul_left 4 hSelection
      _ = (2 * s) * (4 * N) := by ring
      _ ≤ (2 * s) * (d ^ 2) := Nat.mul_le_mul_left (2 * s) hPointBound
      _ = (2 * s * d) * d := by ring
  have hFour : 4 * n ≤ 2 * s * d :=
    Nat.le_of_mul_le_mul_right hCancelInput hd
  have hDegreeScaled : 2 * s * d ≤ 4 * s ^ 2 := by
    calc
      2 * s * d ≤ 2 * s * (2 * s) := Nat.mul_le_mul_left (2 * s) hDegreeBound
      _ = 4 * s ^ 2 := by ring
  have hFourFinal : 4 * n ≤ 4 * s ^ 2 := hFour.trans hDegreeScaled
  omega


theorem n_le_sq_of_nonabsolute_normalizedFactor_point_bound
    (hBound : RealIrreducibleNotAbsolutelyIrreduciblePointBoundStatement)
    {I : Type*} [DecidableEq I] (indices : Finset I) (point : I → PachDeZeeuw.Algebraic.Point2)
    {F G : PlanePoly} {n s : ℕ}
    (hFactor : G ∈ UniqueFactorizationMonoid.normalizedFactors F)
    (hNonabsolute : ¬ IsAbsolutelyIrreducible G)
    (hInjective : Set.InjOn point (indices : Set I))
    (hZero : ∀ i ∈ indices, point i ∈ PlaneCurveZeroSet G)
    (hSelection : n * G.totalDegree ≤ 2 * s * indices.card)
    (hDegreeBound : G.totalDegree ≤ 2 * s) :
    n ≤ s ^ 2 := by
  have hPointBound : 4 * indices.card ≤ G.totalDegree ^ 2 :=
    realIrreducibleNotAbsolutelyIrreduciblePointBound_indexed hBound indices point
      (normalized_factor_irreducible hFactor) hNonabsolute hInjective hZero
  exact n_le_sq_of_degree_point_bounds
    (normalized_factor_totalDegree_pos hFactor) hSelection hPointBound hDegreeBound

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


theorem planeHomogenization_eq_sum (D : ℕ) (p : PlanePoly) :
    planeHomogenization D p =
      ∑ d ∈ Finset.range (D + 1), planeHomogenizedLayer D d p :=
  rfl


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
open scoped ComplexConjugate


@[simp]
theorem complexPlanePolynomialConjugation_apply (P : ComplexPlanePoly) :
    complexPlanePolynomialConjugation P = MvPolynomial.map (conj : ℂ →+* ℂ) P := by
  rfl

@[simp]
theorem complexPlanePolynomialConjugation_involutive (P : ComplexPlanePoly) :
    complexPlanePolynomialConjugation (complexPlanePolynomialConjugation P) = P := by
  rw [complexPlanePolynomialConjugation_apply, complexPlanePolynomialConjugation_apply,
    MvPolynomial.map_map]
  have hcomp : (conj : ℂ →+* ℂ).comp (conj : ℂ →+* ℂ) = RingHom.id ℂ := by
    ext z
    exact starRingEnd_self_apply z
  rw [hcomp, MvPolynomial.map_id]

@[simp]
theorem complexPlanePolynomialConjugation_realToComplex (p : PlanePoly) :
    complexPlanePolynomialConjugation (realToComplexPlanePolynomial p) =
      realToComplexPlanePolynomial p := by
  rw [complexPlanePolynomialConjugation_apply, realToComplexPlanePolynomial,
    MvPolynomial.map_map]
  have hcomp : (conj : ℂ →+* ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext r
    exact Complex.conj_ofReal r
  rw [hcomp]

private theorem inline_Esgk_ComplexPlaneConjugationDescent__complex_eq_of_conj_eq {z : ℂ} (h : conj z = z) :
    Complex.ofReal z.re = z := by
  exact Complex.conj_eq_iff_re.mp h

 
theorem exists_realToComplexPlanePolynomial_eq_of_conjugation_eq
    {P : ComplexPlanePoly}
    (hP : complexPlanePolynomialConjugation P = P) :
    ∃ p : PlanePoly, realToComplexPlanePolynomial p = P := by
  let p : PlanePoly := .ofCoeff <|
    Finsupp.mapRange Complex.re (by simp) (AddMonoidAlgebra.coeff P)
  refine ⟨p, ?_⟩
  change MvPolynomial.map Complex.ofRealHom
    (.ofCoeff <| Finsupp.mapRange Complex.re (by simp) (AddMonoidAlgebra.coeff P)) = P
  apply (MvPolynomial.map_mapRange_eq_iff Complex.ofRealHom Complex.re (by simp) P).mpr
  intro d
  have hd : conj (P.coeff d) = P.coeff d := by
    have hcoeff := congrArg (fun Q : ComplexPlanePoly ↦ Q.coeff d) hP
    simpa only [complexPlanePolynomialConjugation_apply, MvPolynomial.coeff_map] using hcoeff
  exact inline_Esgk_ComplexPlaneConjugationDescent__complex_eq_of_conj_eq hd

private theorem inline_Esgk_ComplexPlaneConjugationDescent__realToComplexPlanePolynomial_ne_zero_of_ne_zero {p : PlanePoly}
    (hp : p ≠ 0) : realToComplexPlanePolynomial p ≠ 0 := by
  exact (MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective).ne hp

 
theorem realToComplexPlanePolynomial_dvd_iff {A B : PlanePoly} (hA : A ≠ 0) :
    realToComplexPlanePolynomial A ∣ realToComplexPlanePolynomial B ↔ A ∣ B := by
  constructor
  · rintro ⟨Q, hQ⟩
    have hQfixed : complexPlanePolynomialConjugation Q = Q := by
      apply mul_left_cancel₀ (inline_Esgk_ComplexPlaneConjugationDescent__realToComplexPlanePolynomial_ne_zero_of_ne_zero hA)
      calc
        realToComplexPlanePolynomial A * complexPlanePolynomialConjugation Q =
            complexPlanePolynomialConjugation
              (realToComplexPlanePolynomial A * Q) := by
                rw [map_mul, complexPlanePolynomialConjugation_realToComplex]
        _ = complexPlanePolynomialConjugation (realToComplexPlanePolynomial B) := by rw [hQ]
        _ = realToComplexPlanePolynomial B := complexPlanePolynomialConjugation_realToComplex B
        _ = realToComplexPlanePolynomial A * Q := hQ
    obtain ⟨q, hq⟩ := exists_realToComplexPlanePolynomial_eq_of_conjugation_eq hQfixed
    refine ⟨q, ?_⟩
    apply (MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective)
    change realToComplexPlanePolynomial B = realToComplexPlanePolynomial (A * q)
    rw [map_mul, hq, hQ]
  · intro hAB
    exact map_dvd realToComplexPlanePolynomial hAB

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


theorem numDistances_le_numDistancesOrdered {n : ℕ} (p : Config n) :
    NumDistances p ≤ NumDistancesOrdered p := by
  unfold NumDistances NumDistancesOrdered OrderedDistanceValues EuclideanGeometry.distinctDistances Config.toFinset
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_image] at hr
  obtain ⟨pair, hpair_mem, hpair_dist⟩ := hr
  rw [Finset.mem_offDiag] at hpair_mem
  obtain ⟨hx_mem, hy_mem, hxy_ne⟩ := hpair_mem
  rw [Finset.mem_image] at hx_mem hy_mem
  obtain ⟨i, _, hpi⟩ := hx_mem
  obtain ⟨j, _, hpj⟩ := hy_mem
  rw [Finset.mem_image]
  refine ⟨(i, j), ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    intro (hij : i = j)
    apply hxy_ne
    rw [← hpi, ← hpj, hij]
  · simp only
    rw [hpi, hpj]
    exact hpair_dist


theorem numDistances_eq_numDistancesOrdered_of_injective {n : ℕ} {p : Config n}
    (hp : Function.Injective p) :
    NumDistances p = NumDistancesOrdered p := by
  unfold NumDistances NumDistancesOrdered OrderedDistanceValues EuclideanGeometry.distinctDistances Config.toFinset
  congr 1
  apply Finset.Subset.antisymm
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨pair, hpair_mem, hpair_dist⟩ := hr
    rw [Finset.mem_offDiag] at hpair_mem
    obtain ⟨hx_mem, hy_mem, hxy_ne⟩ := hpair_mem
    rw [Finset.mem_image] at hx_mem hy_mem
    obtain ⟨i, _, hpi⟩ := hx_mem
    obtain ⟨j, _, hpj⟩ := hy_mem
    rw [Finset.mem_image]
    refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      intro (hij : i = j)
      apply hxy_ne
      rw [← hpi, ← hpj, hij]
    · simp only
      rw [hpi, hpj]
      exact hpair_dist
  · intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨ij, hij_mem, hij_dist⟩ := hr
    rw [Finset.mem_filter] at hij_mem
    obtain ⟨_, hij_ne⟩ := hij_mem
    rw [Finset.mem_image]
    refine ⟨(p ij.1, p ij.2), ?_, hij_dist⟩
    rw [Finset.mem_offDiag]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.mem_image]; exact ⟨ij.1, Finset.mem_univ _, rfl⟩
    · rw [Finset.mem_image]; exact ⟨ij.2, Finset.mem_univ _, rfl⟩
    · intro h; exact hij_ne (hp h)


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

private theorem inline_Esgk_PlaneProjectiveHomogenizationMul__sum_antidiagonal_eq_sum_product_of_support
    {M : Type*} [AddCommMonoid M] (D degreeRight : ℕ) (F : ℕ × ℕ → M)
    (hF : ∀ ij, F ij ≠ 0 → ij.1 ≤ D ∧ ij.2 ≤ degreeRight) :
    ∑ k ∈ Finset.range (D + degreeRight + 1),
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, F ij =
      ∑ ij ∈ Finset.range (D + 1) ×ˢ Finset.range (degreeRight + 1), F ij := by
  classical
  let rectangle := Finset.range (D + 1) ×ˢ Finset.range (degreeRight + 1)
  have hfiber (k : ℕ) :
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, F ij =
        ∑ ij ∈ rectangle with ij.1 + ij.2 = k, F ij := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro ij hij
      simp only [Finset.mem_filter] at hij
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr hij.2
    · intro ij hij hnot
      by_contra hne
      have hijBounds := hF ij hne
      apply hnot
      simp only [Finset.mem_filter, rectangle, Finset.mem_product, Finset.mem_range,
        Nat.lt_add_one_iff]
      exact ⟨hijBounds, Finset.HasAntidiagonal.mem_antidiagonal.mp hij⟩
  have hmaps : ∀ ij ∈ rectangle, ij.1 + ij.2 ∈ Finset.range (D + degreeRight + 1) := by
    intro ij hij
    dsimp only [rectangle] at hij
    rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
    rw [Finset.mem_range] at hi hj ⊢
    omega
  calc
    ∑ k ∈ Finset.range (D + degreeRight + 1),
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, F ij =
        ∑ k ∈ Finset.range (D + degreeRight + 1),
          ∑ ij ∈ rectangle with ij.1 + ij.2 = k, F ij := by
      exact Finset.sum_congr rfl fun k _ ↦ hfiber k
    _ = ∑ ij ∈ rectangle, F ij := by
      exact Finset.sum_fiberwise_of_maps_to (f := F) (g := fun ij ↦ ij.1 + ij.2) hmaps
    _ = ∑ ij ∈ Finset.range (D + 1) ×ˢ Finset.range (degreeRight + 1), F ij := rfl

private theorem inline_Esgk_PlaneProjectiveHomogenizationMul__planeHomogenizedLayer_mul
    (D degreeRight i j : ℕ) (f g : PlanePoly) (hi : i ≤ D) (hj : j ≤ degreeRight) :
    planeHomogenizedLayer D i f * planeHomogenizedLayer degreeRight j g =
      realPlanePolynomialProjectiveEmbedding
          (MvPolynomial.homogeneousComponent i f * MvPolynomial.homogeneousComponent j g) *
        projectivePlaneZ ^ (D + degreeRight - (i + j)) := by
  rw [planeHomogenizedLayer, planeHomogenizedLayer]
  calc
    (realPlanePolynomialProjectiveEmbedding (MvPolynomial.homogeneousComponent i f) *
          projectivePlaneZ ^ (D - i)) *
        (realPlanePolynomialProjectiveEmbedding (MvPolynomial.homogeneousComponent j g) *
          projectivePlaneZ ^ (degreeRight - j)) =
        (realPlanePolynomialProjectiveEmbedding (MvPolynomial.homogeneousComponent i f) *
            realPlanePolynomialProjectiveEmbedding (MvPolynomial.homogeneousComponent j g)) *
          (projectivePlaneZ ^ (D - i) * projectivePlaneZ ^ (degreeRight - j)) := by
      ac_rfl
    _ = realPlanePolynomialProjectiveEmbedding
          (MvPolynomial.homogeneousComponent i f * MvPolynomial.homogeneousComponent j g) *
        projectivePlaneZ ^ ((D - i) + (degreeRight - j)) := by
      rw [map_mul, pow_add]
    _ = realPlanePolynomialProjectiveEmbedding
          (MvPolynomial.homogeneousComponent i f * MvPolynomial.homogeneousComponent j g) *
        projectivePlaneZ ^ (D + degreeRight - (i + j)) := by
      congr 2
      omega

 
theorem planeHomogenization_mul_of_totalDegree_le
    {D degreeRight : ℕ} {f g : PlanePoly} (hf : f.totalDegree ≤ D) (hg : g.totalDegree ≤ degreeRight) :
    planeHomogenization (D + degreeRight) (f * g) =
      planeHomogenization D f * planeHomogenization degreeRight g := by
  classical
  let F : ℕ × ℕ → ProjectivePlanePoly := fun ij ↦
    realPlanePolynomialProjectiveEmbedding
        (MvPolynomial.homogeneousComponent ij.1 f * MvPolynomial.homogeneousComponent ij.2 g) *
      projectivePlaneZ ^ (D + degreeRight - (ij.1 + ij.2))
  have hsupport : ∀ ij, F ij ≠ 0 → ij.1 ≤ D ∧ ij.2 ≤ degreeRight := by
    intro ij hij
    constructor
    · by_contra hi
      apply hij
      simp only [F]
      rw [MvPolynomial.homogeneousComponent_eq_zero ij.1 f
        (lt_of_le_of_lt hf (Nat.lt_of_not_ge hi))]
      simp
    · by_contra hj
      apply hij
      simp only [F]
      rw [MvPolynomial.homogeneousComponent_eq_zero ij.2 g
        (lt_of_le_of_lt hg (Nat.lt_of_not_ge hj))]
      simp
  have hleft :
      planeHomogenization (D + degreeRight) (f * g) =
        ∑ k ∈ Finset.range (D + degreeRight + 1),
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, F ij := by
    rw [planeHomogenization_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [planeHomogenizedLayer,
      MvPolynomial.homogeneousComponent_mul_eq_sum_antidiagonal, map_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro ij hij
    simp only [F]
    rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hij]
  have hright :
      planeHomogenization D f * planeHomogenization degreeRight g =
        ∑ ij ∈ Finset.range (D + 1) ×ˢ Finset.range (degreeRight + 1), F ij := by
    rw [planeHomogenization_eq_sum, planeHomogenization_eq_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
    refine Finset.sum_congr rfl ?_
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Nat.lt_add_one_iff] at hij
    exact inline_Esgk_PlaneProjectiveHomogenizationMul__planeHomogenizedLayer_mul D degreeRight ij.1 ij.2 f g hij.1 hij.2
  calc
    planeHomogenization (D + degreeRight) (f * g) =
        ∑ k ∈ Finset.range (D + degreeRight + 1),
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, F ij := hleft
    _ = ∑ ij ∈ Finset.range (D + 1) ×ˢ Finset.range (degreeRight + 1), F ij :=
      inline_Esgk_PlaneProjectiveHomogenizationMul__sum_antidiagonal_eq_sum_product_of_support D degreeRight F hsupport
    _ = planeHomogenization D f * planeHomogenization degreeRight g := hright.symm

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

open scoped BigOperators

namespace Esgk


private lemma inline_Esgk_SharpResultantFiniteSetCount__remainingEval_injective :
    Function.Injective (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) := by
  rw [← MvPolynomial.aeval_eq_eval]
  exact (MvPolynomial.aeval_injective_iff_of_isEmpty.mpr (RingHom.injective _))

private lemma inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_ne_zero
    (r : MvPolynomial (Fin 1) ℝ) (hr : r ≠ 0) :
    Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r) ≠ 0 := by
  apply (Polynomial.map_ne_zero_iff inline_Esgk_SharpResultantFiniteSetCount__remainingEval_injective).mpr
  intro h
  apply hr
  exact (MvPolynomial.finSuccEquiv ℝ 0).injective h

private lemma inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_natDegree_le
    (r : MvPolynomial (Fin 1) ℝ) :
    (Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)).natDegree ≤
      r.totalDegree := by
  calc
    (Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)).natDegree ≤
        (headCurry r).natDegree := Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 0 r := by
      simpa [headCurry] using (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 0) r)
    _ ≤ r.totalDegree := MvPolynomial.degreeOf_le_totalDegree r 0

private lemma inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_eval_eq_zero
    (r : MvPolynomial (Fin 1) ℝ) (z : Fin 2 → ℝ)
    (hz : MvPolynomial.eval (fun i : Fin 1 ↦ z i.succ) r = 0) :
    Polynomial.eval (z 1)
      (Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)) = 0 := by
  have hcoords :
      (fun i : Fin 1 ↦ z i.succ) = Fin.cons (z 1) bundle_Esgk_SharpResultantFiniteSetCount_remainingEval := by
    funext i
    fin_cases i
    rfl
  rw [hcoords] at hz
  simpa using
    (MvPolynomial.eval_eq_eval_mv_eval' (R := ℝ) bundle_Esgk_SharpResultantFiniteSetCount_remainingEval (z 1) r).symm ▸ hz


theorem common_zero_finset_card_le_totalDegree_mul
    (p q : MvPolynomial (Fin 2) ℝ) (S : Finset (Fin 2 → ℝ))
    (hpDegree : 0 < (headCurry p).natDegree)
    (hresultant : headResultant p q ≠ 0)
    (hprojection : Set.InjOn (fun z : Fin 2 → ℝ ↦ z 1) (S : Set (Fin 2 → ℝ)))
    (hzero : ∀ z ∈ S, MvPolynomial.eval z p = 0 ∧ MvPolynomial.eval z q = 0) :
    S.card ≤ p.totalDegree * q.totalDegree := by
  let r := headResultant p q
  let u : Polynomial ℝ := Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)
  let T : Finset ℝ := S.image (fun z : Fin 2 → ℝ ↦ z 1)
  have hcard : S.card = T.card := by
    exact (Finset.card_image_iff.mpr hprojection).symm
  have hr : r ≠ 0 := by
    simpa [r] using hresultant
  have hu : u ≠ 0 := by
    simpa [u] using inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_ne_zero r hr
  have hTsubset : (T : Set ℝ) ⊆ u.rootSet ℝ := by
    intro y hy
    change y ∈ T at hy
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hy
    rw [Polynomial.mem_rootSet_of_ne hu]
    exact inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_eval_eq_zero r z
      (eval_headResultant_eq_zero_of_common_zero p q z hpDegree
        (hzero z hzS).1 (hzero z hzS).2)
  have hTcard : T.card ≤ u.natDegree := by
    rw [← Set.ncard_coe_finset T]
    exact (Set.ncard_le_ncard hTsubset).trans (Polynomial.ncard_rootSet_le u ℝ)
  have huDegree : u.natDegree ≤ r.totalDegree := by
    simpa [u] using inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_natDegree_le r
  rw [hcard]
  exact hTcard.trans huDegree |>.trans
    (headResultant_totalDegree_le_totalDegree_mul p q)

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


namespace PachDeZeeuw.Algebraic

open MvPolynomial


@[simp] lemma shearPoint_apply (s : ℝ) (p : ℝ × ℝ) :
    shearPoint s p = (p.1 - s * p.2, p.2) := rfl


theorem evalPlane_shearPoly_shearPoint (s : ℝ) (h : PlanePoly) (p : ℝ × ℝ) :
    evalPlane (shearPoly s h) (shearPoint s p) = evalPlane h p := by
   
  set pt : Fin 2 → ℝ :=
    (fun i => if i = 0 then (shearPoint s p).1 else (shearPoint s p).2) with hpt
   
  have h1 : evalPlane (shearPoly s h) (shearPoint s p)
      = (MvPolynomial.aeval pt) (MvPolynomial.aeval (shearVars s) h) := by
    rw [shearPoly, evalPlane, MvPolynomial.aeval_eq_eval]
  rw [h1]
   
   
  rw [MvPolynomial.comp_aeval_apply]
   
  have hpt0 : pt 0 = p.1 - s * p.2 := rfl
  have hpt1 : pt 1 = p.2 := rfl
   
  have hvars : (fun i => (MvPolynomial.aeval pt) (shearVars s i))
      = (fun i : Fin 2 => if i = 0 then p.1 else p.2) := by
    funext i
    fin_cases i
    ·  
      show (MvPolynomial.aeval pt) (MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)
          = p.1
      rw [map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Algebra.algebraMap_self_apply, hpt0, hpt1]
      ring
    ·  
      show (MvPolynomial.aeval pt) (MvPolynomial.X 1) = p.2
      rw [MvPolynomial.aeval_X, hpt1]
  rw [hvars, evalPlane, MvPolynomial.aeval_eq_eval]


theorem totalDegree_aeval_le {R : Type*} [CommSemiring R] {σ τ : Type*}
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  have hsum : MvPolynomial.aeval f p
      = ∑ v ∈ p.support, MvPolynomial.aeval f (MvPolynomial.monomial v (MvPolynomial.coeff v p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [hsum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro v hv
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ v.support, (f i ^ v i).totalDegree
      ≤ ∑ i ∈ v.support, v i * (f i).totalDegree :=
        Finset.sum_le_sum (fun i _ => MvPolynomial.totalDegree_pow _ _)
    _ ≤ ∑ i ∈ v.support, v i * 1 :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (le_refl (v i)) (hf i))
    _ = v.sum (fun _ e => e) := by simp only [mul_one]; rfl
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hv


lemma shearVars_totalDegree_le (s : ℝ) (i : Fin 2) : (shearVars s i).totalDegree ≤ 1 := by
  unfold shearVars
  split
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact le_of_eq (totalDegree_X 0)
    · exact (totalDegree_mul _ _).trans (le_of_eq (by rw [totalDegree_C, totalDegree_X]))
  · exact le_of_eq (totalDegree_X 1)


theorem shearPoly_totalDegree_le (s : ℝ) (h : PlanePoly) :
    (shearPoly s h).totalDegree ≤ h.totalDegree := by
  unfold shearPoly
  exact totalDegree_aeval_le (shearVars s) (shearVars_totalDegree_le s) h

end PachDeZeeuw.Algebraic

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open Filter
open scoped Classical

variable {n : ℕ}


theorem fixedDistance_card_le_three {p : Config n}
    (hgp : InGeneralPosition (Config.toFinset p)) (c : Point) (r : ℝ) :
    ((Config.toFinset p).filter (fun x ↦ dist x c = r)).card ≤ 3 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq (s := (Config.toFinset p).filter (fun x ↦ dist x c = r)) (n := 4) (by omega)
  have hTX : T ⊆ Config.toFinset p := hTsub.trans (Finset.filter_subset _ _)
  have hcos : Cospherical (SetLike.coe T) := by
    refine ⟨c, r, ?_⟩
    intro x hx
    have hxT : x ∈ T := by simpa using hx
    have hxf := hTsub hxT
    rw [Finset.mem_filter] at hxf
    exact hxf.2
  exact hgp.2 T hTX hTcard hcos


end Esgk

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry

 
theorem distinctDistances_le_of_subset {U V : Finset Point} (hUV : U ⊆ V) :
    EuclideanGeometry.distinctDistances U ≤ EuclideanGeometry.distinctDistances V := by
  unfold EuclideanGeometry.distinctDistances
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_image] at hr ⊢
  obtain ⟨xy, hxy, rfl⟩ := hr
  rw [Finset.mem_offDiag] at hxy
  exact ⟨xy, Finset.mem_offDiag.mpr ⟨hUV hxy.1, hUV hxy.2.1, hxy.2.2⟩, rfl⟩


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


theorem eval_eq_evalPlane_chart (p : PlanePoly) (x : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i => x i) p = evalPlane p (chartEquiv x) := by
  unfold evalPlane
  refine congrArg (fun f => MvPolynomial.eval f p) ?_
  funext i
  fin_cases i <;> simp


end PachDeZeeuw.Algebraic

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


@[simp] lemma shearAlgEquiv_apply (s : ℝ) (h : PlanePoly) :
    shearAlgEquiv s h = shearPoly s h := by
  rw [shearAlgEquiv, AlgEquiv.ofAlgHom_apply]
  rfl


theorem irreducible_shearPoly_iff (s : ℝ) (h : PlanePoly) :
    Irreducible (shearPoly s h) ↔ Irreducible h := by
  rw [← shearAlgEquiv_apply s h]
  exact MulEquiv.irreducible_iff (shearAlgEquiv s)

end PachDeZeeuw.Algebraic

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq (m : Fin 2 →₀ ℕ) : (m.sum fun _ e => e) = m 0 + m 1 := by
  rw [Finsupp.sum, ← Finsupp.degree_apply, Finsupp.degree_eq_sum, Fin.sum_univ_two]

 
private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__sum_support_single (D : ℕ) :
    ∑ i ∈ (Finsupp.single (1 : Fin 2) D).support, (Finsupp.single (1 : Fin 2) D) i = D := by
  rw [← Finsupp.degree_apply, Finsupp.degree_single]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_single_one_pow (s : ℝ) (a : ℕ) :
    coeff (Finsupp.single (1 : Fin 2) a) ((X 0 + C s * X 1) ^ a) = s ^ a := by
  classical
  induction a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_add, coeff_add]
    have hX0 : coeff (Finsupp.single (1 : Fin 2) (n + 1)) ((X 0 + C s * X 1) ^ n * X 0) = 0 := by
      rw [coeff_mul_X', if_neg]; simp [Finsupp.mem_support_iff]
    have hX1 : coeff (Finsupp.single (1 : Fin 2) (n + 1)) ((X 0 + C s * X 1) ^ n * (C s * X 1))
        = s ^ (n + 1) := by
      rw [show (X 0 + C s * X 1 : PlanePoly) ^ n * (C s * X 1)
            = C s * ((X 0 + C s * X 1) ^ n * X 1) by ring, coeff_C_mul,
          show (Finsupp.single (1 : Fin 2) (n + 1))
            = (Finsupp.single (1 : Fin 2) n) + (Finsupp.single (1 : Fin 2) 1) by
              rw [← Finsupp.single_add], coeff_mul_X, ih]
      ring
    rw [hX0, hX1, zero_add]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__shear_monomial (s : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    shearPoly s (monomial m c) = C c * (X 0 + C s * X 1) ^ (m 0) * (X 1) ^ (m 1) := by
  unfold shearPoly shearVars
  rw [aeval_monomial, MvPolynomial.algebraMap_eq,
    Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [Fin.prod_univ_two, Fin.isValue, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  ring


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial (s : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    coeff (Finsupp.single (1 : Fin 2) (m 0 + m 1)) (shearPoly s (monomial m c))
      = c * s ^ (m 0) := by
  classical
  rw [inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__shear_monomial, X_pow_eq_monomial, mul_assoc, coeff_C_mul,
    show (Finsupp.single (1 : Fin 2) (m 0 + m 1))
        = (Finsupp.single (1 : Fin 2) (m 0)) + (Finsupp.single (1 : Fin 2) (m 1)) by
        rw [← Finsupp.single_add],
    coeff_mul_monomial, inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_single_one_pow, mul_one]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial_lt (s : ℝ) (D : ℕ) (m : Fin 2 →₀ ℕ) (c : ℝ)
    (hlt : m 0 + m 1 < D) :
    coeff (Finsupp.single (1 : Fin 2) D) (shearPoly s (monomial m c)) = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  rw [inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__sum_support_single]
  refine lt_of_le_of_lt (shearPoly_totalDegree_le s (monomial m c)) ?_
  refine lt_of_le_of_lt (totalDegree_monomial_le m c) ?_
  rw [Function.id_def, inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq]
  exact hlt


theorem coeff_yD_shear_eq_eval (h : PlanePoly) (s : ℝ) :
    coeff (Finsupp.single (1 : Fin 2) h.totalDegree) (shearPoly s h)
      = (shearTopPoly h).eval s := by
  classical
  set D := h.totalDegree with hD
  have hexp : shearPoly s h
      = ∑ m ∈ h.support, shearPoly s (monomial m (coeff m h)) := by
    conv_lhs => rw [h.as_sum]
    rw [shearPoly, map_sum]
    rfl
  rw [hexp, coeff_sum, shearTopPoly, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro m hm
  have hle : m 0 + m 1 ≤ D := by
    rw [hD, ← inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq m]; exact le_totalDegree hm
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [if_pos (heq.trans hD)]
    have hidx : (Finsupp.single (1 : Fin 2) D) = Finsupp.single (1 : Fin 2) (m 0 + m 1) := by
      rw [heq]
    rw [hidx, inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  · rw [if_neg (by omega), inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial_lt s D m (coeff m h) hlt]
    simp


theorem shearTopPoly_ne_zero (h : PlanePoly) (hh : h ≠ 0) : shearTopPoly h ≠ 0 := by
  classical
  set D := h.totalDegree with hD
  have hne : h.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m0, hm0, hsup⟩ :=
    Finset.exists_mem_eq_sup h.support hne (fun s => s.sum fun _ e => e)
  have hm0deg : m0 0 + m0 1 = D := by rw [← inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq m0, ← hsup]; rfl
  have hcoeff0 : coeff m0 h ≠ 0 := MvPolynomial.mem_support_iff.mp hm0
  intro hzero
  apply hcoeff0
  have hkey : (shearTopPoly h).coeff (m0 0) = coeff m0 h := by
    rw [shearTopPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single m0]
    · rw [if_pos hm0deg, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro m _ hmm0
      by_cases hmd : m 0 + m 1 = D
      · rw [if_pos hmd, Polynomial.coeff_C_mul_X_pow, if_neg]
        intro hm00
        apply hmm0
        have hm00' : m 0 = m0 0 := hm00.symm
        have hm1 : m 1 = m0 1 := by omega
        apply Finsupp.ext
        intro i
        match i with
        | 0 => exact hm00'
        | 1 => exact hm1
      · rw [if_neg hmd, Polynomial.coeff_zero]
    · intro hm
      exact absurd hm0 (by rw [MvPolynomial.notMem_support_iff] at hm ⊢; exact hm)
  rw [hzero, Polynomial.coeff_zero] at hkey
  exact hkey.symm


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_X_mul_pderiv (i : Fin 2) (g : PlanePoly) (m : Fin 2 →₀ ℕ) :
    coeff m (X i * pderiv i g) = (m i) • coeff m g := by
  classical
  have hexp : X i * pderiv i g
      = ∑ v ∈ g.support, (v i) • monomial v (coeff v g) := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [X_mul_pderiv_monomial]
  rw [hexp, coeff_sum]
  simp only [coeff_smul, coeff_monomial]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro v _ hvm
    rw [if_neg (fun h => hvm h), smul_zero]
  · intro hm
    rw [notMem_support_iff] at hm
    rw [if_pos rfl, hm, smul_zero]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_eq_zero_of_pderiv_eq_zero (g : PlanePoly) (D : ℕ) (hD : 1 ≤ D)
    (h0 : pderiv (1 : Fin 2) g = 0) :
    coeff (Finsupp.single (1 : Fin 2) D) g = 0 := by
  have hco := inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_X_mul_pderiv (1 : Fin 2) g (Finsupp.single (1 : Fin 2) D)
  rw [h0, mul_zero, coeff_zero] at hco
  rw [Finsupp.single_eq_same, nsmul_eq_mul] at hco
  have hDpos : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp hco.symm).resolve_left hDpos


theorem partialY_shearPoly_finite_bad (h : PlanePoly) (hpos : 1 ≤ h.totalDegree) :
    {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}.Finite := by
  have hh : h ≠ 0 := by
    intro h0
    rw [h0, totalDegree_zero] at hpos
    exact absurd hpos (by norm_num)
  have hPne : shearTopPoly h ≠ 0 := shearTopPoly_ne_zero h hh
  apply Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hPne)
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs ⊢
   
  rw [Polynomial.IsRoot.def, ← coeff_yD_shear_eq_eval]
  exact inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_eq_zero_of_pderiv_eq_zero (shearPoly s h) h.totalDegree hpos hs

end PachDeZeeuw.Algebraic

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
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ} {α : Type*}


theorem distanceOutNeighborsAtValue_card_le_three {p : Config n}
    (hp : Function.Injective p) (hgp : InGeneralPosition (Config.toFinset p))
    (i : Fin n) (r : ℝ) :
    (DistanceOutNeighborsAtValue p i r).card ≤ 3 := by
  classical
  let S : Finset Point := (Config.toFinset p).filter (fun x => dist x (p i) = r)
  have hcard_le : (DistanceOutNeighborsAtValue p i r).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn (fun j => p j) ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, DistanceOutNeighborsAtValue, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      obtain ⟨_hne, hdist⟩ := hj
      change p j ∈ (Config.toFinset p).filter (fun x => dist x (p i) = r)
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      · rw [dist_comm]
        exact hdist
    · intro _a _ha _b _hb hab
      exact hp hab
  exact hcard_le.trans (fixedDistance_card_le_three hgp (p i) r)


theorem distanceDegreeProfile_sum_eq_pred (p : Config n) (i : Fin n) :
    ∑ r ∈ OrderedDistanceValues p, (DistanceOutNeighborsAtValue p i r).card = n - 1 := by
  classical
  let s : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i
  let f : Fin n → ℝ := fun j ↦ dist (p i) (p j)
  have hmaps : ∀ j ∈ s, f j ∈ OrderedDistanceValues p := by
    intro j hj
    rw [OrderedDistanceValues, Finset.mem_image]
    refine ⟨(i, j), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      by simpa [s, Finset.mem_erase, ne_comm] using hj⟩
  have hfiber' :
      ∑ r ∈ OrderedDistanceValues p, (s.filter (fun j ↦ f j = r)).card = s.card := by
    exact (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hcard : s.card = n - 1 := by
    simp [s, Finset.card_univ, Fintype.card_fin]
  rw [← hcard, ← hfiber']
  apply Finset.sum_congr rfl
  intro r _hr
  have hfilter : s.filter (fun j ↦ f j = r) = DistanceOutNeighborsAtValue p i r := by
    ext j
    simp [s, f, DistanceOutNeighborsAtValue, ne_comm]
  rw [hfilter]

end Esgk

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial _root_.Polynomial


theorem isCoprime_fraction_map_of_primitive_irreducible_not_dvd
    (P Q : Polynomial XCoeff)
    (hPprim : P.IsPrimitive)
    (hPirr : Irreducible P)
    (hnot : ¬ P ∣ Q) :
    IsCoprime (P.map (algebraMap XCoeff XFrac))
      (Q.map (algebraMap XCoeff XFrac)) := by
  have hPmapIrr : Irreducible (P.map (algebraMap XCoeff XFrac)) :=
    hPprim.irreducible_iff_irreducible_map_fraction_map.mp hPirr
  rw [hPmapIrr.coprime_iff_not_dvd]
  intro hmap
  by_cases hQzero : Q = 0
  · exact hnot (hQzero ▸ dvd_zero P)
  have hcontent : Q.content ≠ 0 := by
    intro hzero
    exact hQzero (Polynomial.content_eq_zero_iff.mp hzero)
  have hcontentMapUnit :
      IsUnit (Polynomial.C (algebraMap XCoeff XFrac Q.content)) := by
    apply Polynomial.isUnit_C.mpr
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    apply hcontent
    exact IsFractionRing.injective XCoeff XFrac (by simpa using hzero)
  have hmapPrimPart :
      P.map (algebraMap XCoeff XFrac) ∣ Q.primPart.map (algebraMap XCoeff XFrac) := by
    apply (IsUnit.dvd_mul_left hcontentMapUnit).mp
    rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Q.eq_C_content_mul_primPart]
    exact hmap
  have hprimPart : P ∣ Q.primPart :=
    hPprim.dvd_of_fraction_map_dvd_fraction_map hmapPrimPart
  exact hnot (dvd_trans hprimPart Q.primPart_dvd)

end PachDeZeeuw.Algebraic

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


theorem headResultant_ne_zero_of_irreducible_not_dvd
    (p q : PlanePoly)
    (hpDegree : 0 < (headCurry p).natDegree)
    (hirr : Irreducible p)
    (hnot : ¬ p ∣ q) :
    headResultant p q ≠ 0 := by
  have hprimitive : (Curry0 p).IsPrimitive := by
    apply curry_isPrimitive_of_irreducible_positive_natDegree p hirr
    simpa only [Curry0, headCurry] using hpDegree
  have hcoprime :
      IsCoprime
        ((Curry0 p).map (algebraMap XCoeff XFrac))
        ((Curry0 q).map (algebraMap XCoeff XFrac)) := by
    exact isCoprime_fraction_map_of_primitive_irreducible_not_dvd
      (Curry0 p) (Curry0 q)
      hprimitive
      (by
        simpa [Curry0] using
          (hirr.map (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv))
      (by
        intro hdiv
        apply hnot
        have hdiv' := map_dvd (MvPolynomial.finSuccEquiv ℝ 1).symm hdiv
        simpa [Curry0] using hdiv')
  simpa [headResultant, headCurry, Curry0] using
    (resultant_ne_zero_of_fraction_coprime (Curry0 p) (Curry0 q) hcoprime)


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


attribute [simp] PlaneProjectiveModel.projectivePlaneAffineChart_projectivePolynomial


@[simp]
theorem totalDegree_realToComplexPlanePolynomial (G : PlanePoly) :
    (realToComplexPlanePolynomial G).totalDegree = G.totalDegree := by
  change (MvPolynomial.map Complex.ofRealHom G).totalDegree = G.totalDegree
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective G Complex.ofReal_injective]


attribute [simp]
  projectivePlaneAffineChart_complexPlaneHomogenization_totalDegree
  projectivePlaneAffineChart_planeHomogenization_totalDegree


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

namespace PachDeZeeuw.Algebraic

open MvPolynomial

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_C (s a : ℝ) :
    shearPoly s (C a) = C a := by
  simp [shearPoly]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_zero (s : ℝ) :
    shearPoly s 0 = 0 := by
  simp [shearPoly]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_add (s : ℝ) (p q : PlanePoly) :
    shearPoly s (p + q) = shearPoly s p + shearPoly s q := by
  simp [shearPoly]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_mul (s : ℝ) (p q : PlanePoly) :
    shearPoly s (p * q) = shearPoly s p * shearPoly s q := by
  simp [shearPoly]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_X_zero (s : ℝ) :
    shearPoly s (X (0 : Fin 2)) = X 0 + C s * X 1 := by
  simp [shearPoly, shearVars]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_X_one (s : ℝ) :
    shearPoly s (X (1 : Fin 2)) = X 1 := by
  simp [shearPoly, shearVars]








theorem eval_shearPoly_shearPoint_chart (s : ℝ) (h : PlanePoly) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval
        (fun i ↦ (chartEquiv.symm (shearPoint s (chartEquiv z))) i)
        (shearPoly s h) =
      MvPolynomial.eval (fun i ↦ z i) h := by
  rw [eval_eq_evalPlane_chart, Homeomorph.apply_symm_apply,
    evalPlane_shearPoly_shearPoint, ← eval_eq_evalPlane_chart]




 
theorem eval_rename_swap_swapPoint (h : PlanePoly) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i ↦ swapPoint z i)
        (MvPolynomial.rename (Equiv.swap 0 1) h) =
      MvPolynomial.eval (fun i ↦ z i) h := by
  rw [MvPolynomial.eval_rename]
  have hcoords :
      ((fun i ↦ swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i ↦ z i := by
    funext i
    fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
  rw [hcoords]




end PachDeZeeuw.Algebraic
end

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


theorem sepPoly_eval (p q : ℝ × ℝ) (s : ℝ) :
    (sepPoly p q).eval s = (p.1 - q.1) - s * (p.2 - q.2) := by
  simp only [sepPoly, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  ring


theorem sepPoly_ne_zero {p q : ℝ × ℝ} (hpq : p ≠ q) : sepPoly p q ≠ 0 := by
  intro hzero
  by_cases hy : p.2 = q.2
  ·  
    have hx : p.1 ≠ q.1 := by
      intro hx
      exact hpq (Prod.ext hx hy)
    have hcoeff : (sepPoly p q).coeff 0 = p.1 - q.1 := by
      simp only [sepPoly, hy, sub_self, map_zero, zero_mul, sub_zero]
      rw [Polynomial.coeff_C, if_pos rfl]
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    exact (sub_ne_zero.mpr hx) hcoeff.symm
  ·  
    have hcoeff : (sepPoly p q).coeff 1 = -(p.2 - q.2) := by
      rw [sepPoly, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by norm_num),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one, zero_sub]
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    have : p.2 - q.2 = 0 := by linarith [neg_eq_zero.mp hcoeff.symm]
    exact (sub_ne_zero.mpr hy) this


theorem exists_good_shear
    (Γ : Finset PlanePoly) (P : Finset (ℝ × ℝ)) (d : ℕ)
    (hirr : ∀ h ∈ Γ, Irreducible h)
    (hdeg : ∀ h ∈ Γ, h.totalDegree ≤ d)
    (hpos : ∀ h ∈ Γ, 1 ≤ h.totalDegree) :
    ∃ s : ℝ,
      (∀ h ∈ Γ, MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) ≠ 0) ∧
      (∀ h ∈ Γ, (shearPoly s h).totalDegree ≤ d) ∧
      (∀ h ∈ Γ, Irreducible (shearPoly s h)) ∧
      Set.InjOn (fun p => (shearPoint s p).1) ↑P := by
  classical
   
  set B₁ : Set ℝ := ⋃ h ∈ Γ, {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}
    with hB₁
  have hB₁_fin : B₁.Finite := by
    rw [hB₁]
    refine Set.Finite.biUnion (Finset.finite_toSet Γ) ?_
    intro h hh
    exact partialY_shearPoly_finite_bad h (hpos h hh)
   
  set B₂ : Set ℝ := ⋃ pq ∈ P.offDiag, {s : ℝ | (sepPoly pq.1 pq.2).IsRoot s} with hB₂
  have hB₂_fin : B₂.Finite := by
    rw [hB₂]
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro pq hpq
    have hne : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp (Finset.mem_coe.mp hpq)).2.2
    exact Polynomial.finite_setOfPred_isRoot (sepPoly_ne_zero hne)
   
  obtain ⟨s, hs⟩ := (hB₁_fin.union hB₂_fin).exists_notMem
  rw [Set.mem_union, not_or] at hs
  obtain ⟨hs₁, hs₂⟩ := hs
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  ·  
    intro h hh hpd
    apply hs₁
    rw [hB₁, Set.mem_iUnion₂]
    exact ⟨h, hh, hpd⟩
  ·  
    intro h hh
    exact (shearPoly_totalDegree_le s h).trans (hdeg h hh)
  ·  
    intro h hh
    exact (irreducible_shearPoly_iff s h).mpr (hirr h hh)
  ·  
    intro p hp q hq hpqeq
    by_contra hpq
     
    apply hs₂
    rw [hB₂, Set.mem_iUnion₂]
    refine ⟨(p, q), Finset.mem_offDiag.mpr ⟨Finset.mem_coe.mp hp, Finset.mem_coe.mp hq, hpq⟩, ?_⟩
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, sepPoly_eval]
     
    simp only [shearPoint_apply] at hpqeq
    linarith [hpqeq]

end PachDeZeeuw.Algebraic

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open scoped BigOperators

variable {n : ℕ}


theorem distanceDegreeProfile_add_missingDegree_eq_three_mul_numDistancesOrdered
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (i : Fin n) :
    (n - 1) + DistanceMissingDegree p i = 3 * NumDistancesOrdered p := by
  classical
  rw [← distanceDegreeProfile_sum_eq_pred p i]
  unfold DistanceMissingDegree NumDistancesOrdered
  rw [← Finset.sum_add_distrib]
  calc
    ∑ r ∈ OrderedDistanceValues p,
        ((DistanceOutNeighborsAtValue p i r).card + DistanceMissingMultiplicity p i r) =
        ∑ _r ∈ OrderedDistanceValues p, 3 := by
      apply Finset.sum_congr rfl
      intro r _hr
      have hcap := distanceOutNeighborsAtValue_card_le_three hp hgp i r
      unfold DistanceMissingMultiplicity
      omega
    _ = 3 * (OrderedDistanceValues p).card := by
      simp [Nat.mul_comm]


theorem distanceSquaredProfilePowerSum_add_squaredMissingPowerSum
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (i : Fin n) (j : ℕ) :
    DistanceSquaredProfilePowerSum p i j + DistanceSquaredMissingPowerSum p i j =
      3 * ∑ r ∈ OrderedDistanceValues p, (r ^ 2) ^ j := by
  classical
  unfold DistanceSquaredProfilePowerSum DistanceSquaredMissingPowerSum
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  have hcap := distanceOutNeighborsAtValue_card_le_three hp hgp i r
  rw [← add_mul]
  congr 1
  norm_cast
  unfold DistanceMissingMultiplicity
  omega

 
theorem distanceSquaredProfilePowerSum_eq_sum_dist_sq_pow
    (p : Config n) (i : Fin n) (j : ℕ) :
    DistanceSquaredProfilePowerSum p i j =
      ∑ q ∈ (Finset.univ : Finset (Fin n)).erase i, ((dist (p i) (p q)) ^ 2) ^ j := by
  classical
  let s : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i
  let f : Fin n → ℝ := fun q ↦ dist (p i) (p q)
  have hmaps : ∀ q ∈ s, f q ∈ OrderedDistanceValues p := by
    intro q hq
    rw [OrderedDistanceValues, Finset.mem_image]
    refine ⟨(i, q), ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      by simpa [s, Finset.mem_erase, ne_comm] using hq⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to'
    (s := s) (t := OrderedDistanceValues p) (g := f) hmaps (fun r : ℝ ↦ (r ^ 2) ^ j)
  have hfiber' :
      ∑ r ∈ OrderedDistanceValues p,
          ((s.filter (fun q ↦ f q = r)).card : ℝ) * (r ^ 2) ^ j =
        ∑ q ∈ s, ((f q) ^ 2) ^ j := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat] using hfiber
  rw [DistanceSquaredProfilePowerSum, ← hfiber']
  apply Finset.sum_congr rfl
  intro r _hr
  have hfilter : s.filter (fun q ↦ f q = r) = DistanceOutNeighborsAtValue p i r := by
    ext q
    simp [s, f, DistanceOutNeighborsAtValue, ne_comm]
  rw [hfilter]

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial _root_.Polynomial





theorem curry0_natDegree_pos_of_pderiv_zero_ne
    (p : PlanePoly) (hpartial : pderiv (0 : Fin 2) p ≠ 0) :
    0 < (Curry0 p).natDegree := by
  have hdegree_ne : MvPolynomial.degreeOf (0 : Fin 2) p ≠ 0 := by
    intro hzero
    apply hpartial
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars]
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
    exact not_not_intro hzero
  have hcurry_degree :
      (Curry0 p).natDegree = MvPolynomial.degreeOf (0 : Fin 2) p := by
    simpa [Curry0] using
      (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) (f := p))
  rw [hcurry_degree]
  exact Nat.pos_of_ne_zero hdegree_ne





end PachDeZeeuw.Algebraic
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open scoped BigOperators

variable {n : ℕ}


theorem distanceSquaredMissingMultiset_card (p : Config n) (i : Fin n) :
    (distanceSquaredMissingMultiset p i).card = DistanceMissingDegree p i := by
  classical
  simp [distanceSquaredMissingMultiset, DistanceMissingDegree, Multiset.card_bind]

 
theorem distanceSquaredMissingMultiset_sum_pow (p : Config n) (i : Fin n) (t : ℕ) :
    ((distanceSquaredMissingMultiset p i).map fun x ↦ x ^ t).sum =
      DistanceSquaredMissingPowerSum p i t := by
  classical
  simp [distanceSquaredMissingMultiset, DistanceSquaredMissingPowerSum, Multiset.map_bind,
    Multiset.map_replicate, Multiset.sum_bind, Multiset.sum_replicate]

 
theorem distanceSquaredMissingMultiset_esymm_eq_zero_of_lt
    (p : Config n) (i : Fin n) (m : ℕ) (h : DistanceMissingDegree p i < m) :
    (distanceSquaredMissingMultiset p i).esymm m = 0 := by
  rw [Multiset.esymm, Multiset.powersetCard_eq_empty m]
  · simp
  · rwa [distanceSquaredMissingMultiset_card]

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
open PachDeZeeuw.Algebraic


theorem sharp_finite_common_zero_count
    (p q : PlanePoly) (S : Finset (Fin 2 → ℝ))
    (hirr : Irreducible p)
    (hpos : 1 ≤ p.totalDegree)
    (hnot : ¬ p ∣ q)
    (hzero : ∀ z ∈ S, MvPolynomial.eval z p = 0 ∧ MvPolynomial.eval z q = 0) :
    S.card ≤ p.totalDegree * q.totalDegree := by
  let toPoint : (Fin 2 → ℝ) → PachDeZeeuw.Algebraic.Point2 := fun z ↦ WithLp.toLp 2 z
  let P : Finset (ℝ × ℝ) := S.image (fun z ↦ chartEquiv (toPoint z))
  have hfamilyIrreducible :
      ∀ h ∈ ({p} : Finset PlanePoly), Irreducible h := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact hirr
  have hfamilyDegree :
      ∀ h ∈ ({p} : Finset PlanePoly), h.totalDegree ≤ p.totalDegree := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact le_rfl
  have hfamilyPositive :
      ∀ h ∈ ({p} : Finset PlanePoly), 1 ≤ h.totalDegree := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact hpos
  obtain ⟨s, hpderiv, hdegree, hirrShear, hseparate⟩ :=
    exists_good_shear ({p} : Finset PlanePoly) P p.totalDegree
      hfamilyIrreducible hfamilyDegree hfamilyPositive
  have hpmem : p ∈ ({p} : Finset PlanePoly) := Finset.mem_singleton_self p
  have hpderiv : pderiv (1 : Fin 2) (shearPoly s p) ≠ 0 := hpderiv p hpmem
  have hdegree : (shearPoly s p).totalDegree ≤ p.totalDegree := hdegree p hpmem
  have hirrShear : Irreducible (shearPoly s p) := hirrShear p hpmem
  let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let p' : PlanePoly := MvPolynomial.rename swap (shearPoly s p)
  let q' : PlanePoly := MvPolynomial.rename swap (shearPoly s q)
  let phi : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun z ↦
    fun i ↦ swapPoint (chartEquiv.symm (shearPoint s (chartEquiv (toPoint z)))) i
  let T : Finset (Fin 2 → ℝ) := S.image phi
  have hphi : Set.InjOn phi (S : Set (Fin 2 → ℝ)) := by
    intro z hz w hw hzw
    have hswap :
        swapPoint (chartEquiv.symm (shearPoint s (chartEquiv (toPoint z)))) =
          swapPoint (chartEquiv.symm (shearPoint s (chartEquiv (toPoint w)))) := by
      ext i
      exact congrFun hzw i
    have hshear :
        chartEquiv.symm (shearPoint s (chartEquiv (toPoint z))) =
          chartEquiv.symm (shearPoint s (chartEquiv (toPoint w))) :=
      swapPoint_injective hswap
    have hfirst :
        (shearPoint s (chartEquiv (toPoint z))).1 =
          (shearPoint s (chartEquiv (toPoint w))).1 := by
      have hpair' := congrArg chartEquiv hshear
      exact congrArg Prod.fst hpair'
    have hzP : chartEquiv (toPoint z) ∈ P :=
      Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hwP : chartEquiv (toPoint w) ∈ P :=
      Finset.mem_image.mpr ⟨w, hw, rfl⟩
    have hpair : chartEquiv (toPoint z) = chartEquiv (toPoint w) :=
      hseparate hzP hwP hfirst
    have hpoint : toPoint z = toPoint w := chartEquiv.injective hpair
    funext i
    have hi := congrArg (fun x : PachDeZeeuw.Algebraic.Point2 ↦ x i) hpoint
    simpa [toPoint] using hi
  have hTcard : T.card = S.card := by
    exact Finset.card_image_iff.mpr hphi
  have hzero' :
      ∀ z ∈ T, MvPolynomial.eval z p' = 0 ∧ MvPolynomial.eval z q' = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hwp : MvPolynomial.eval w p = 0 := (hzero w hw).1
    have hwq : MvPolynomial.eval w q = 0 := (hzero w hw).2
    have hshearPoint := chartEquiv.symm (shearPoint s (chartEquiv (toPoint w)))
    constructor
    · rw [show p' = MvPolynomial.rename swap (shearPoly s p) by rfl]
      rw [eval_rename_swap_swapPoint]
      rw [eval_shearPoly_shearPoint_chart]
      simpa [toPoint] using hwp
    · rw [show q' = MvPolynomial.rename swap (shearPoly s q) by rfl]
      rw [eval_rename_swap_swapPoint]
      rw [eval_shearPoly_shearPoint_chart]
      simpa [toPoint] using hwq
  have hpartial' : pderiv (0 : Fin 2) p' ≠ 0 := by
    rw [show p' = MvPolynomial.rename swap (shearPoly s p) by rfl]
    have hrename :
        pderiv (0 : Fin 2) (MvPolynomial.rename swap (shearPoly s p)) =
          MvPolynomial.rename swap (pderiv (1 : Fin 2) (shearPoly s p)) := by
      simpa [swap] using
        (MvPolynomial.pderiv_rename swap.injective (x := (1 : Fin 2))
          (p := shearPoly s p))
    rw [hrename]
    exact (MvPolynomial.renameEquiv ℝ swap).injective.ne hpderiv
  have hpdegree' : 0 < (headCurry p').natDegree :=
    curry0_natDegree_pos_of_pderiv_zero_ne p' hpartial'
  have hirr' : Irreducible p' := by
    rw [show p' = MvPolynomial.rename swap (shearPoly s p) by rfl]
    exact hirrShear.map (MvPolynomial.renameEquiv ℝ swap).toRingEquiv
  have hnot' : ¬ p' ∣ q' := by
    intro hdiv
    change MvPolynomial.rename swap (shearPoly s p) ∣
      MvPolynomial.rename swap (shearPoly s q) at hdiv
    rw [← MvPolynomial.renameEquiv_apply, ← MvPolynomial.renameEquiv_apply] at hdiv
    have hdivShear : shearPoly s p ∣ shearPoly s q := by
      have hdiv' := map_dvd (MvPolynomial.renameEquiv ℝ swap).symm hdiv
      simpa only [AlgEquiv.symm_apply_apply] using hdiv'
    have hdivAlg : shearAlgEquiv s p ∣ shearAlgEquiv s q := by
      rw [shearAlgEquiv_apply, shearAlgEquiv_apply]
      exact hdivShear
    have hdivOrig := map_dvd (shearAlgEquiv s).symm hdivAlg
    exact hnot (by simpa only [AlgEquiv.symm_apply_apply] using hdivOrig)
  have hresultant : headResultant p' q' ≠ 0 :=
    headResultant_ne_zero_of_irreducible_not_dvd p' q' hpdegree' hirr' hnot'
  have hprojection : Set.InjOn (fun z : Fin 2 → ℝ ↦ z 1) (T : Set (Fin 2 → ℝ)) := by
    intro z hz w hw hzw
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hw
    have hi := hzw
    have hfirst :
        (shearPoint s (chartEquiv (toPoint z₀))).1 =
          (shearPoint s (chartEquiv (toPoint w₀))).1 := by
      simpa [phi, swapPoint, mkPoint2] using hi
    have hzP : chartEquiv (toPoint z₀) ∈ P :=
      Finset.mem_image.mpr ⟨z₀, hz₀, rfl⟩
    have hwP : chartEquiv (toPoint w₀) ∈ P :=
      Finset.mem_image.mpr ⟨w₀, hw₀, rfl⟩
    have hpair : chartEquiv (toPoint z₀) = chartEquiv (toPoint w₀) :=
      hseparate hzP hwP hfirst
    have hpoint : toPoint z₀ = toPoint w₀ := chartEquiv.injective hpair
    have hzw₀ : z₀ = w₀ := by
      funext i
      have hj := congrArg (fun x : PachDeZeeuw.Algebraic.Point2 ↦ x i) hpoint
      simpa [toPoint] using hj
    subst w₀
    rfl
  have hbound := common_zero_finset_card_le_totalDegree_mul
    p' q' T hpdegree' hresultant hprojection hzero'
  have hpdegreeBound : p'.totalDegree ≤ p.totalDegree := by
    dsimp [p']
    change ((MvPolynomial.renameEquiv ℝ swap) (shearPoly s p)).totalDegree ≤ p.totalDegree
    rw [MvPolynomial.totalDegree_renameEquiv]
    exact hdegree
  have hqdegreeBound : q'.totalDegree ≤ q.totalDegree := by
    dsimp [q']
    change ((MvPolynomial.renameEquiv ℝ swap) (shearPoly s q)).totalDegree ≤ q.totalDegree
    rw [MvPolynomial.totalDegree_renameEquiv]
    exact (shearPoly_totalDegree_le s q)
  calc
    S.card = T.card := hTcard.symm
    _ ≤ p'.totalDegree * q'.totalDegree := hbound
    _ ≤ p.totalDegree * q.totalDegree := Nat.mul_le_mul hpdegreeBound hqdegreeBound

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
open scoped BigOperators

variable {n : ℕ}


theorem eval_distanceNewtonPowerSumPolynomial
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (i : Fin n) (t : ℕ) (ht : 0 < t) :
    MvPolynomial.eval (fun k ↦ p i k) (distanceNewtonPowerSumPolynomial p t) =
      DistanceSquaredMissingPowerSum p i t := by
  classical
  have hsum :
      ∑ q : Fin n, (dist (p i) (p q) ^ 2) ^ t =
        DistanceSquaredProfilePowerSum p i t := by
    rw [distanceSquaredProfilePowerSum_eq_sum_dist_sq_pow]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp [ht.ne']
  have hledger :=
    distanceSquaredProfilePowerSum_add_squaredMissingPowerSum hp hgp i t
  calc
    MvPolynomial.eval (fun k ↦ p i k) (distanceNewtonPowerSumPolynomial p t) =
        3 * ∑ r ∈ OrderedDistanceValues p, (r ^ 2) ^ t -
          ∑ q : Fin n, (dist (p i) (p q) ^ 2) ^ t := by
      simp [distanceNewtonPowerSumPolynomial, eval_planeSquaredDistancePolynomial]
    _ = 3 * ∑ r ∈ OrderedDistanceValues p, (r ^ 2) ^ t -
        DistanceSquaredProfilePowerSum p i t := by rw [hsum]
    _ = DistanceSquaredMissingPowerSum p i t := by
      rw [sub_eq_iff_eq_add]
      simpa [add_comm] using hledger.symm

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

open EuclideanGeometry PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem eval_distanceNewtonElementaryPolynomial
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (i : Fin n) (m : ℕ) :
    MvPolynomial.eval (fun k ↦ p i k) (distanceNewtonElementaryPolynomial p m) =
      (distanceSquaredMissingMultiset p i).esymm m := by
  let ev : PlanePoly →ₐ[ℚ] ℝ :=
    (MvPolynomial.eval (fun k ↦ p i k)).toRatAlgHom
  calc
    MvPolynomial.eval (fun k ↦ p i k) (distanceNewtonElementaryPolynomial p m) =
        ev (distanceNewtonElementaryPolynomial p m) := by simp [ev]
    _ = newtonElementaryFromPowerSums
          (fun t ↦ ((distanceSquaredMissingMultiset p i).map fun x ↦ x ^ t).sum) m := by
      apply map_newtonElementaryFromPowerSums_of_succ ev
      intro t
      calc
        ev (distanceNewtonPowerSumPolynomial p (t + 1)) =
            MvPolynomial.eval (fun k ↦ p i k)
              (distanceNewtonPowerSumPolynomial p (t + 1)) := by
          simp [ev]
        _ = DistanceSquaredMissingPowerSum p i (t + 1) :=
          eval_distanceNewtonPowerSumPolynomial hp hgp i (t + 1) (Nat.succ_pos t)
        _ = ((distanceSquaredMissingMultiset p i).map fun x ↦ x ^ (t + 1)).sum :=
          (distanceSquaredMissingMultiset_sum_pow p i (t + 1)).symm
    _ = (distanceSquaredMissingMultiset p i).esymm m :=
      newtonElementaryFromPowerSums_eq_esymm _ _


theorem eval_distanceNewtonElementaryPolynomial_eq_zero_of_missingDegree_lt
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (i : Fin n) (m : ℕ)
    (hm : DistanceMissingDegree p i < m) :
    MvPolynomial.eval (fun k ↦ p i k) (distanceNewtonElementaryPolynomial p m) = 0 := by
  rw [eval_distanceNewtonElementaryPolynomial hp hgp i]
  exact distanceSquaredMissingMultiset_esymm_eq_zero_of_lt p i m hm


theorem eval_distanceNewtonElementaryPolynomial_succ_eq_zero
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) (σ : ℕ)
    (hσ : (n - 1) + σ = 3 * NumDistancesOrdered p) (i : Fin n) :
    MvPolynomial.eval (fun k ↦ p i k)
        (distanceNewtonElementaryPolynomial p (σ + 1)) = 0 := by
  apply eval_distanceNewtonElementaryPolynomial_eq_zero_of_missingDegree_lt hp hgp i
  have hmissing :=
    distanceDegreeProfile_add_missingDegree_eq_three_mul_numDistancesOrdered hp hgp i
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
open scoped BigOperators

variable {n : ℕ}


theorem distanceNewtonPowerSumPolynomial_totalDegree_le (p : Config n) (t : ℕ) :
    (distanceNewtonPowerSumPolynomial p t).totalDegree ≤ 2 * t := by
  classical
  rw [distanceNewtonPowerSumPolynomial]
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · simp only [MvPolynomial.totalDegree_C, zero_le]
  · refine MvPolynomial.totalDegree_finsetSum_le ?_
    intro q _
    calc
      ((planeSquaredDistancePolynomial (p q)) ^ t).totalDegree ≤
          t * (planeSquaredDistancePolynomial (p q)).totalDegree :=
        MvPolynomial.totalDegree_pow _ _
      _ ≤ t * 2 := Nat.mul_le_mul_left t (planeSquaredDistancePolynomial_totalDegree_le _)
      _ = 2 * t := Nat.mul_comm _ _


theorem homogeneousComponent_two_mul_distanceNewtonPowerSumPolynomial
    (p : Config n) (t : ℕ) (ht : 0 < t) :
    MvPolynomial.homogeneousComponent (2 * t) (distanceNewtonPowerSumPolynomial p t) =
      MvPolynomial.C (-(Fintype.card (Fin n) : ℝ)) * planeRadialQuadratic ^ t := by
  classical
  have hpositiveDegree : 0 < 2 * t := Nat.mul_pos (by omega) ht
  have hconstantDegree :
      (MvPolynomial.C
          (3 * ∑ r ∈ OrderedDistanceValues p, (r ^ 2) ^ t) : PlanePoly).totalDegree <
        2 * t := by
    simpa only [MvPolynomial.totalDegree_C] using hpositiveDegree
  rw [distanceNewtonPowerSumPolynomial, map_sub, map_sum]
  rw [MvPolynomial.homogeneousComponent_eq_zero (2 * t) _ hconstantDegree]
  simp_rw [MvPolynomial.homogeneousComponent_pow_of_totalDegree_le
    (planeSquaredDistancePolynomial_totalDegree_le _) t]
  simp_rw [homogeneousComponent_two_planeSquaredDistancePolynomial]
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [zero_sub, Finset.card_univ, ← neg_smul, MvPolynomial.smul_eq_C_mul]

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

 
theorem affineCircularChartI_planeRadialQuadratic :
    affineCircularChartI planeRadialQuadratic =
      circularChartU *
        (circularChartU + MvPolynomial.C (2 * Complex.I)) := by
  simp [affineCircularChartI, affineCircularChart, planeRadialQuadratic, circularChartU]
  have hI : (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 = -1 := by
    rw [← map_pow]
    simp [Complex.I_sq]
  have htwo : (MvPolynomial.C (2 : ℂ) : CircularChartPoly) = 2 := by
    simp only [map_ofNat]
  calc
    1 + (MvPolynomial.C Complex.I + MvPolynomial.X 0) ^ 2 =
        1 + (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 +
          2 * MvPolynomial.C Complex.I * MvPolynomial.X 0 +
          MvPolynomial.X 0 ^ 2 := by ring
    _ = MvPolynomial.X 0 *
        (MvPolynomial.X 0 + MvPolynomial.C 2 * MvPolynomial.C Complex.I) := by
      rw [hI, htwo]
      ring

 
theorem affineCircularChartJ_planeRadialQuadratic :
    affineCircularChartJ planeRadialQuadratic =
      circularChartU *
        (circularChartU - MvPolynomial.C (2 * Complex.I)) := by
  simp [affineCircularChartJ, affineCircularChart, planeRadialQuadratic, circularChartU]
  have hI : (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 = -1 := by
    rw [← map_pow]
    simp [Complex.I_sq]
  have htwo : (MvPolynomial.C (2 : ℂ) : CircularChartPoly) = 2 := by
    simp only [map_ofNat]
  calc
    1 + (-MvPolynomial.C Complex.I + MvPolynomial.X 0) ^ 2 =
        1 + (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 -
          2 * MvPolynomial.C Complex.I * MvPolynomial.X 0 +
          MvPolynomial.X 0 ^ 2 := by ring
    _ = MvPolynomial.X 0 *
        (MvPolynomial.X 0 - MvPolynomial.C 2 * MvPolynomial.C Complex.I) := by
      rw [hI, htwo]
      ring

 
theorem circularChartU_pow_dvd_affineCircularChartI_of_planeRadialQuadratic_pow_dvd
    {r : ℕ} {q : PlanePoly} (hq : planeRadialQuadratic ^ r ∣ q) :
    circularChartU ^ r ∣ affineCircularChartI q := by
  rcases hq with ⟨q, rfl⟩
  refine ⟨(circularChartU + MvPolynomial.C (2 * Complex.I)) ^ r *
      affineCircularChartI q, ?_⟩
  rw [map_mul, map_pow, affineCircularChartI_planeRadialQuadratic, mul_pow]
  ac_rfl

 
theorem circularChartU_pow_dvd_affineCircularChartJ_of_planeRadialQuadratic_pow_dvd
    {r : ℕ} {q : PlanePoly} (hq : planeRadialQuadratic ^ r ∣ q) :
    circularChartU ^ r ∣ affineCircularChartJ q := by
  rcases hq with ⟨q, rfl⟩
  refine ⟨(circularChartU - MvPolynomial.C (2 * Complex.I)) ^ r *
      affineCircularChartJ q, ?_⟩
  rw [map_mul, map_pow, affineCircularChartJ_planeRadialQuadratic, mul_pow]
  ac_rfl

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


namespace IsRadiallyFiltered

 
theorem zero (m : ℕ) : IsRadiallyFiltered m (0 : PlanePoly) := by
  intro d
  simp

 
theorem add {m : ℕ} {f g : PlanePoly}
    (hf : IsRadiallyFiltered m f) (hg : IsRadiallyFiltered m g) :
    IsRadiallyFiltered m (f + g) := by
  intro d
  rw [map_add]
  exact dvd_add (hf d) (hg d)


theorem sub {m : ℕ} {f g : PlanePoly}
    (hf : IsRadiallyFiltered m f) (hg : IsRadiallyFiltered m g) :
    IsRadiallyFiltered m (f - g) := by
  intro d
  rw [map_sub]
  exact dvd_sub (hf d) (hg d)

 
theorem constant (m : ℕ) (r : ℝ) :
    IsRadiallyFiltered m (MvPolynomial.C r : PlanePoly) := by
  intro d
  by_cases hd : d = 0
  · subst d
    simp
  · rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_C _ r),
      if_neg hd]
    exact dvd_zero _

 
theorem mul {a b : ℕ} {f g : PlanePoly}
    (hf : IsRadiallyFiltered a f) (hg : IsRadiallyFiltered b g) :
    IsRadiallyFiltered (a + b) (f * g) := by
  intro d
  rw [MvPolynomial.homogeneousComponent_mul_eq_sum_antidiagonal]
  apply Finset.dvd_sum
  rintro ⟨i, j⟩ hij
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  have hexponent : d - (a + b) ≤ (i - a) + (j - b) := by
    omega
  refine (pow_dvd_pow planeRadialQuadratic hexponent).trans ?_
  rw [pow_add]
  exact mul_dvd_mul (hf i) (hg j)

 
theorem pow {a : ℕ} {f : PlanePoly} (hf : IsRadiallyFiltered a f) (t : ℕ) :
    IsRadiallyFiltered (a * t) (f ^ t) := by
  induction t with
  | zero =>
      simpa using constant 0 (1 : ℝ)
  | succ t ih =>
      simpa [pow_succ, Nat.mul_succ] using ih.mul hf

end IsRadiallyFiltered

 
theorem planeSquaredDistancePolynomial_isRadiallyFiltered (a : PachDeZeeuw.Algebraic.Point2) :
    IsRadiallyFiltered 1 (planeSquaredDistancePolynomial a) := by
  intro d
  by_cases hd : d ≤ 1
  · simp [Nat.sub_eq_zero_of_le hd]
  by_cases hd2 : d = 2
  · subst d
    simp [homogeneousComponent_two_planeSquaredDistancePolynomial]
  · have htwo : 2 < d := by omega
    rw [MvPolynomial.homogeneousComponent_eq_zero d _
      (planeSquaredDistancePolynomial_totalDegree_le a |>.trans_lt htwo)]
    exact dvd_zero _

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
open scoped BigOperators

variable {n : ℕ}

private theorem inline_Esgk_DistanceNewtonElementaryTopRaw__distanceNewtonElementaryPolynomial_degree_top_aux
    (p : Config n) (m : ℕ) :
    (distanceNewtonElementaryPolynomial p m).totalDegree ≤ 2 * m ∧
      MvPolynomial.homogeneousComponent (2 * m)
          (distanceNewtonElementaryPolynomial p m) =
        MvPolynomial.C
            (newtonElementaryFromPowerSums
              (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ)) m) *
          planeRadialQuadratic ^ m := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
      cases m with
      | zero =>
          simp [distanceNewtonElementaryPolynomial, newtonElementaryFromPowerSums]
      | succ m =>
          have hsignDegree (k : ℕ) :
              ((-1 : PlanePoly) ^ k).totalDegree ≤ 0 := by
            calc
              ((-1 : PlanePoly) ^ k).totalDegree ≤
                  k * ((-1 : PlanePoly).totalDegree) :=
                MvPolynomial.totalDegree_pow _ _
              _ = 0 := by simp
          have hsign_eq_C (k : ℕ) :
              (-1 : PlanePoly) ^ k = MvPolynomial.C ((-1 : ℝ) ^ k) := by
            simp
          have hindex (a : ℕ × ℕ) (ha : a ∈ Finset.HasAntidiagonal.antidiagonal m) :
              m - a.2 = a.1 := by
            rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
            omega
          have hindex_lt (a : ℕ × ℕ) (ha : a ∈ Finset.HasAntidiagonal.antidiagonal m) :
              m - a.2 < m + 1 := by
            rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
            omega
          have htermDegree (a : ℕ × ℕ) (ha : a ∈ Finset.HasAntidiagonal.antidiagonal m) :
              (((-1 : PlanePoly) ^ (m - a.2) *
                    distanceNewtonElementaryPolynomial p (m - a.2)) *
                  distanceNewtonPowerSumPolynomial p (a.2 + 1)).totalDegree ≤
                2 * (m + 1) := by
            have hF := (ih (m - a.2) (hindex_lt a ha)).1
            have hQ := distanceNewtonPowerSumPolynomial_totalDegree_le p (a.2 + 1)
            calc
              (((-1 : PlanePoly) ^ (m - a.2) *
                    distanceNewtonElementaryPolynomial p (m - a.2)) *
                  distanceNewtonPowerSumPolynomial p (a.2 + 1)).totalDegree ≤
                  (((-1 : PlanePoly) ^ (m - a.2) *
                      distanceNewtonElementaryPolynomial p (m - a.2)).totalDegree +
                    (distanceNewtonPowerSumPolynomial p (a.2 + 1)).totalDegree) :=
                MvPolynomial.totalDegree_mul _ _
              _ ≤ (((( -1 : PlanePoly) ^ (m - a.2)).totalDegree +
                      (distanceNewtonElementaryPolynomial p (m - a.2)).totalDegree) +
                    (distanceNewtonPowerSumPolynomial p (a.2 + 1)).totalDegree) :=
                Nat.add_le_add_right
                  (MvPolynomial.totalDegree_mul _ _) _
              _ ≤ (0 + 2 * (m - a.2)) + 2 * (a.2 + 1) :=
                Nat.add_le_add (Nat.add_le_add (hsignDegree _) hF) hQ
              _ = 2 * (m + 1) := by
                rw [hindex a ha]
                rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
                omega
          have hsumDegree :
              (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                  (-1 : PlanePoly) ^ (m - a.2) *
                    distanceNewtonElementaryPolynomial p (m - a.2) *
                    distanceNewtonPowerSumPolynomial p (a.2 + 1)).totalDegree ≤
                2 * (m + 1) := by
            apply MvPolynomial.totalDegree_finsetSum_le
            intro a ha
            exact htermDegree a ha
          constructor
          · rw [distanceNewtonElementaryPolynomial, newtonElementaryFromPowerSums.eq_2]
            calc
              (((m + 1 : ℚ)⁻¹) •
                  ((-1 : PlanePoly) ^ (m + 2) *
                    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                      (-1 : PlanePoly) ^ (m - a.2) *
                        distanceNewtonElementaryPolynomial p (m - a.2) *
                        distanceNewtonPowerSumPolynomial p (a.2 + 1))).totalDegree ≤
                    (((-1 : PlanePoly) ^ (m + 2) *
                      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                        (-1 : PlanePoly) ^ (m - a.2) *
                          distanceNewtonElementaryPolynomial p (m - a.2) *
                          distanceNewtonPowerSumPolynomial p (a.2 + 1)).totalDegree) :=
                MvPolynomial.totalDegree_smul_le _ _
              _ ≤ (((-1 : PlanePoly) ^ (m + 2)).totalDegree +
                    (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                      (-1 : PlanePoly) ^ (m - a.2) *
                        distanceNewtonElementaryPolynomial p (m - a.2) *
                        distanceNewtonPowerSumPolynomial p (a.2 + 1)).totalDegree) :=
                MvPolynomial.totalDegree_mul _ _
              _ ≤ 0 + 2 * (m + 1) := Nat.add_le_add (hsignDegree _) hsumDegree
              _ = 2 * (m + 1) := by simp
          · have hsignedDegree (a : ℕ × ℕ) (ha : a ∈ Finset.HasAntidiagonal.antidiagonal m) :
                ((-1 : PlanePoly) ^ (m - a.2) *
                    distanceNewtonElementaryPolynomial p (m - a.2)).totalDegree ≤
                  2 * (m - a.2) := by
              calc
                ((-1 : PlanePoly) ^ (m - a.2) *
                    distanceNewtonElementaryPolynomial p (m - a.2)).totalDegree ≤
                    ((-1 : PlanePoly) ^ (m - a.2)).totalDegree +
                      (distanceNewtonElementaryPolynomial p (m - a.2)).totalDegree :=
                  MvPolynomial.totalDegree_mul _ _
                _ ≤ 0 + 2 * (m - a.2) :=
                  Nat.add_le_add (hsignDegree _) (ih (m - a.2) (hindex_lt a ha)).1
                _ = 2 * (m - a.2) := by simp
            have htermTop (a : ℕ × ℕ) (ha : a ∈ Finset.HasAntidiagonal.antidiagonal m) :
                MvPolynomial.homogeneousComponent (2 * (m + 1))
                    (((-1 : PlanePoly) ^ (m - a.2) *
                        distanceNewtonElementaryPolynomial p (m - a.2)) *
                      distanceNewtonPowerSumPolynomial p (a.2 + 1)) =
                  (-1 : PlanePoly) ^ (m - a.2) *
                      (MvPolynomial.C
                          (newtonElementaryFromPowerSums
                            (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ))
                            (m - a.2)) *
                        planeRadialQuadratic ^ (m - a.2)) *
                    (MvPolynomial.C (-(Fintype.card (Fin n) : ℝ)) *
                      planeRadialQuadratic ^ (a.2 + 1)) := by
              have hQ := distanceNewtonPowerSumPolynomial_totalDegree_le p (a.2 + 1)
              have hsignedTop :
                  MvPolynomial.homogeneousComponent (2 * (m - a.2))
                      ((-1 : PlanePoly) ^ (m - a.2) *
                        distanceNewtonElementaryPolynomial p (m - a.2)) =
                    (-1 : PlanePoly) ^ (m - a.2) *
                      MvPolynomial.homogeneousComponent (2 * (m - a.2))
                        (distanceNewtonElementaryPolynomial p (m - a.2)) := by
                calc
                  _ = MvPolynomial.homogeneousComponent (2 * (m - a.2))
                        (((-1 : ℝ) ^ (m - a.2)) •
                          distanceNewtonElementaryPolynomial p (m - a.2)) := by
                    rw [MvPolynomial.smul_eq_C_mul, ← hsign_eq_C]
                  _ = ((-1 : ℝ) ^ (m - a.2)) •
                        MvPolynomial.homogeneousComponent (2 * (m - a.2))
                          (distanceNewtonElementaryPolynomial p (m - a.2)) := by
                    rw [map_smul]
                  _ = _ := by
                    rw [MvPolynomial.smul_eq_C_mul, ← hsign_eq_C]
              rw [show 2 * (m + 1) =
                  2 * (m - a.2) + 2 * (a.2 + 1) by
                    rw [hindex a ha]
                    rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
                    omega]
              rw [MvPolynomial.homogeneousComponent_mul_of_totalDegree_le
                (hsignedDegree a ha) hQ]
              rw [hsignedTop, (ih (m - a.2) (hindex_lt a ha)).2]
              rw [homogeneousComponent_two_mul_distanceNewtonPowerSumPolynomial
                p (a.2 + 1) (by omega)]
            have htermFactor (a : ℕ × ℕ) (ha : a ∈ Finset.HasAntidiagonal.antidiagonal m) :
                (-1 : PlanePoly) ^ (m - a.2) *
                      (MvPolynomial.C
                          (newtonElementaryFromPowerSums
                            (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ))
                            (m - a.2)) *
                        planeRadialQuadratic ^ (m - a.2)) *
                    (MvPolynomial.C (-(Fintype.card (Fin n) : ℝ)) *
                      planeRadialQuadratic ^ (a.2 + 1)) =
                  ((-1 : PlanePoly) ^ (m - a.2) *
                      MvPolynomial.C
                        (newtonElementaryFromPowerSums
                          (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ))
                          (m - a.2)) *
                      MvPolynomial.C (-(Fintype.card (Fin n) : ℝ))) *
                    planeRadialQuadratic ^ (m + 1) := by
              have hexponent : (m - a.2) + (a.2 + 1) = m + 1 := by
                rw [hindex a ha]
                rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
                omega
              calc
                _ = ((-1 : PlanePoly) ^ (m - a.2) *
                        MvPolynomial.C
                          (newtonElementaryFromPowerSums
                            (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ))
                            (m - a.2)) *
                        MvPolynomial.C (-(Fintype.card (Fin n) : ℝ))) *
                      (planeRadialQuadratic ^ (m - a.2) *
                        planeRadialQuadratic ^ (a.2 + 1)) := by ring
                _ = _ := by rw [← pow_add, hexponent]
            have hsumTop :
                MvPolynomial.homogeneousComponent (2 * (m + 1))
                    (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                      (-1 : PlanePoly) ^ (m - a.2) *
                        distanceNewtonElementaryPolynomial p (m - a.2) *
                        distanceNewtonPowerSumPolynomial p (a.2 + 1)) =
                  (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                      (-1 : PlanePoly) ^ (m - a.2) *
                        MvPolynomial.C
                          (newtonElementaryFromPowerSums
                            (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ))
                            (m - a.2)) *
                        MvPolynomial.C (-(Fintype.card (Fin n) : ℝ))) *
                    planeRadialQuadratic ^ (m + 1) := by
              rw [map_sum, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro a ha
              rw [htermTop a ha, htermFactor a ha]
            have houterTop :
                MvPolynomial.homogeneousComponent (2 * (m + 1))
                    ((-1 : PlanePoly) ^ (m + 2) *
                      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                        (-1 : PlanePoly) ^ (m - a.2) *
                          distanceNewtonElementaryPolynomial p (m - a.2) *
                          distanceNewtonPowerSumPolynomial p (a.2 + 1)) =
                  (-1 : PlanePoly) ^ (m + 2) *
                    MvPolynomial.homogeneousComponent (2 * (m + 1))
                      (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                        (-1 : PlanePoly) ^ (m - a.2) *
                          distanceNewtonElementaryPolynomial p (m - a.2) *
                          distanceNewtonPowerSumPolynomial p (a.2 + 1)) := by
              calc
                _ = MvPolynomial.homogeneousComponent (2 * (m + 1))
                      (((-1 : ℝ) ^ (m + 2)) •
                        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                          (-1 : PlanePoly) ^ (m - a.2) *
                            distanceNewtonElementaryPolynomial p (m - a.2) *
                            distanceNewtonPowerSumPolynomial p (a.2 + 1)) := by
                  rw [MvPolynomial.smul_eq_C_mul, ← hsign_eq_C]
                _ = ((-1 : ℝ) ^ (m + 2)) •
                      MvPolynomial.homogeneousComponent (2 * (m + 1))
                        (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                          (-1 : PlanePoly) ^ (m - a.2) *
                            distanceNewtonElementaryPolynomial p (m - a.2) *
                            distanceNewtonPowerSumPolynomial p (a.2 + 1)) := by
                  rw [map_smul]
                _ = _ := by
                  rw [MvPolynomial.smul_eq_C_mul, ← hsign_eq_C]
            have hcoefficient :
                (((m + 1 : ℚ)⁻¹ : ℚ) : ℝ) •
                    ((-1 : PlanePoly) ^ (m + 2) *
                      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                        (-1 : PlanePoly) ^ (m - a.2) *
                          MvPolynomial.C
                            (newtonElementaryFromPowerSums
                              (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ))
                              (m - a.2)) *
                          MvPolynomial.C (-(Fintype.card (Fin n) : ℝ))) =
                  MvPolynomial.C
                    (newtonElementaryFromPowerSums
                      (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ)) (m + 1)) := by
              rw [newtonElementaryFromPowerSums.eq_2]
              change (((m + 1 : ℚ)⁻¹ : ℚ) : ℝ) •
                    ((-1 : PlanePoly) ^ (m + 2) *
                      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                        (-1 : PlanePoly) ^ (m - a.2) *
                          MvPolynomial.C
                            (newtonElementaryFromPowerSums
                              (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ))
                              (m - a.2)) *
                          MvPolynomial.C (-(Fintype.card (Fin n) : ℝ))) =
                  MvPolynomial.C
                    (((((m + 1 : ℚ)⁻¹ : ℚ) : ℝ)) *
                      ((-1 : ℝ) ^ (m + 2) *
                        ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                          (-1 : ℝ) ^ (m - a.2) *
                            newtonElementaryFromPowerSums
                              (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ))
                              (m - a.2) *
                            (-(Fintype.card (Fin n) : ℝ))))
              simp only [map_mul, map_pow, map_neg, map_one, map_sum,
                MvPolynomial.smul_eq_C_mul]
            rw [distanceNewtonElementaryPolynomial, newtonElementaryFromPowerSums.eq_2]
            change MvPolynomial.homogeneousComponent (2 * (m + 1))
                (((((m + 1 : ℚ)⁻¹ : ℚ) : ℝ)) •
                  ((-1 : PlanePoly) ^ (m + 2) *
                    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                      (-1 : PlanePoly) ^ (m - a.2) *
                        distanceNewtonElementaryPolynomial p (m - a.2) *
                        distanceNewtonPowerSumPolynomial p (a.2 + 1))) = _
            rw [map_smul, houterTop, hsumTop]
            calc
              _ = (((((m + 1 : ℚ)⁻¹ : ℚ) : ℝ)) •
                    ((-1 : PlanePoly) ^ (m + 2) *
                      ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                        (-1 : PlanePoly) ^ (m - a.2) *
                          MvPolynomial.C
                            (newtonElementaryFromPowerSums
                              (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ))
                              (m - a.2)) *
                          MvPolynomial.C (-(Fintype.card (Fin n) : ℝ)))) *
                    planeRadialQuadratic ^ (m + 1) := by
                simp only [MvPolynomial.smul_eq_C_mul]
                ring
              _ = _ := by rw [hcoefficient]

 
theorem distanceNewtonElementaryPolynomial_totalDegree_le (p : Config n) (m : ℕ) :
    (distanceNewtonElementaryPolynomial p m).totalDegree ≤ 2 * m :=
  (inline_Esgk_DistanceNewtonElementaryTopRaw__distanceNewtonElementaryPolynomial_degree_top_aux p m).1


theorem homogeneousComponent_two_mul_distanceNewtonElementaryPolynomial_raw
    (p : Config n) (m : ℕ) :
    MvPolynomial.homogeneousComponent (2 * m)
        (distanceNewtonElementaryPolynomial p m) =
      MvPolynomial.C
          (newtonElementaryFromPowerSums
            (fun _ : ℕ ↦ -(Fintype.card (Fin n) : ℝ)) m) *
        planeRadialQuadratic ^ m :=
  (inline_Esgk_DistanceNewtonElementaryTopRaw__distanceNewtonElementaryPolynomial_degree_top_aux p m).2

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
open scoped BigOperators

variable {n : ℕ}


theorem distanceNewtonPowerSumPolynomial_isRadiallyFiltered (p : Config n) (t : ℕ) :
    IsRadiallyFiltered t (distanceNewtonPowerSumPolynomial p t) := by
  classical
  have hconstant :
      IsRadiallyFiltered t
        (MvPolynomial.C (3 * ∑ r ∈ OrderedDistanceValues p, (r ^ 2) ^ t) : PlanePoly) :=
    IsRadiallyFiltered.constant t _
  have hterm (q : Fin n) :
      IsRadiallyFiltered t ((planeSquaredDistancePolynomial (p q)) ^ t) := by
    simpa using (planeSquaredDistancePolynomial_isRadiallyFiltered (p q)).pow t
  have hsum (s : Finset (Fin n)) :
      IsRadiallyFiltered t (∑ q ∈ s, (planeSquaredDistancePolynomial (p q)) ^ t) := by
    induction s using Finset.induction_on with
    | empty => simpa using IsRadiallyFiltered.zero t
    | @insert q s hq ih =>
        rw [Finset.sum_insert hq]
        exact (hterm q).add ih
  simpa [distanceNewtonPowerSumPolynomial] using hconstant.sub (hsum Finset.univ)

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
open scoped BigOperators

private theorem inline_Esgk_NewtonRadialFiltration__isRadiallyFiltered_rat_smul {m : ℕ} {f : PlanePoly} (q : ℚ)
    (hf : IsRadiallyFiltered m f) :
    IsRadiallyFiltered m (q • f) := by
  change IsRadiallyFiltered m ((q : ℝ) • f)
  rw [MvPolynomial.smul_eq_C_mul]
  simpa using (IsRadiallyFiltered.constant 0 (q : ℝ)).mul hf


theorem newtonElementaryFromPowerSums_isRadiallyFiltered (P : ℕ → PlanePoly)
    (hP : ∀ t, IsRadiallyFiltered (t + 1) (P (t + 1))) (m : ℕ) :
    IsRadiallyFiltered m (newtonElementaryFromPowerSums P m) := by
  classical
  induction m using Nat.strong_induction_on with
  | h m ih =>
      cases m with
      | zero =>
          rw [newtonElementaryFromPowerSums.eq_1]
          simpa using IsRadiallyFiltered.constant 0 (1 : ℝ)
      | succ m =>
          rw [newtonElementaryFromPowerSums.eq_2]
          have hsign (k : ℕ) : IsRadiallyFiltered 0 ((-1 : PlanePoly) ^ k) := by
            have hnegOne : IsRadiallyFiltered 0 (-1 : PlanePoly) := by
              simpa using IsRadiallyFiltered.constant 0 (-1 : ℝ)
            simpa using hnegOne.pow k
          have hterm (a : ℕ × ℕ) (ha : a ∈ Finset.HasAntidiagonal.antidiagonal m) :
              IsRadiallyFiltered (m + 1)
                ((-1 : PlanePoly) ^ (m - a.2) *
                  newtonElementaryFromPowerSums P (m - a.2) * P (a.2 + 1)) := by
            rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha
            have hrec :
                IsRadiallyFiltered (m - a.2)
                  (newtonElementaryFromPowerSums P (m - a.2)) :=
              ih (m - a.2) (by omega)
            have hraw := ((hsign (m - a.2)).mul hrec).mul (hP a.2)
            have hweight : (m - a.2) + (a.2 + 1) = m + 1 := by omega
            simpa only [zero_add, hweight] using hraw
          have hsum :
              IsRadiallyFiltered (m + 1)
                (∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                  (-1 : PlanePoly) ^ (m - a.2) *
                    newtonElementaryFromPowerSums P (m - a.2) * P (a.2 + 1)) := by
            intro d
            rw [map_sum]
            apply Finset.dvd_sum
            intro a ha
            exact hterm a ha d
          have houter :
              IsRadiallyFiltered (m + 1)
                ((-1 : PlanePoly) ^ (m + 2) *
                  ∑ a ∈ Finset.HasAntidiagonal.antidiagonal m,
                    (-1 : PlanePoly) ^ (m - a.2) *
                      newtonElementaryFromPowerSums P (m - a.2) * P (a.2 + 1)) := by
            simpa using (hsign (m + 2)).mul hsum
          exact inline_Esgk_NewtonRadialFiltration__isRadiallyFiltered_rat_smul ((m + 1 : ℚ)⁻¹) houter

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

 
private theorem inline_Esgk_PlaneCircularLocalOrderDegree__complex_I_ne_neg_I : Complex.I ≠ -Complex.I := by
  intro h
  have him : (1 : ℝ) = -1 := congrArg Complex.im h
  have hlt : (-1 : ℝ) < 1 := lt_trans neg_one_lt_zero zero_lt_one
  exact (ne_of_gt hlt) him


theorem planeCircularLocalOrderI_add_planeCircularLocalOrderJ_le_totalDegree
    {G : PlanePoly} (hG : G ≠ 0) :
    planeCircularLocalOrderI G + planeCircularLocalOrderJ G ≤ G.totalDegree := by
  calc
    planeCircularLocalOrderI G + planeCircularLocalOrderJ G ≤
        (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I +
          (complexPlaneInfinityRestriction G).rootMultiplicity (-Complex.I) :=
      Nat.add_le_add
        (planeCircularLocalOrder_le_rootMultiplicity Complex.I hG)
        (planeCircularLocalOrder_le_rootMultiplicity (-Complex.I) hG)
    _ ≤ (complexPlaneInfinityRestriction G).natDegree :=
      Polynomial.rootMultiplicity_add_rootMultiplicity_le_natDegree_of_ne
        (complexPlaneInfinityRestriction G) inline_Esgk_PlaneCircularLocalOrderDegree__complex_I_ne_neg_I
    _ ≤ G.totalDegree := complexPlaneInfinityRestriction_natDegree_le G

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

 
theorem homogeneousComponent_two_mul_distanceNewtonElementaryPolynomial
    (p : Config n) (m : ℕ) :
    MvPolynomial.homogeneousComponent (2 * m)
        (distanceNewtonElementaryPolynomial p m) =
      MvPolynomial.C (Ring.choose (-(Fintype.card (Fin n) : ℝ)) m) *
        planeRadialQuadratic ^ m := by
  rw [homogeneousComponent_two_mul_distanceNewtonElementaryPolynomial_raw,
    newtonElementaryFromPowerSums_const_eq_ringChoose]

 
theorem planeRadialQuadratic_ne_zero : planeRadialQuadratic ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 2 ↦ if i = 0 then (1 : ℝ) else 0)) hzero
  simp [planeRadialQuadratic] at heval


theorem distanceNewtonElementaryPolynomial_totalDegree_eq
    (p : Config n) (m : ℕ) (hn : 0 < n) :
    (distanceNewtonElementaryPolynomial p m).totalDegree = 2 * m := by
  cases m with
  | zero =>
      simpa using
        (Nat.le_zero.mp (distanceNewtonElementaryPolynomial_totalDegree_le p 0))
  | succ m =>
      apply le_antisymm (distanceNewtonElementaryPolynomial_totalDegree_le p (m + 1))
      have hcoefficient :
          Ring.choose (-(Fintype.card (Fin n) : ℝ)) (m + 1) ≠ 0 := by
        simpa using (ringChoose_neg_natCast_ne_zero (n := n) (m := m + 1) hn)
      have htop :
          MvPolynomial.homogeneousComponent (2 * (m + 1))
              (distanceNewtonElementaryPolynomial p (m + 1)) ≠ 0 := by
        rw [homogeneousComponent_two_mul_distanceNewtonElementaryPolynomial]
        exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hcoefficient)
          (pow_ne_zero _ planeRadialQuadratic_ne_zero)
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

 
theorem distanceNewtonElementaryPolynomial_isRadiallyFiltered (p : Config n) (m : ℕ) :
    IsRadiallyFiltered m (distanceNewtonElementaryPolynomial p m) := by
  unfold distanceNewtonElementaryPolynomial
  apply newtonElementaryFromPowerSums_isRadiallyFiltered
  intro t
  exact distanceNewtonPowerSumPolynomial_isRadiallyFiltered p (t + 1)


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


theorem projectiveCircularChart_planeHomogenization_totalDegree_ne_zero
    (c : ℂ) {G : PlanePoly} (hG : G ≠ 0) :
    projectiveCircularChart c (planeHomogenization G.totalDegree G) ≠ 0 := by
  have hshift :
      (complexPlaneInfinityRestriction G).comp (Polynomial.X + Polynomial.C c) ≠ 0 :=
    Polynomial.comp_X_add_C_ne_zero_iff.mpr (complexPlaneInfinityRestriction_ne_zero hG)
  rw [← chartInfinityRestriction_projectiveCircularChart_planeHomogenization] at hshift
  exact fun hzero ↦ hshift (by rw [hzero, map_zero])

private theorem inline_Esgk_PlaneCircularLocalOrderMul__circularChartLocalOrder_ne_top
    {F : CircularChartPoly} (hF : F ≠ 0) :
    MvPolynomial.localOrder F ≠ ⊤ := by
  simpa only [MvPolynomial.localOrder, MvPowerSeries.order_eq_top_iff,
    MvPolynomial.coe_eq_zero_iff, ne_eq] using hF

 
theorem planeCircularLocalOrder_mul
    (c : ℂ) {f g : PlanePoly} (hf : f ≠ 0) (hg : g ≠ 0) :
    planeCircularLocalOrder c (f * g) =
      planeCircularLocalOrder c f + planeCircularLocalOrder c g := by
  have hdegree : (f * g).totalDegree = f.totalDegree + g.totalDegree :=
    MvPolynomial.totalDegree_mul_of_isDomain hf hg
  have hfOrder :
      MvPolynomial.localOrder
          (projectiveCircularChart c (planeHomogenization f.totalDegree f)) ≠ ⊤ :=
    inline_Esgk_PlaneCircularLocalOrderMul__circularChartLocalOrder_ne_top
      (projectiveCircularChart_planeHomogenization_totalDegree_ne_zero c hf)
  have hgOrder :
      MvPolynomial.localOrder
          (projectiveCircularChart c (planeHomogenization g.totalDegree g)) ≠ ⊤ :=
    inline_Esgk_PlaneCircularLocalOrderMul__circularChartLocalOrder_ne_top
      (projectiveCircularChart_planeHomogenization_totalDegree_ne_zero c hg)
  simp only [planeCircularLocalOrder, hdegree,
    planeHomogenization_mul_of_totalDegree_le (f := f) (g := g) le_rfl le_rfl, map_mul,
    MvPolynomial.localOrder_mul, ENat.toNat_add hfOrder hgOrder]


@[simp]
theorem planeCircularLocalOrder_one (c : ℂ) :
    planeCircularLocalOrder c (1 : PlanePoly) = 0 := by
  have h := planeCircularLocalOrder_mul c
    (f := (1 : PlanePoly)) (g := (1 : PlanePoly)) one_ne_zero one_ne_zero
  simp only [one_mul] at h
  omega

 
theorem planeCircularLocalOrder_eq_zero_of_isUnit
    (c : ℂ) {u : PlanePoly} (hu : IsUnit u) :
    planeCircularLocalOrder c u = 0 := by
  rcases hu with ⟨u, rfl⟩
  have h := planeCircularLocalOrder_mul c
    (f := (u : PlanePoly)) (g := ((u⁻¹ : PlanePolyˣ) : PlanePoly))
    (Units.ne_zero u) (Units.ne_zero u⁻¹)
  have hprod : (u : PlanePoly) * ((u⁻¹ : PlanePolyˣ) : PlanePoly) = 1 := Units.mul_inv u
  rw [hprod, planeCircularLocalOrder_one] at h
  omega


theorem planeCircularLocalOrder_eq_of_associated
    (c : ℂ) {f g : PlanePoly} (hfg : Associated f g) (hf : f ≠ 0) :
    planeCircularLocalOrder c f = planeCircularLocalOrder c g := by
  rcases hfg with ⟨u, hu⟩
  have h := planeCircularLocalOrder_mul c hf (Units.ne_zero u)
  rw [hu, planeCircularLocalOrder_eq_zero_of_isUnit c u.isUnit, add_zero] at h
  exact h.symm

 
theorem planeCircularLocalOrderI_eq_of_associated
    {f g : PlanePoly} (hfg : Associated f g) (hf : f ≠ 0) :
    planeCircularLocalOrderI f = planeCircularLocalOrderI g := by
  simpa only [planeCircularLocalOrderI] using
    planeCircularLocalOrder_eq_of_associated Complex.I hfg hf

 
theorem planeCircularLocalOrderJ_eq_of_associated
    {f g : PlanePoly} (hfg : Associated f g) (hf : f ≠ 0) :
    planeCircularLocalOrderJ f = planeCircularLocalOrderJ g := by
  simpa only [planeCircularLocalOrderJ] using
    planeCircularLocalOrder_eq_of_associated (-Complex.I) hfg hf


theorem planeCircularLocalOrder_multiset_prod
    (c : ℂ) (s : Multiset PlanePoly) (hs : ∀ f ∈ s, f ≠ 0) :
    planeCircularLocalOrder c s.prod = (s.map (planeCircularLocalOrder c)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons f s ih =>
      have hf : f ≠ 0 := hs f (by simp)
      have hs' : ∀ g ∈ s, g ≠ 0 := fun g hg ↦ hs g (by simp [hg])
      have hprod : s.prod ≠ 0 :=
        Multiset.prod_ne_zero fun hzero ↦ hs' 0 hzero rfl
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
        planeCircularLocalOrder_mul c hf hprod, ih hs']


theorem planeCircularLocalOrderI_multiset_prod
    (s : Multiset PlanePoly) (hs : ∀ f ∈ s, f ≠ 0) :
    planeCircularLocalOrderI s.prod = (s.map planeCircularLocalOrderI).sum := by
  change planeCircularLocalOrder Complex.I s.prod =
    (s.map (planeCircularLocalOrder Complex.I)).sum
  exact planeCircularLocalOrder_multiset_prod Complex.I s hs


theorem planeCircularLocalOrderJ_multiset_prod
    (s : Multiset PlanePoly) (hs : ∀ f ∈ s, f ≠ 0) :
    planeCircularLocalOrderJ s.prod = (s.map planeCircularLocalOrderJ).sum := by
  change planeCircularLocalOrder (-Complex.I) s.prod =
    (s.map (planeCircularLocalOrder (-Complex.I))).sum
  exact planeCircularLocalOrder_multiset_prod (-Complex.I) s hs

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


private theorem inline_Esgk_RadialFiltrationCircularMultiplicity__projectiveCircularChart_planeHomogenization_mem_idealOfVars_pow
    (c : ℂ) {m : ℕ} {f : PlanePoly}
    (hf : ∀ d, circularChartU ^ (d - m) ∣
      affineCircularChart c (MvPolynomial.homogeneousComponent d f)) :
    projectiveCircularChart c (planeHomogenization (2 * m) f) ∈
      MvPolynomial.idealOfVars (Fin 2) ℂ ^ m := by
  rw [projectiveCircularChart_planeHomogenization]
  apply Ideal.sum_mem
  intro d hd
  have hd_le : d ≤ 2 * m := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hd
  have horder : m ≤ (d - m) + (2 * m - d) := by
    omega
  have hdvd : MvPolynomial.X (0 : Fin 2) ^ (d - m) ∣
      affineCircularChart c (MvPolynomial.homogeneousComponent d f) := by
    simpa only [circularChartU] using hf d
  simpa only [circularChartZ] using
    MvPolynomial.X_pow_mul_mem_pow_idealOfVars_of_X_pow_dvd
      (R := ℂ) (0 : Fin 2) (1 : Fin 2) (d - m) (2 * m - d) m
        (affineCircularChart c (MvPolynomial.homogeneousComponent d f)) horder hdvd


theorem hasCircularMultiplicityAtLeast_two_mul_of_isRadiallyFiltered
    {m : ℕ} {f : PlanePoly} (hf : IsRadiallyFiltered m f)
    (_hdegree : f.totalDegree ≤ 2 * m) :
    HasCircularMultiplicityAtLeast (2 * m) m f := by
  constructor
  · change projectiveCircularChart Complex.I (planeHomogenization (2 * m) f) ∈
      MvPolynomial.idealOfVars (Fin 2) ℂ ^ m
    apply inline_Esgk_RadialFiltrationCircularMultiplicity__projectiveCircularChart_planeHomogenization_mem_idealOfVars_pow Complex.I
    intro d
    exact circularChartU_pow_dvd_affineCircularChartI_of_planeRadialQuadratic_pow_dvd (hf d)
  · change projectiveCircularChart (-Complex.I) (planeHomogenization (2 * m) f) ∈
      MvPolynomial.idealOfVars (Fin 2) ℂ ^ m
    apply inline_Esgk_RadialFiltrationCircularMultiplicity__projectiveCircularChart_planeHomogenization_mem_idealOfVars_pow (-Complex.I)
    intro d
    exact circularChartU_pow_dvd_affineCircularChartJ_of_planeRadialQuadratic_pow_dvd (hf d)


theorem distanceNewtonElementaryPolynomial_hasCircularMultiplicityAtLeast
    {n : ℕ} (p : Config n) (m : ℕ) :
    HasCircularMultiplicityAtLeast (2 * m) m (distanceNewtonElementaryPolynomial p m) := by
  exact hasCircularMultiplicityAtLeast_two_mul_of_isRadiallyFiltered
    (distanceNewtonElementaryPolynomial_isRadiallyFiltered p m)
    (distanceNewtonElementaryPolynomial_totalDegree_le p m)

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

 
theorem distanceNewtonElementaryPolynomial_ne_zero
    (p : Config n) (m : ℕ) (hn : 0 < n) :
    distanceNewtonElementaryPolynomial p m ≠ 0 := by
  have hcoefficient :
      Ring.choose (-(Fintype.card (Fin n) : ℝ)) m ≠ 0 := by
    simpa using (ringChoose_neg_natCast_ne_zero (n := n) (m := m) hn)
  have htop :
      MvPolynomial.homogeneousComponent (2 * m)
          (distanceNewtonElementaryPolynomial p m) ≠ 0 := by
    rw [homogeneousComponent_two_mul_distanceNewtonElementaryPolynomial]
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hcoefficient)
      (pow_ne_zero _ planeRadialQuadratic_ne_zero)
  intro hzero
  apply htop
  rw [hzero]
  simp


theorem le_planeCircularLocalOrder_of_mem_pow
    (c : ℂ) {G : PlanePoly} (hG : G ≠ 0) {D m : ℕ}
    (hdegree : G.totalDegree = D)
    (hmem : projectiveCircularChart c (planeHomogenization D G) ∈
      MvPolynomial.idealOfVars (Fin 2) ℂ ^ m) :
    m ≤ planeCircularLocalOrder c G := by
  have hmem' :
      projectiveCircularChart c (planeHomogenization G.totalDegree G) ∈
        MvPolynomial.idealOfVars (Fin 2) ℂ ^ m := by
    simpa only [hdegree] using hmem
  have horder :
      (m : ℕ∞) ≤ MvPolynomial.localOrder
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) :=
    (MvPolynomial.mem_pow_idealOfVars_iff_le_localOrder m _).mp hmem'
  have hchart :
      projectiveCircularChart c (planeHomogenization G.totalDegree G) ≠ 0 :=
    projectiveCircularChart_planeHomogenization_totalDegree_ne_zero c hG
  have horder_ne_top :
      MvPolynomial.localOrder
          (projectiveCircularChart c (planeHomogenization G.totalDegree G)) ≠ ⊤ := by
    simpa only [MvPolynomial.localOrder, MvPowerSeries.order_eq_top_iff,
      MvPolynomial.coe_eq_zero_iff, ne_eq] using hchart
  rw [← ENat.coe_toNat horder_ne_top] at horder
  change m ≤
    (MvPolynomial.localOrder
      (projectiveCircularChart c (planeHomogenization G.totalDegree G))).toNat
  simpa only [ENat.coe_le_coe] using horder


theorem distanceNewtonElementaryPolynomial_planeCircularLocalOrderI_eq
    (p : Config n) (m : ℕ) (hn : 0 < n) :
    planeCircularLocalOrderI (distanceNewtonElementaryPolynomial p m) = m := by
  let F := distanceNewtonElementaryPolynomial p m
  have hF : F ≠ 0 := distanceNewtonElementaryPolynomial_ne_zero p m hn
  have hdegree : F.totalDegree = 2 * m :=
    distanceNewtonElementaryPolynomial_totalDegree_eq p m hn
  have hmult : HasCircularMultiplicityAtLeast (2 * m) m F :=
    distanceNewtonElementaryPolynomial_hasCircularMultiplicityAtLeast p m
  have hI : m ≤ planeCircularLocalOrderI F := by
    simpa only [planeCircularLocalOrderI] using
      le_planeCircularLocalOrder_of_mem_pow Complex.I hF hdegree
        (by simpa only [projectiveCircularChartI] using hmult.1)
  have hJ : m ≤ planeCircularLocalOrderJ F := by
    simpa only [planeCircularLocalOrderJ] using
      le_planeCircularLocalOrder_of_mem_pow (-Complex.I) hF hdegree
        (by simpa only [projectiveCircularChartJ] using hmult.2)
  have hsum : planeCircularLocalOrderI F + planeCircularLocalOrderJ F ≤ 2 * m := by
    simpa only [hdegree] using
      planeCircularLocalOrderI_add_planeCircularLocalOrderJ_le_totalDegree hF
  change planeCircularLocalOrderI F = m
  omega


theorem distanceNewtonElementaryPolynomial_planeCircularLocalOrderJ_eq
    (p : Config n) (m : ℕ) (hn : 0 < n) :
    planeCircularLocalOrderJ (distanceNewtonElementaryPolynomial p m) = m := by
  let F := distanceNewtonElementaryPolynomial p m
  have hF : F ≠ 0 := distanceNewtonElementaryPolynomial_ne_zero p m hn
  have hdegree : F.totalDegree = 2 * m :=
    distanceNewtonElementaryPolynomial_totalDegree_eq p m hn
  have hmult : HasCircularMultiplicityAtLeast (2 * m) m F :=
    distanceNewtonElementaryPolynomial_hasCircularMultiplicityAtLeast p m
  have hI : m ≤ planeCircularLocalOrderI F := by
    simpa only [planeCircularLocalOrderI] using
      le_planeCircularLocalOrder_of_mem_pow Complex.I hF hdegree
        (by simpa only [projectiveCircularChartI] using hmult.1)
  have hJ : m ≤ planeCircularLocalOrderJ F := by
    simpa only [planeCircularLocalOrderJ] using
      le_planeCircularLocalOrder_of_mem_pow (-Complex.I) hF hdegree
        (by simpa only [projectiveCircularChartJ] using hmult.2)
  have hsum : planeCircularLocalOrderI F + planeCircularLocalOrderJ F ≤ 2 * m := by
    simpa only [hdegree] using
      planeCircularLocalOrderI_add_planeCircularLocalOrderJ_le_totalDegree hF
  change planeCircularLocalOrderJ F = m
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





theorem isMaximallyCircular_of_order_sum_eq_totalDegree
    {G : PlanePoly}
    (hG : planeCircularLocalOrderI G + planeCircularLocalOrderJ G = G.totalDegree) :
    IsMaximallyCircular G := by
  have hconj := planeCircularLocalOrderI_eq_planeCircularLocalOrderJ G
  constructor <;> omega


theorem normalizedFactors_planeCircularLocalOrder_sum_eq_totalDegree
    {F : PlanePoly} (hF : F ≠ 0)
    (hFsum : planeCircularLocalOrderI F + planeCircularLocalOrderJ F = F.totalDegree) :
    ∀ G ∈ UniqueFactorizationMonoid.normalizedFactors F,
      planeCircularLocalOrderI G + planeCircularLocalOrderJ G = G.totalDegree := by
  let s : Multiset PlanePoly := UniqueFactorizationMonoid.normalizedFactors F
  have hsnonzero : ∀ G ∈ s, G ≠ 0 := by
    intro G hG
    exact (normalized_factor_irreducible (p := F) (h := G) (by simpa [s] using hG)).ne_zero
  have hsprod_ne : s.prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hzero
    exact hsnonzero 0 hzero rfl
  have hassoc : Associated s.prod F := by
    simpa [s] using UniqueFactorizationMonoid.prod_normalizedFactors hF
  have hIsum :
      (s.map planeCircularLocalOrderI).sum = planeCircularLocalOrderI F := by
    calc
      (s.map planeCircularLocalOrderI).sum = planeCircularLocalOrderI s.prod :=
        (planeCircularLocalOrderI_multiset_prod s hsnonzero).symm
      _ = planeCircularLocalOrderI F :=
        planeCircularLocalOrderI_eq_of_associated hassoc hsprod_ne
  have hJsum :
      (s.map planeCircularLocalOrderJ).sum = planeCircularLocalOrderJ F := by
    calc
      (s.map planeCircularLocalOrderJ).sum = planeCircularLocalOrderJ s.prod :=
        (planeCircularLocalOrderJ_multiset_prod s hsnonzero).symm
      _ = planeCircularLocalOrderJ F :=
        planeCircularLocalOrderJ_eq_of_associated hassoc hsprod_ne
  have horderSum :
      (s.map fun G ↦ planeCircularLocalOrderI G + planeCircularLocalOrderJ G).sum =
        planeCircularLocalOrderI F + planeCircularLocalOrderJ F := by
    rw [Multiset.sum_map_add, hIsum, hJsum]
  have hdegreeProd :
      s.prod.totalDegree = (s.map fun G : PlanePoly ↦ G.totalDegree).sum :=
    helper_multiset_prod_totalDegree_eq_sum s hsnonzero
  have hdegreeSum :
      (s.map fun G : PlanePoly ↦ G.totalDegree).sum = F.totalDegree := by
    calc
      (s.map fun G : PlanePoly ↦ G.totalDegree).sum = s.prod.totalDegree := hdegreeProd.symm
      _ = F.totalDegree := totalDegree_eq_of_associated hassoc
  have hfactorBound :
      ∀ G ∈ s,
        planeCircularLocalOrderI G + planeCircularLocalOrderJ G ≤ G.totalDegree := by
    intro G hG
    exact planeCircularLocalOrderI_add_planeCircularLocalOrderJ_le_totalDegree
      (hsnonzero G hG)
  have hdeficitSum :
      (s.map fun G ↦ G.totalDegree -
          (planeCircularLocalOrderI G + planeCircularLocalOrderJ G)).sum = 0 := by
    rw [Multiset.sum_map_tsub s hfactorBound, hdegreeSum, horderSum, hFsum,
      Nat.sub_self]
  intro G hG
  have hGs : G ∈ s := by simpa [s] using hG
  have hdeficitMem :
      G.totalDegree - (planeCircularLocalOrderI G + planeCircularLocalOrderJ G) ∈
        s.map fun H ↦ H.totalDegree -
          (planeCircularLocalOrderI H + planeCircularLocalOrderJ H) := by
    exact Multiset.mem_map.mpr ⟨G, hGs, rfl⟩
  have hdeficit :
      G.totalDegree - (planeCircularLocalOrderI G + planeCircularLocalOrderJ G) = 0 :=
    (Multiset.sum_eq_zero_iff.mp hdeficitSum) _ hdeficitMem
  exact le_antisymm (hfactorBound G hGs) (Nat.sub_eq_zero_iff_le.mp hdeficit)


variable {n : ℕ}


theorem distanceNewtonElementaryPolynomial_normalizedFactors_order_sum_eq_totalDegree
    (p : Config n) (m : ℕ) (hn : 0 < n) :
    ∀ G ∈ UniqueFactorizationMonoid.normalizedFactors
        (distanceNewtonElementaryPolynomial p m),
      planeCircularLocalOrderI G + planeCircularLocalOrderJ G = G.totalDegree := by
  have hcarrier : distanceNewtonElementaryPolynomial p m ≠ 0 :=
    distanceNewtonElementaryPolynomial_ne_zero p m hn
  have hcarrierSum :
      planeCircularLocalOrderI (distanceNewtonElementaryPolynomial p m) +
          planeCircularLocalOrderJ (distanceNewtonElementaryPolynomial p m) =
        (distanceNewtonElementaryPolynomial p m).totalDegree := by
    rw [distanceNewtonElementaryPolynomial_planeCircularLocalOrderI_eq p m hn,
      distanceNewtonElementaryPolynomial_planeCircularLocalOrderJ_eq p m hn,
      distanceNewtonElementaryPolynomial_totalDegree_eq p m hn]
    omega
  exact normalizedFactors_planeCircularLocalOrder_sum_eq_totalDegree hcarrier hcarrierSum


theorem distanceNewtonElementaryPolynomial_normalizedFactors_isMaximallyCircular
    (p : Config n) (m : ℕ) (hn : 0 < n) :
    ∀ G ∈ UniqueFactorizationMonoid.normalizedFactors
        (distanceNewtonElementaryPolynomial p m),
      IsMaximallyCircular G := by
  intro G hG
  apply isMaximallyCircular_of_order_sum_eq_totalDegree
  exact distanceNewtonElementaryPolynomial_normalizedFactors_order_sum_eq_totalDegree
    p m hn G hG

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


@[simp]
theorem mem_factorPointIndices {p : Fin n → PachDeZeeuw.Algebraic.Point2} {G : PlanePoly} {i : Fin n} :
    i ∈ factorPointIndices p G ↔ p i ∈ PlaneCurveZeroSet G := by
  simp [factorPointIndices]


theorem normalizedFactors_cover_factorPointIndices
    (p : Fin n → PachDeZeeuw.Algebraic.Point2) (F : PlanePoly) (hF : F ≠ 0)
    (hzero : ∀ i, p i ∈ PlaneCurveZeroSet F) :
    (Finset.univ : Finset (Fin n)) ⊆
      (UniqueFactorizationMonoid.normalizedFactors F).toFinset.biUnion
        (factorPointIndices p) := by
  classical
  intro i _hi
  have hi := zeroSet_subset_normalizedFactor_union (p := F) hF (hzero i)
  rcases Set.mem_iUnion.mp hi with ⟨G, hi⟩
  rcases Set.mem_iUnion.mp hi with ⟨hG, hpG⟩
  exact Finset.mem_biUnion.mpr ⟨G, by simpa using hG, by simpa using hpG⟩

 
theorem normalizedFactors_toFinset_totalDegree_sum_le (F : PlanePoly) (hF : F ≠ 0) :
    ∑ G ∈ (UniqueFactorizationMonoid.normalizedFactors F).toFinset, G.totalDegree ≤
      F.totalDegree := by
  classical
  let s : Multiset PlanePoly := UniqueFactorizationMonoid.normalizedFactors F
  have hsnonzero : ∀ G ∈ s, G ≠ 0 := by
    intro G hG
    exact (normalized_factor_irreducible (p := F) (h := G) (by simpa [s] using hG)).ne_zero
  have hdegreeProd :
      s.prod.totalDegree = (s.map fun G : PlanePoly ↦ G.totalDegree).sum :=
    helper_multiset_prod_totalDegree_eq_sum s hsnonzero
  have hassoc : Associated s.prod F := by
    simpa [s] using UniqueFactorizationMonoid.prod_normalizedFactors hF
  have hdegreeSum :
      (s.map fun G : PlanePoly ↦ G.totalDegree).sum = F.totalDegree := by
    calc
      (s.map fun G : PlanePoly ↦ G.totalDegree).sum = s.prod.totalDegree :=
        hdegreeProd.symm
      _ = F.totalDegree := totalDegree_eq_of_associated hassoc
  have hdedupDegree :
      (s.dedup.map fun G : PlanePoly ↦ G.totalDegree).sum ≤
        (s.map fun G : PlanePoly ↦ G.totalDegree).sum := by
    rcases Multiset.le_iff_exists_add.mp (Multiset.dedup_le s) with ⟨t, ht⟩
    calc
      (s.dedup.map fun G : PlanePoly ↦ G.totalDegree).sum ≤
          (s.dedup.map fun G : PlanePoly ↦ G.totalDegree).sum +
            (t.map fun G : PlanePoly ↦ G.totalDegree).sum := by omega
      _ = ((s.dedup + t).map fun G : PlanePoly ↦ G.totalDegree).sum := by simp
      _ = (s.map fun G : PlanePoly ↦ G.totalDegree).sum := by rw [← ht]
  calc
    ∑ G ∈ (UniqueFactorizationMonoid.normalizedFactors F).toFinset, G.totalDegree =
        (s.dedup.map fun G : PlanePoly ↦ G.totalDegree).sum := by
      change
        (((UniqueFactorizationMonoid.normalizedFactors F).toFinset).1.map
            fun G : PlanePoly ↦ G.totalDegree).sum = _
      rw [Multiset.toFinset_val]
    _ ≤ (s.map fun G : PlanePoly ↦ G.totalDegree).sum := hdedupDegree
    _ = F.totalDegree := hdegreeSum


theorem exists_normalizedFactor_point_degree_inequality
    (p : Fin n → PachDeZeeuw.Algebraic.Point2) (F : PlanePoly) (hn : 0 < n) (hF : F ≠ 0)
    (hzero : ∀ i, p i ∈ PlaneCurveZeroSet F) :
    ∃ G ∈ UniqueFactorizationMonoid.normalizedFactors F,
      n * G.totalDegree ≤ (factorPointIndices p G).card * F.totalDegree := by
  classical
  let factors : Finset PlanePoly :=
    (UniqueFactorizationMonoid.normalizedFactors F).toFinset
  have hcover :
      (Finset.univ : Finset (Fin n)) ⊆ factors.biUnion (factorPointIndices p) := by
    simpa [factors] using normalizedFactors_cover_factorPointIndices p F hF hzero
  have hfactors : factors.Nonempty := by
    let i : Fin n := ⟨0, hn⟩
    have hi : i ∈ factors.biUnion (factorPointIndices p) := hcover (by simp)
    rcases Finset.mem_biUnion.mp hi with ⟨G, hG, _hiG⟩
    exact ⟨G, hG⟩
  have hpointCard :
      n ≤ ∑ G ∈ factors, (factorPointIndices p G).card := by
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (factors.biUnion (factorPointIndices p)).card := Finset.card_le_card hcover
      _ ≤ ∑ G ∈ factors, (factorPointIndices p G).card := Finset.card_biUnion_le
  have hdistinctDegree : ∑ G ∈ factors, G.totalDegree ≤ F.totalDegree := by
    simpa [factors] using normalizedFactors_toFinset_totalDegree_sum_le F hF
  have hweightedSum :
      ∑ G ∈ factors, n * G.totalDegree ≤
        ∑ G ∈ factors, (factorPointIndices p G).card * F.totalDegree := by
    calc
      ∑ G ∈ factors, n * G.totalDegree =
          n * ∑ G ∈ factors, G.totalDegree := by rw [Finset.mul_sum]
      _ ≤ n * F.totalDegree := Nat.mul_le_mul_left n hdistinctDegree
      _ ≤ (∑ G ∈ factors, (factorPointIndices p G).card) * F.totalDegree :=
        Nat.mul_le_mul_right F.totalDegree hpointCard
      _ = ∑ G ∈ factors, (factorPointIndices p G).card * F.totalDegree := by
        rw [Finset.sum_mul]
  rcases Finset.exists_le_of_sum_le hfactors hweightedSum with ⟨G, hG, hineq⟩
  refine ⟨G, ?_, hineq⟩
  exact Multiset.mem_toFinset.mp (by simpa only [factors] using hG)


theorem exists_irreducible_normalizedFactor_point_degree_inequality
    (p : Fin n → PachDeZeeuw.Algebraic.Point2) (F : PlanePoly) (hn : 0 < n) (hF : F ≠ 0)
    (hzero : ∀ i, p i ∈ PlaneCurveZeroSet F) :
    ∃ G ∈ UniqueFactorizationMonoid.normalizedFactors F,
      Irreducible G ∧ 0 < G.totalDegree ∧
        n * G.totalDegree ≤ (factorPointIndices p G).card * F.totalDegree := by
  rcases exists_normalizedFactor_point_degree_inequality p F hn hF hzero with
    ⟨G, hG, hineq⟩
  exact ⟨G, hG, normalized_factor_irreducible hG,
    normalized_factor_totalDegree_pos hG, hineq⟩

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


theorem coprime_finite_common_zero_count
    (p q : PlanePoly) (S : Finset (Fin 2 → ℝ))
    (hp0 : p ≠ 0)
    (hNoCommon : ∀ r, Irreducible r → r ∣ p → ¬ r ∣ q)
    (hzero : ∀ z ∈ S, MvPolynomial.eval z p = 0 ∧ MvPolynomial.eval z q = 0) :
    S.card ≤ p.totalDegree * q.totalDegree := by
  classical
  let toPoint : (Fin 2 → ℝ) → PachDeZeeuw.Algebraic.Point2 := fun z ↦ WithLp.toLp 2 z
  let factors : Finset PlanePoly :=
    (UniqueFactorizationMonoid.normalizedFactors p).toFinset
  let fiber : PlanePoly → Finset (Fin 2 → ℝ) :=
    fun G ↦ S.filter (fun z ↦ toPoint z ∈ PlaneCurveZeroSet G)
  have hzeroSet : ∀ z ∈ S, toPoint z ∈ PlaneCurveZeroSet p := by
    intro z hz
    rw [mem_PlaneCurveZeroSet]
    simpa [toPoint] using (hzero z hz).1
  have hcover : S ⊆ factors.biUnion fiber := by
    intro z hz
    have hzcover := zeroSet_subset_normalizedFactor_union (p := p) hp0 (hzeroSet z hz)
    rcases Set.mem_iUnion.mp hzcover with ⟨G, hzcover⟩
    rcases Set.mem_iUnion.mp hzcover with ⟨hG, hzG⟩
    have hGmem : G ∈ factors := by simpa [factors] using hG
    exact Finset.mem_biUnion.mpr ⟨G, hGmem,
      Finset.mem_filter.mpr ⟨hz, hzG⟩⟩
  have hfiber : ∀ G ∈ factors, (fiber G).card ≤ G.totalDegree * q.totalDegree := by
    intro G hG
    have hGmem : G ∈ UniqueFactorizationMonoid.normalizedFactors p := by
      exact UniqueFactorizationMonoid.mem_primeFactors.mp (by simpa [factors] using hG)
    have hGirr : Irreducible G := normalized_factor_irreducible hGmem
    have hGdvd : G ∣ p := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hGmem
    have hGnot : ¬ G ∣ q := hNoCommon G hGirr hGdvd
    apply sharp_finite_common_zero_count G q (fiber G) hGirr
      (normalized_factor_totalDegree_pos hGmem) hGnot
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    rw [mem_PlaneCurveZeroSet] at hz'
    exact ⟨by simpa [toPoint] using hz'.2, (hzero z hz'.1).2⟩
  calc
    S.card ≤ (factors.biUnion fiber).card := Finset.card_le_card hcover
    _ ≤ ∑ G ∈ factors, (fiber G).card := Finset.card_biUnion_le
    _ ≤ ∑ G ∈ factors, G.totalDegree * q.totalDegree := by
      exact Finset.sum_le_sum fun G hG ↦ hfiber G hG
    _ = (∑ G ∈ factors, G.totalDegree) * q.totalDegree := by
      rw [Finset.sum_mul]
    _ ≤ p.totalDegree * q.totalDegree := by
      exact Nat.mul_le_mul_right _ (normalizedFactors_toFinset_totalDegree_sum_le p hp0)

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


theorem exists_distanceNewtonElementaryPolynomial_normalizedFactor_point_degree_inequality
    (p : Config n) (σ : ℕ) (hn : 0 < n) (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p))
    (hσ : (n - 1) + σ = 3 * NumDistancesOrdered p) :
    ∃ G ∈ UniqueFactorizationMonoid.normalizedFactors
        (distanceNewtonElementaryPolynomial p (σ + 1)),
      Irreducible G ∧ 0 < G.totalDegree ∧ IsMaximallyCircular G ∧
        n * G.totalDegree ≤ (factorPointIndices p G).card * (2 * (σ + 1)) ∧
        G.totalDegree ≤ 2 * (σ + 1) := by
  have hcarrier : distanceNewtonElementaryPolynomial p (σ + 1) ≠ 0 :=
    distanceNewtonElementaryPolynomial_ne_zero p (σ + 1) hn
  have hzero :
      ∀ i, p i ∈ PlaneCurveZeroSet (distanceNewtonElementaryPolynomial p (σ + 1)) := by
    intro i
    rw [mem_PlaneCurveZeroSet]
    exact eval_distanceNewtonElementaryPolynomial_succ_eq_zero hp hgp σ hσ i
  rcases exists_irreducible_normalizedFactor_point_degree_inequality
      p (distanceNewtonElementaryPolynomial p (σ + 1)) hn hcarrier hzero with
    ⟨G, hG, hGirreducible, hGdegree_pos, hpointDegree⟩
  have hmaximallyCircular : IsMaximallyCircular G :=
    distanceNewtonElementaryPolynomial_normalizedFactors_isMaximallyCircular
      p (σ + 1) hn G hG
  have hcarrierDegree :
      (distanceNewtonElementaryPolynomial p (σ + 1)).totalDegree = 2 * (σ + 1) :=
    distanceNewtonElementaryPolynomial_totalDegree_eq p (σ + 1) hn
  have hGdegree : G.totalDegree ≤ 2 * (σ + 1) := by
    rw [← hcarrierDegree]
    exact normalized_factor_degree_le hcarrier hG
  rw [hcarrierDegree] at hpointDegree
  exact ⟨G, hG, hGirreducible, hGdegree_pos, hmaximallyCircular, hpointDegree, hGdegree⟩

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

 
theorem IsCircleFactor.totalDegree_eq {G : PlanePoly} (hG : IsCircleFactor G) :
    G.totalDegree = 2 := by
  rcases hG with ⟨c, r, _hr, hassoc⟩
  calc
    G.totalDegree = (circleEquationPolynomial c r).totalDegree :=
      totalDegree_eq_of_associated hassoc
    _ = 2 := circleEquationPolynomial_totalDegree_eq c r


theorem factorPointIndices_card_le_three_of_isCircleFactor
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) {G : PlanePoly}
    (hG : IsCircleFactor G) :
    (factorPointIndices p G).card ≤ 3 := by
  classical
  rcases hG with ⟨c, r, hr, hassoc⟩
  apply le_trans (Finset.card_le_card_of_injOn p ?_ ?_)
    (fixedDistance_card_le_three hgp c r)
  · intro i hi
    change p i ∈ (Config.toFinset p).filter (fun x ↦ dist x c = r)
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · have hzero : p i ∈ PlaneCurveZeroSet G := mem_factorPointIndices.mp hi
      rw [zeroSet_eq_of_associated hassoc,
        circleEquationPolynomial_zeroSet c hr] at hzero
      simpa [Metric.mem_sphere, dist_eq_norm] using hzero
  · intro i _hi j _hj hij
    exact hp hij


theorem numPoints_le_three_mul_of_circleFactor_point_degree_inequality
    {p : Config n} (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p)) {F G : PlanePoly} {s : ℕ}
    (hG : IsCircleFactor G) (hFdegree : F.totalDegree = 2 * s)
    (hselect : n * G.totalDegree ≤ (factorPointIndices p G).card * F.totalDegree) :
    n ≤ 3 * s := by
  have hGdegree : G.totalDegree = 2 := hG.totalDegree_eq
  have hcard : (factorPointIndices p G).card ≤ 3 :=
    factorPointIndices_card_le_three_of_isCircleFactor hp hgp hG
  rw [hGdegree, hFdegree] at hselect
  have hselect' : n * 2 ≤ 3 * (2 * s) :=
    hselect.trans (Nat.mul_le_mul_right (2 * s) hcard)
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

open EuclideanGeometry PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem distanceNewtonElementaryPolynomial_normalizedFactor_trichotomy
    (hNonabsoluteBound : RealIrreducibleNotAbsolutelyIrreduciblePointBoundStatement)
    (p : Config n) (σ : ℕ) (hn : 0 < n) (hp : Function.Injective p)
    (hgp : InGeneralPosition (Config.toFinset p))
    (hσ : (n - 1) + σ = 3 * NumDistancesOrdered p) :
    let s := σ + 1
    n ≤ 3 * s ∨ n ≤ s ^ 2 ∨
      ∃ G N,
        G ∈ UniqueFactorizationMonoid.normalizedFactors
            (distanceNewtonElementaryPolynomial p s) ∧
          Irreducible G ∧
          IsAbsolutelyIrreducible G ∧
          ¬ IsCircleFactor G ∧
          IsMaximallyCircular G ∧
          0 < G.totalDegree ∧
          n * G.totalDegree ≤ N * (2 * s) ∧
          G.totalDegree ≤ 2 * s ∧
          N = (factorPointIndices p G).card := by
  classical
  dsimp only
  rcases exists_distanceNewtonElementaryPolynomial_normalizedFactor_point_degree_inequality
      p σ hn hp hgp hσ with
    ⟨G, hGfactor, hGirreducible, hGdegreePos, hGmaximallyCircular, hSelection,
      hGdegreeBound⟩
  by_cases hGcircle : IsCircleFactor G
  · left
    have hCarrierDegree :
        (distanceNewtonElementaryPolynomial p (σ + 1)).totalDegree = 2 * (σ + 1) :=
      distanceNewtonElementaryPolynomial_totalDegree_eq p (σ + 1) hn
    exact numPoints_le_three_mul_of_circleFactor_point_degree_inequality hp hgp hGcircle
      hCarrierDegree (by simpa [hCarrierDegree] using hSelection)
  · by_cases hGabsolute : IsAbsolutelyIrreducible G
    · right
      right
      exact ⟨G, (factorPointIndices p G).card, hGfactor, hGirreducible, hGabsolute,
        hGcircle, hGmaximallyCircular, hGdegreePos, hSelection, hGdegreeBound, rfl⟩
    · right
      left
      apply n_le_sq_of_nonabsolute_normalizedFactor_point_bound hNonabsoluteBound
        (factorPointIndices p G) p hGfactor hGabsolute
      · exact hp.injOn
      · intro i hi
        exact mem_factorPointIndices.mp hi
      · calc
          n * G.totalDegree ≤ (factorPointIndices p G).card * (2 * (σ + 1)) := hSelection
          _ = 2 * (σ + 1) * (factorPointIndices p G).card := Nat.mul_comm _ _
      · exact hGdegreeBound

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
open scoped ComplexConjugate


lemma complexRealPartPoly_add (H K : ComplexPlanePoly) :
    complexRealPartPoly (H + K) = complexRealPartPoly H + complexRealPartPoly K := by
  simp [complexRealPartPoly, Finsupp.mapRange_add, Complex.add_re]

lemma complexImagPartPoly_add (H K : ComplexPlanePoly) :
    complexImagPartPoly (H + K) = complexImagPartPoly H + complexImagPartPoly K := by
  simp [complexImagPartPoly, Finsupp.mapRange_add, Complex.add_im]

lemma complexRealPartPoly_monomial (e : Fin 2 →₀ ℕ) (c : ℂ) :
    complexRealPartPoly (MvPolynomial.monomial e c) = MvPolynomial.monomial e c.re := by
  ext m
  change (Finsupp.mapRange Complex.re (by simp)
    (AddMonoidAlgebra.coeff (MvPolynomial.monomial e c))) m = _
  rw [Finsupp.mapRange_apply]
  by_cases hm : e = m
  · subst e
    conv_lhs =>
      change Complex.re (MvPolynomial.coeff m (MvPolynomial.monomial m c))
    rw [MvPolynomial.coeff_monomial]
    rw [MvPolynomial.coeff_monomial]
    simp
  · conv_lhs =>
      change Complex.re (MvPolynomial.coeff m (MvPolynomial.monomial e c))
    rw [MvPolynomial.coeff_monomial]
    rw [MvPolynomial.coeff_monomial]
    simp [hm]

lemma complexImagPartPoly_monomial (e : Fin 2 →₀ ℕ) (c : ℂ) :
    complexImagPartPoly (MvPolynomial.monomial e c) = MvPolynomial.monomial e c.im := by
  ext m
  change (Finsupp.mapRange Complex.im (by simp)
    (AddMonoidAlgebra.coeff (MvPolynomial.monomial e c))) m = _
  rw [Finsupp.mapRange_apply]
  by_cases hm : e = m
  · subst e
    conv_lhs =>
      change Complex.im (MvPolynomial.coeff m (MvPolynomial.monomial m c))
    rw [MvPolynomial.coeff_monomial]
    rw [MvPolynomial.coeff_monomial]
    simp
  · conv_lhs =>
      change Complex.im (MvPolynomial.coeff m (MvPolynomial.monomial e c))
    rw [MvPolynomial.coeff_monomial]
    rw [MvPolynomial.coeff_monomial]
    simp [hm]

lemma complexRealPartPoly_support_subset (H : ComplexPlanePoly) :
    (complexRealPartPoly H).support ⊆ H.support := by
  intro m hm
  have hm' := MvPolynomial.mem_support_iff.mp hm
  change Complex.re (H.coeff m) ≠ 0 at hm'
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  exact hm' (by rw [hz]; simp)

lemma complexImagPartPoly_support_subset (H : ComplexPlanePoly) :
    (complexImagPartPoly H).support ⊆ H.support := by
  intro m hm
  have hm' := MvPolynomial.mem_support_iff.mp hm
  change Complex.im (H.coeff m) ≠ 0 at hm'
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  exact hm' (by rw [hz]; simp)

lemma complexRealPartPoly_totalDegree_le (H : ComplexPlanePoly) :
    (complexRealPartPoly H).totalDegree ≤ H.totalDegree := by
  rw [MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  apply Finset.sup_le
  intro m hm
  rw [Finsupp.card_toMultiset]
  calc
    m.sum (fun _ e ↦ e) ≤ H.totalDegree := by
      simpa [Finsupp.degree_eq_sum] using
        MvPolynomial.le_totalDegree (complexRealPartPoly_support_subset H hm)
    _ = H.support.sup (fun m ↦ (Finsupp.toMultiset m).card) :=
      MvPolynomial.totalDegree_eq H

lemma complexImagPartPoly_totalDegree_le (H : ComplexPlanePoly) :
    (complexImagPartPoly H).totalDegree ≤ H.totalDegree := by
  rw [MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  apply Finset.sup_le
  intro m hm
  rw [Finsupp.card_toMultiset]
  calc
    m.sum (fun _ e ↦ e) ≤ H.totalDegree := by
      simpa [Finsupp.degree_eq_sum] using
        MvPolynomial.le_totalDegree (complexImagPartPoly_support_subset H hm)
    _ = H.support.sup (fun m ↦ (Finsupp.toMultiset m).card) :=
      MvPolynomial.totalDegree_eq H

lemma complexRealPartPoly_eval (H : ComplexPlanePoly) (z : Fin 2 → ℝ) :
    MvPolynomial.eval z (complexRealPartPoly H) =
      (MvPolynomial.eval (fun i ↦ Complex.ofReal (z i)) H).re := by
  induction H using MvPolynomial.induction_on' with
  | add H K hH hK =>
      rw [complexRealPartPoly_add, MvPolynomial.eval_add, hH, hK,
        MvPolynomial.eval_add, Complex.add_re]
  | monomial e c =>
      rw [complexRealPartPoly_monomial]
      simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Complex.mul_re,
        ← Complex.ofReal_pow]

lemma complexImagPartPoly_eval (H : ComplexPlanePoly) (z : Fin 2 → ℝ) :
    MvPolynomial.eval z (complexImagPartPoly H) =
      (MvPolynomial.eval (fun i ↦ Complex.ofReal (z i)) H).im := by
  induction H using MvPolynomial.induction_on' with
  | add H K hH hK =>
      rw [complexImagPartPoly_add, MvPolynomial.eval_add, hH, hK,
        MvPolynomial.eval_add, Complex.add_im]
  | monomial e c =>
      rw [complexImagPartPoly_monomial]
      simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Complex.mul_im,
        ← Complex.ofReal_pow]

lemma complexification_real_im (H : ComplexPlanePoly) :
    realToComplexPlanePolynomial (complexRealPartPoly H) +
        MvPolynomial.C Complex.I * realToComplexPlanePolynomial (complexImagPartPoly H) = H := by
  induction H using MvPolynomial.induction_on' with
  | add H K hH hK =>
      rw [complexRealPartPoly_add, complexImagPartPoly_add, map_add, map_add]
      calc
        realToComplexPlanePolynomial (complexRealPartPoly H) +
              realToComplexPlanePolynomial (complexRealPartPoly K) +
              MvPolynomial.C Complex.I *
                (realToComplexPlanePolynomial (complexImagPartPoly H) +
                  realToComplexPlanePolynomial (complexImagPartPoly K)) =
            (realToComplexPlanePolynomial (complexRealPartPoly H) +
              MvPolynomial.C Complex.I * realToComplexPlanePolynomial (complexImagPartPoly H)) +
              (realToComplexPlanePolynomial (complexRealPartPoly K) +
                MvPolynomial.C Complex.I * realToComplexPlanePolynomial (complexImagPartPoly K)) := by ring
        _ = H + K := by rw [hH, hK]
  | monomial e c =>
      rw [complexRealPartPoly_monomial, complexImagPartPoly_monomial]
      simp only [realToComplexPlanePolynomial, MvPolynomial.map_monomial]
      ext m
      by_cases hm : e = m
      · subst e
        simp [MvPolynomial.coeff_monomial]
        exact Complex.ext (by simp) (by simp)
      · simp [MvPolynomial.coeff_monomial, hm]

lemma complexification_conj_real_im (H : ComplexPlanePoly) :
    complexPlanePolynomialConjugation H =
      realToComplexPlanePolynomial (complexRealPartPoly H) -
        MvPolynomial.C Complex.I * realToComplexPlanePolynomial (complexImagPartPoly H) := by
  calc
    complexPlanePolynomialConjugation H =
        complexPlanePolynomialConjugation
          (realToComplexPlanePolynomial (complexRealPartPoly H) +
            MvPolynomial.C Complex.I * realToComplexPlanePolynomial (complexImagPartPoly H)) := by
              rw [complexification_real_im H]
    _ = realToComplexPlanePolynomial (complexRealPartPoly H) -
          MvPolynomial.C Complex.I * realToComplexPlanePolynomial (complexImagPartPoly H) := by
      rw [map_add, map_mul, complexPlanePolynomialConjugation_realToComplex]
      simp only [complexPlanePolynomialConjugation_realToComplex]
      simp [complexPlanePolynomialConjugation_apply, Complex.conj_I, sub_eq_add_neg]

lemma complexification_eval_real (p : PlanePoly) (z : Fin 2 → ℝ) :
    MvPolynomial.eval (fun i ↦ Complex.ofReal (z i))
        (realToComplexPlanePolynomial p) = Complex.ofReal (MvPolynomial.eval z p) := by
  have hfun : (fun i : Fin 2 ↦ Complex.ofReal (z i)) =
      (Complex.ofRealHom ∘ z) := by rfl
  rw [realToComplexPlanePolynomial, MvPolynomial.eval_map, hfun,
    ← MvPolynomial.eval_map]
  exact (MvPolynomial.map_eval Complex.ofRealHom z p).symm

lemma totalDegree_conjugation (H : ComplexPlanePoly) :
    (complexPlanePolynomialConjugation H).totalDegree = H.totalDegree := by
  rw [complexPlanePolynomialConjugation_apply]
  rw [MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  apply congrArg (fun s : Finset (Fin 2 →₀ ℕ) ↦ s.sup (fun m ↦ (Finsupp.toMultiset m).card))
  ext m
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
  exact map_ne_zero (starRingEnd ℂ)

private lemma inline_Esgk_NonabsolutePlanePointBound__mul_dvd_of_irreducible_nonassociate
    {a b c : ComplexPlanePoly} (ha : Irreducible a) (hb : Irreducible b)
    (hab : ¬ Associated a b) (hac : a ∣ c) (hbc : b ∣ c) : a * b ∣ c := by
  rcases hac with ⟨q, hq⟩
  have hba : ¬ b ∣ a := by
    intro h
    exact hab (hb.associated_of_dvd ha h).symm
  have hbq : b ∣ q := by
    rcases (irreducible_iff_prime.mp hb).dvd_or_dvd (show b ∣ a * q by
      rw [← hq]
      exact hbc) with h | h
    · exact (hba h).elim
    · exact h
  rcases hbq with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  rw [hq, hr]
  ac_rfl

private lemma inline_Esgk_NonabsolutePlanePointBound__totalDegree_associated_complex {P Q : ComplexPlanePoly}
    (h : Associated P Q) (hP : P ≠ 0) (_hQ : Q ≠ 0) : P.totalDegree = Q.totalDegree := by
  rcases h with ⟨u, hu⟩
  have hu0 : u.val.totalDegree = 0 :=
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp u.isUnit).2
  calc
    P.totalDegree = (P * (↑u : ComplexPlanePoly)).totalDegree := by
      rw [MvPolynomial.totalDegree_mul_of_isDomain hP (by simp [u.isUnit.ne_zero])]
      simp [hu0]
    _ = Q.totalDegree := by rw [hu]


theorem real_irreducible_not_absolutely_irreducible_point_bound
    : RealIrreducibleNotAbsolutelyIrreduciblePointBoundStatement := by
  classical
  intro G S hG hNonabsolute hS
  let F : ComplexPlanePoly := realToComplexPlanePolynomial G
  have hG0 : G ≠ 0 := hG.ne_zero
  have hF0 : F ≠ 0 := by
    dsimp [F]
    exact (MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective).ne hG0
  have hFunit : ¬ IsUnit F := by
    intro hFu
    have hFone : F ∣ realToComplexPlanePolynomial (1 : PlanePoly) := by
      rw [show realToComplexPlanePolynomial (1 : PlanePoly) = 1 by simp]
      exact isUnit_iff_dvd_one.mp hFu
    have hGone : G ∣ 1 := by
      apply (realToComplexPlanePolynomial_dvd_iff hG0).mp
      simpa [F] using hFone
    exact hG.not_isUnit (isUnit_of_dvd_one hGone)
  have hFnonabsolute : ¬ Irreducible F := by
    change ¬ Irreducible (MvPolynomial.map Complex.ofRealHom G)
    exact hNonabsolute
  obtain ⟨H, hH, hHF⟩ := WfDvdMonoid.exists_irreducible_factor hFunit hF0
  let τ := complexPlanePolynomialConjugation
  have hτH : Irreducible (τ H) := hH.map τ
  have hH0 : H ≠ 0 := hH.ne_zero
  have hτH0 : τ H ≠ 0 := by
    intro hz
    apply hH0
    rw [← complexPlanePolynomialConjugation_involutive H, hz]
    simp
  have hτHF : τ H ∣ F := by
    have h := map_dvd τ hHF
    change τ H ∣ τ F at h
    change τ H ∣ τ (realToComplexPlanePolynomial G) at h
    rw [complexPlanePolynomialConjugation_realToComplex G] at h
    exact h
  have hNonassoc : ¬ Associated H (τ H) := by
    intro hassoc
    rcases hassoc.symm with ⟨u, hu⟩
    rcases (MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit) with
      ⟨c, hcunit, huc⟩
    have hu' : τ H * MvPolynomial.C c = H := by
      rw [← huc]
      exact hu
    rcases MvPolynomial.support_nonempty.mpr hH0 with ⟨m, hm⟩
    have hm0 : H.coeff m ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using hm
    have hcoeff : conj (H.coeff m) * c = H.coeff m := by
      have hh := congrArg (fun P : ComplexPlanePoly ↦ P.coeff m) hu'
      have hτcoeff : (τ H).coeff m = conj (H.coeff m) := by
        rw [complexPlanePolynomialConjugation_apply, MvPolynomial.coeff_map]
      calc
        conj (H.coeff m) * c = c * conj (H.coeff m) := by ac_rfl
        _ = (MvPolynomial.C c * τ H).coeff m := by rw [MvPolynomial.coeff_C_mul, hτcoeff]
        _ = (τ H * MvPolynomial.C c).coeff m := by rw [mul_comm]
        _ = H.coeff m := hh
    let K : ComplexPlanePoly := MvPolynomial.C (conj (H.coeff m)) * H
    have hKfixed : τ K = K := by
      dsimp [K]
      calc
        τ (MvPolynomial.C (conj (H.coeff m)) * H) =
            MvPolynomial.C (H.coeff m) * τ H := by
              rw [map_mul, complexPlanePolynomialConjugation_apply, MvPolynomial.map_C]
              simp
        _ = MvPolynomial.C (conj (H.coeff m) * c) * τ H := by rw [hcoeff]
        _ = MvPolynomial.C (conj (H.coeff m)) * (MvPolynomial.C c * τ H) := by
              rw [MvPolynomial.C_mul]
              ac_rfl
        _ = MvPolynomial.C (conj (H.coeff m)) * (τ H * MvPolynomial.C c) := by
              rw [mul_comm (MvPolynomial.C c) (τ H)]
        _ = MvPolynomial.C (conj (H.coeff m)) * H := by rw [hu']
    have hsunit : IsUnit (MvPolynomial.C (conj (H.coeff m)) : ComplexPlanePoly) := by
      rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
      exact ⟨conj (H.coeff m), isUnit_iff_ne_zero.mpr ((map_ne_zero conj).mpr hm0), rfl⟩
    have hKF : K ∣ F := by
      rcases hHF with ⟨q, hq⟩
      rcases hsunit with ⟨v, hv⟩
      refine ⟨(↑(v⁻¹) : ComplexPlanePoly) * q, ?_⟩
      calc
        F = H * q := hq
        _ = (MvPolynomial.C (conj (H.coeff m)) * (↑(v⁻¹) : ComplexPlanePoly)) *
              (H * q) := by rw [← hv, ← Units.val_mul]; simp
        _ = K * ((↑(v⁻¹) : ComplexPlanePoly) * q) := by dsimp [K]; ac_rfl
    obtain ⟨p, hpK⟩ := exists_realToComplexPlanePolynomial_eq_of_conjugation_eq hKfixed
    have hp0 : p ≠ 0 := by
      intro hp
      rcases hKF with ⟨q, hq⟩
      apply hF0
      rw [hq, ← hpK, hp]
      simp
    have hHK : H ∣ K := by
      dsimp [K]
      refine ⟨MvPolynomial.C (conj (H.coeff m)), ?_⟩
      ac_rfl
    have hpG : p ∣ G := (realToComplexPlanePolynomial_dvd_iff hp0).mp (by simpa [F, hpK] using hKF)
    have hpunit : ¬ IsUnit p := by
      intro hpu
      have hKunit : IsUnit K := by rw [← hpK]; exact IsUnit.map _ hpu
      exact hH.not_isUnit (isUnit_of_dvd_one
        (dvd_trans hHK (isUnit_iff_dvd_one.mp hKunit)))
    rcases hpG with ⟨q, hq⟩
    rcases hG.isUnit_or_isUnit hq with hpq | hqunit
    · exact hpunit hpq
    · have hGp : Associated G p := by
        rw [hq]
        exact associated_mul_unit_left p q hqunit
      have hFP : Associated F (realToComplexPlanePolynomial p) := hGp.map _
      have hFK : Associated F K := by simpa [hpK] using hFP
      have hKirr : Irreducible K := by
        dsimp [K]
        exact (irreducible_isUnit_mul hsunit).mpr hH
      exact hFnonabsolute (hFK.symm.irreducible hKirr)
  let Q : ComplexPlanePoly := H * τ H
  have hQ0 : Q ≠ 0 := mul_ne_zero hH0 hτH0
  have hQF : Q ∣ F := inline_Esgk_NonabsolutePlanePointBound__mul_dvd_of_irreducible_nonassociate hH hτH hNonassoc hHF hτHF
  have hQfixed : τ Q = Q := by
    dsimp [Q]
    rw [map_mul, complexPlanePolynomialConjugation_involutive]
    ac_rfl
  obtain ⟨p, hpQ⟩ := exists_realToComplexPlanePolynomial_eq_of_conjugation_eq hQfixed
  have hp0 : p ≠ 0 := by
    intro hp
    rcases hQF with ⟨q, hq⟩
    apply hF0
    rw [hq, ← hpQ, hp]
    simp
  have hpG : p ∣ G := (realToComplexPlanePolynomial_dvd_iff hp0).mp (by simpa [F, hpQ] using hQF)
  have hHQ : H ∣ Q := by
    dsimp [Q]
    exact ⟨τ H, rfl⟩
  have hpunit : ¬ IsUnit p := by
    intro hpu
    have hQunit : IsUnit Q := by rw [← hpQ]; exact IsUnit.map _ hpu
    exact hH.not_isUnit (isUnit_of_dvd_one
      (dvd_trans hHQ (isUnit_iff_dvd_one.mp hQunit)))
  rcases hpG with ⟨q, hq⟩
  have hGp : Associated G p := by
    rcases hG.isUnit_or_isUnit hq with hpq | hqunit
    · exact (hpunit hpq).elim
    · rw [hq]
      exact associated_mul_unit_left p q hqunit
  have hFQ : Associated F Q := by
    have hFP : Associated F (realToComplexPlanePolynomial p) := hGp.map _
    simpa [hpQ] using hFP
  let coord : PachDeZeeuw.Algebraic.Point2 → (Fin 2 → ℝ) := fun x i ↦ x i
  let T : Finset (Fin 2 → ℝ) := S.image coord
  have hcoord : Set.InjOn coord (S : Set PachDeZeeuw.Algebraic.Point2) := by
    intro x hx y hy hxy
    ext i
    exact congrFun hxy i
  have hTcard : T.card = S.card := by
    simpa [T] using Finset.card_image_of_injOn hcoord
  have hTzero : ∀ z ∈ T,
      MvPolynomial.eval z (complexRealPartPoly H) = 0 ∧
        MvPolynomial.eval z (complexImagPartPoly H) = 0 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have hxG : MvPolynomial.eval (fun i ↦ x i) G = 0 :=
      mem_PlaneCurveZeroSet.mp (hS hx)
    have hxF : MvPolynomial.eval (fun i ↦ Complex.ofReal (x i)) F = 0 := by
      rw [complexification_eval_real, hxG]
      simp
    rcases hFQ with ⟨u, hu⟩
    have hxQ : MvPolynomial.eval (fun i ↦ Complex.ofReal (x i)) Q = 0 := by
      rw [← hu, MvPolynomial.eval_mul, hxF, zero_mul]
    have hxH : MvPolynomial.eval (fun i ↦ Complex.ofReal (x i)) H = 0 := by
      have hzprod :
          MvPolynomial.eval (fun i ↦ Complex.ofReal (x i)) H *
              MvPolynomial.eval (fun i ↦ Complex.ofReal (x i)) (τ H) = 0 := by
        simpa [Q, MvPolynomial.eval_mul] using hxQ
      rcases mul_eq_zero.mp hzprod with hzH | hzτ
      · exact hzH
      · have := congrArg conj hzτ
        have hevalconj :
            MvPolynomial.eval (fun i ↦ Complex.ofReal (x i)) (τ H) =
              conj (MvPolynomial.eval (fun i ↦ Complex.ofReal (x i)) H) := by
          rw [complexPlanePolynomialConjugation_apply]
          have hargs : (fun i ↦ Complex.ofReal (x i)) =
              ((conj : ℂ →+* ℂ) ∘ (fun i ↦ Complex.ofReal (x i))) := by
            funext i
            simp
          conv_lhs => rw [hargs]
          rw [← MvPolynomial.map_eval]
        rw [hevalconj] at this
        simpa using this
    constructor
    · rw [complexRealPartPoly_eval, hxH]
      rfl
    · rw [complexImagPartPoly_eval, hxH]
      rfl
  have hNoCommon : ∀ r, Irreducible r → r ∣ complexRealPartPoly H →
      ¬ r ∣ complexImagPartPoly H := by
    intro r hr hRe hIm
    let R := realToComplexPlanePolynomial r
    have hR0 : R ≠ 0 := by
      dsimp [R]
      exact (MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective).ne hr.ne_zero
    have hRH : R ∣ H := by
      rw [← complexification_real_im H]
      exact dvd_add (map_dvd _ hRe) (dvd_mul_of_dvd_right (map_dvd _ hIm) _)
    have hRτ : R ∣ τ H := by
      rw [complexification_conj_real_im H]
      exact dvd_sub (map_dvd _ hRe) (dvd_mul_of_dvd_right (map_dvd _ hIm) _)
    have hRunit : ¬ IsUnit R := by
      intro hRu
      have hRone : R ∣ realToComplexPlanePolynomial (1 : PlanePoly) :=
        by simpa using (isUnit_iff_dvd_one.mp hRu)
      have hrone : r ∣ 1 := (realToComplexPlanePolynomial_dvd_iff hr.ne_zero).mp hRone
      exact hr.not_isUnit (isUnit_of_dvd_one hrone)
    have hHR : Associated H R := (hH.dvd_iff.mp hRH).resolve_left hRunit
    have hτR : Associated (τ H) R := (hτH.dvd_iff.mp hRτ).resolve_left hRunit
    exact hNonassoc (hHR.trans hτR.symm)
  have hNoCommonSwap : ∀ r, Irreducible r → r ∣ complexImagPartPoly H →
      ¬ r ∣ complexRealPartPoly H := by
    intro r hr hIm hRe
    let R := realToComplexPlanePolynomial r
    have hRH : R ∣ H := by
      rw [← complexification_real_im H]
      exact dvd_add (map_dvd _ hRe) (dvd_mul_of_dvd_right (map_dvd _ hIm) _)
    have hRτ : R ∣ τ H := by
      rw [complexification_conj_real_im H]
      exact dvd_sub (map_dvd _ hRe) (dvd_mul_of_dvd_right (map_dvd _ hIm) _)
    have hRunit : ¬ IsUnit R := by
      intro hRu
      have hRone : R ∣ realToComplexPlanePolynomial (1 : PlanePoly) := by
        simpa using (isUnit_iff_dvd_one.mp hRu)
      have hrone : r ∣ 1 := (realToComplexPlanePolynomial_dvd_iff hr.ne_zero).mp hRone
      exact hr.not_isUnit (isUnit_of_dvd_one hrone)
    have hHR : Associated H R := (hH.dvd_iff.mp hRH).resolve_left hRunit
    have hτR : Associated (τ H) R := (hτH.dvd_iff.mp hRτ).resolve_left hRunit
    exact hNonassoc (hHR.trans hτR.symm)
  have hdegRe := complexRealPartPoly_totalDegree_le H
  have hdegIm := complexImagPartPoly_totalDegree_le H
  have hSdeg : S.card ≤ H.totalDegree ^ 2 := by
    rw [← hTcard]
    by_cases hRe0 : complexRealPartPoly H = 0
    · have hIm0 : complexImagPartPoly H ≠ 0 := by
        intro hIm0
        apply hH0
        rw [← complexification_real_im H, hRe0, hIm0]
        simp
      have hcount := coprime_finite_common_zero_count
        (complexImagPartPoly H) (complexRealPartPoly H) T hIm0 hNoCommonSwap
        (by intro z hz; exact ⟨(hTzero z hz).2, (hTzero z hz).1⟩)
      calc
        T.card ≤ (complexImagPartPoly H).totalDegree *
            (complexRealPartPoly H).totalDegree := hcount
        _ ≤ H.totalDegree * H.totalDegree := Nat.mul_le_mul hdegIm hdegRe
        _ = H.totalDegree ^ 2 := by ring
    · have hcount := coprime_finite_common_zero_count
        (complexRealPartPoly H) (complexImagPartPoly H) T hRe0 hNoCommon hTzero
      calc
        T.card ≤ (complexRealPartPoly H).totalDegree *
            (complexImagPartPoly H).totalDegree := hcount
        _ ≤ H.totalDegree * H.totalDegree := Nat.mul_le_mul hdegRe hdegIm
        _ = H.totalDegree ^ 2 := by ring
  have hdegF : F.totalDegree = G.totalDegree := by
    simp [F]
  have hdegQ : Q.totalDegree = H.totalDegree + (τ H).totalDegree := by
    dsimp [Q]
    rw [MvPolynomial.totalDegree_mul_of_isDomain hH0 hτH0]
  have hdegG : G.totalDegree = 2 * H.totalDegree := by
    have hAssocDeg := inline_Esgk_NonabsolutePlanePointBound__totalDegree_associated_complex hFQ hF0 hQ0
    have hdegτ := totalDegree_conjugation H
    rw [hdegF, hdegQ, hdegτ] at hAssocDeg
    omega
  nlinarith

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
theorem mem_factorPointSet {n : ℕ} {p : Config n} {G : PlanePoly}
    {x : PachDeZeeuw.Algebraic.Point2} :
    x ∈ factorPointSet p G ↔ ∃ i ∈ factorPointIndices p G, p i = x := by
  simp [factorPointSet]

 
theorem factorPointSet_subset_PlaneCurveZeroSet {n : ℕ} (p : Config n) (G : PlanePoly) :
    (factorPointSet p G : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G := by
  intro x hx
  rcases mem_factorPointSet.mp hx with ⟨i, hi, rfl⟩
  exact mem_factorPointIndices.mp hi


theorem card_factorPointSet {n : ℕ} {p : Config n} (G : PlanePoly)
    (hp : Function.Injective p) :
    (factorPointSet p G).card = (factorPointIndices p G).card := by
  exact Finset.card_image_of_injOn hp.injOn

 
theorem factorPointSet_subset_toFinset {n : ℕ} (p : Config n) (G : PlanePoly) :
    factorPointSet p G ⊆ Config.toFinset p := by
  intro x hx
  rcases mem_factorPointSet.mp hx with ⟨i, _hi, rfl⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

 
theorem distinctDistances_factorPointSet_le_numDistancesOrdered {n : ℕ}
    (p : Config n) (G : PlanePoly) :
    EuclideanGeometry.distinctDistances (factorPointSet p G) ≤ NumDistancesOrdered p := by
  calc
    EuclideanGeometry.distinctDistances (factorPointSet p G) ≤ EuclideanGeometry.distinctDistances (Config.toFinset p) :=
      distinctDistances_le_of_subset (factorPointSet_subset_toFinset p G)
    _ = NumDistances p := rfl
    _ ≤ NumDistancesOrdered p := numDistances_le_numDistancesOrdered p


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


theorem numDistancesOrdered_lt_numPoints_of_distanceNewton_slack_lt
    (p : Config n) (σ : ℕ) (hn : 0 < n)
    (hσ : (n - 1) + σ = 3 * NumDistancesOrdered p) (
    hslt : σ + 1 < n) :
    NumDistancesOrdered p < n := by
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

open Filter PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem maximallyCircularQuarticDistinctDistances_factorPointIndices_numDistancesOrdered
    (hCurve : MaximallyCircularQuarticDistinctDistancesStatement) :
    ∃ T C : ℕ, 0 < T ∧ 0 < C ∧
      ∀ {n : ℕ} (p : Config n) (G : PlanePoly),
        Function.Injective p →
        Irreducible G →
        IsAbsolutelyIrreducible G →
        ¬ IsCircleFactor G →
        IsMaximallyCircular G →
        T * G.totalDegree ^ 5 ≤ (factorPointIndices p G).card ^ 2 →
          (factorPointIndices p G).card ^ 4 ≤
            C * G.totalDegree ^ 4 * (NumDistancesOrdered p) ^ 3 := by
  rcases hCurve with ⟨T, C, hT, hC, hCurve⟩
  refine ⟨T, C, hT, hC, ?_⟩
  intro n p G hp hGirreducible hGabsolute hGcircle hGmaximal hThreshold
  have hBound := hCurve G (factorPointSet p G) hGirreducible hGabsolute hGcircle
    hGmaximal (factorPointSet_subset_PlaneCurveZeroSet p G)
  rw [card_factorPointSet G hp] at hBound
  calc
    (factorPointIndices p G).card ^ 4 ≤
        C * G.totalDegree ^ 4 * (EuclideanGeometry.distinctDistances (factorPointSet p G)) ^ 3 :=
      hBound hThreshold
    _ ≤ C * G.totalDegree ^ 4 * (NumDistancesOrdered p) ^ 3 := by
      gcongr
      exact distinctDistances_factorPointSet_le_numDistancesOrdered p G

private theorem inline_Esgk_MaximallyCircularQuarticBootstrap__quartic_threshold_failure
    (n s N d T : ℕ) (hd : 0 < d) (hselect : n * d ≤ N * (2 * s))
    (hdegree : d ≤ 2 * s) (hfail : N ^ 2 < T * d ^ 5) :
    n ^ 2 < 32 * T * s ^ 5 := by
  have htwoSPos : 0 < 2 * s := lt_of_lt_of_le hd hdegree
  have hselectSq : n ^ 2 * d ^ 2 ≤ N ^ 2 * (2 * s) ^ 2 := by
    calc
      n ^ 2 * d ^ 2 = (n * d) ^ 2 := by ring
      _ ≤ (N * (2 * s)) ^ 2 := Nat.pow_le_pow_left hselect 2
      _ = N ^ 2 * (2 * s) ^ 2 := by ring
  have hthresholdMul : N ^ 2 * (2 * s) ^ 2 < (T * d ^ 5) * (2 * s) ^ 2 :=
    Nat.mul_lt_mul_of_pos_right hfail (pow_pos htwoSPos 2)
  have hcancelProduct :
      n ^ 2 * d ^ 2 < (T * d ^ 3 * (2 * s) ^ 2) * d ^ 2 := by
    calc
      n ^ 2 * d ^ 2 ≤ N ^ 2 * (2 * s) ^ 2 := hselectSq
      _ < (T * d ^ 5) * (2 * s) ^ 2 := hthresholdMul
      _ = (T * d ^ 3 * (2 * s) ^ 2) * d ^ 2 := by ring
  have hcancel : n ^ 2 < T * d ^ 3 * (2 * s) ^ 2 :=
    Nat.lt_of_mul_lt_mul_right hcancelProduct
  have hdegreePow : d ^ 3 ≤ (2 * s) ^ 3 := Nat.pow_le_pow_left hdegree 3
  calc
    n ^ 2 < T * d ^ 3 * (2 * s) ^ 2 := hcancel
    _ ≤ T * (2 * s) ^ 3 * (2 * s) ^ 2 := by gcongr
    _ = 32 * T * s ^ 5 := by ring

private theorem inline_Esgk_MaximallyCircularQuarticBootstrap__quartic_threshold_success
    (n s N d K C : ℕ) (hn : 0 < n) (hd : 0 < d)
    (hselect : n * d ≤ N * (2 * s))
    (hcurve : N ^ 4 ≤ C * d ^ 4 * K ^ 3) (hK : K ≤ n) :
    n ≤ 16 * C * s ^ 4 := by
  have hselectFourth : n ^ 4 * d ^ 4 ≤ N ^ 4 * (2 * s) ^ 4 := by
    calc
      n ^ 4 * d ^ 4 = (n * d) ^ 4 := by ring
      _ ≤ (N * (2 * s)) ^ 4 := Nat.pow_le_pow_left hselect 4
      _ = N ^ 4 * (2 * s) ^ 4 := by ring
  have hcurveMul : N ^ 4 * (2 * s) ^ 4 ≤
      (C * d ^ 4 * K ^ 3) * (2 * s) ^ 4 :=
    Nat.mul_le_mul_right ((2 * s) ^ 4) hcurve
  have hcancelProduct : n ^ 4 * d ^ 4 ≤
      (C * K ^ 3 * (2 * s) ^ 4) * d ^ 4 := by
    calc
      n ^ 4 * d ^ 4 ≤ N ^ 4 * (2 * s) ^ 4 := hselectFourth
      _ ≤ (C * d ^ 4 * K ^ 3) * (2 * s) ^ 4 := hcurveMul
      _ = (C * K ^ 3 * (2 * s) ^ 4) * d ^ 4 := by ring
  have hcancel : n ^ 4 ≤ C * K ^ 3 * (2 * s) ^ 4 :=
    Nat.le_of_mul_le_mul_right hcancelProduct (pow_pos hd 4)
  have hKPow : K ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hK 3
  have hnFourth : n ^ 4 ≤ (16 * C * s ^ 4) * n ^ 3 := by
    calc
      n ^ 4 ≤ C * K ^ 3 * (2 * s) ^ 4 := hcancel
      _ ≤ C * n ^ 3 * (2 * s) ^ 4 := by gcongr
      _ = (16 * C * s ^ 4) * n ^ 3 := by ring
  have hcancelN : n * n ^ 3 ≤ (16 * C * s ^ 4) * n ^ 3 := by
    calc
      n * n ^ 3 = n ^ 4 := by ring
      _ ≤ (16 * C * s ^ 4) * n ^ 3 := hnFourth
  exact Nat.le_of_mul_le_mul_right hcancelN (pow_pos hn 3)

private theorem inline_Esgk_MaximallyCircularQuarticBootstrap__quartic_failure_to_linear
    (n s T : ℕ) (hs : 0 < s) (hslt : s < n)
    (hfail : n ^ 2 < 32 * T * s ^ 5) :
    n ≤ 32 * T * s ^ 4 := by
  have hT : 0 < T := by
    by_contra hT
    have hTzero : T = 0 := Nat.eq_zero_of_not_pos hT
    simp [hTzero] at hfail
  have hcoeff : 0 < 32 * T := Nat.mul_pos (by norm_num) hT
  by_contra hnot
  have hge : 32 * T * s ^ 4 < n := Nat.lt_of_not_ge hnot
  have hleft : (32 * T * s ^ 4) * s < (32 * T * s ^ 4) * n := by
    have hbase : 0 < 32 * T * s ^ 4 := Nat.mul_pos hcoeff (pow_pos hs 4)
    exact (Nat.mul_lt_mul_left hbase).2 hslt
  have hright : (32 * T * s ^ 4) * n ≤ n * n := by
    exact Nat.mul_le_mul_right n hge.le
  have hcontra : 32 * T * s ^ 5 < n ^ 2 := by
    calc
      32 * T * s ^ 5 = (32 * T * s ^ 4) * s := by ring
      _ < (32 * T * s ^ 4) * n := hleft
      _ ≤ n * n := hright
      _ = n ^ 2 := by ring
  exact Nat.lt_asymm hcontra hfail

 
theorem distinct_distances_deficiency_quartic_bound_of_curve_bound
    (hNonabsoluteBound : RealIrreducibleNotAbsolutelyIrreduciblePointBoundStatement)
    (hCurve : MaximallyCircularQuarticDistinctDistancesStatement) :
    ∃ A : ℕ, 0 < A ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          EuclideanGeometry.InGeneralPosition (Config.toFinset p) →
          ∃ σ : ℕ,
            (n - 1) + σ = 3 * EuclideanGeometry.distinctDistances (Config.toFinset p) ∧
            n ≤ A * (σ + 1) ^ 4 := by
  rcases maximallyCircularQuarticDistinctDistances_factorPointIndices_numDistancesOrdered hCurve with
    ⟨T, C, hT, hC, hCurveIndexed⟩
  let A : ℕ := max 3 (max (32 * T) (16 * C))
  have hApos : 0 < A := by
    dsimp [A]
    omega
  refine ⟨A, hApos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn p hp hgp
  let i : Fin n := ⟨0, hn⟩
  let σ : ℕ := DistanceMissingDegree p i
  have hσordered : (n - 1) + σ = 3 * NumDistancesOrdered p := by
    exact distanceDegreeProfile_add_missingDegree_eq_three_mul_numDistancesOrdered hp hgp i
  have htrichotomy := distanceNewtonElementaryPolynomial_normalizedFactor_trichotomy
    hNonabsoluteBound p σ hn hp hgp hσordered
  dsimp only at htrichotomy
  have hAthree : 3 ≤ A := by simp [A]
  have hAfailure : 32 * T ≤ A := by simp [A]
  have hAsuccess : 16 * C ≤ A := by simp [A]
  have hAone : 1 ≤ A := by omega
  have hspos : 0 < σ + 1 := by omega
  have hsPowOne : σ + 1 ≤ (σ + 1) ^ 4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hspos (by omega : 1 ≤ 4)
  have hsPowTwo : (σ + 1) ^ 2 ≤ (σ + 1) ^ 4 :=
    Nat.pow_le_pow_right hspos (by omega)
  have hσfinal : (n - 1) + σ = 3 * EuclideanGeometry.distinctDistances (Config.toFinset p) := by
    change (n - 1) + σ = 3 * NumDistances p
    rw [numDistances_eq_numDistancesOrdered_of_injective hp]
    exact hσordered
  refine ⟨σ, hσfinal, ?_⟩
  rcases htrichotomy with hCircle | hNonabsolute | hFactor
  · calc
      n ≤ 3 * (σ + 1) := hCircle
      _ ≤ A * (σ + 1) := Nat.mul_le_mul_right _ hAthree
      _ ≤ A * (σ + 1) ^ 4 := Nat.mul_le_mul_left _ hsPowOne
  · calc
      n ≤ (σ + 1) ^ 2 := hNonabsolute
      _ = 1 * (σ + 1) ^ 2 := by simp
      _ ≤ A * (σ + 1) ^ 2 := Nat.mul_le_mul_right _ hAone
      _ ≤ A * (σ + 1) ^ 4 := Nat.mul_le_mul_left _ hsPowTwo
  · rcases hFactor with ⟨G, N, hGfactor, hGirreducible, hGabsolute, hGnoncircle,
      hGmaximal, hGdegreePos, hSelection, hGdegree, hN⟩
    by_cases hs : n ≤ σ + 1
    · calc
        n ≤ σ + 1 := hs
        _ ≤ (σ + 1) ^ 4 := hsPowOne
        _ = 1 * (σ + 1) ^ 4 := by simp
        _ ≤ A * (σ + 1) ^ 4 := Nat.mul_le_mul_right _ hAone
    · have hslt : σ + 1 < n := Nat.lt_of_not_ge hs
      have hDistances : NumDistancesOrdered p ≤ n :=
        (numDistancesOrdered_lt_numPoints_of_distanceNewton_slack_lt
          p σ hn hσordered hslt).le
      have hCurveSelected :
          T * G.totalDegree ^ 5 ≤ N ^ 2 →
            N ^ 4 ≤ C * G.totalDegree ^ 4 * (NumDistancesOrdered p) ^ 3 := by
        intro hThreshold
        rw [hN] at hThreshold ⊢
        exact hCurveIndexed p G hp hGirreducible hGabsolute hGnoncircle hGmaximal hThreshold
      by_cases hThreshold : T * G.totalDegree ^ 5 ≤ N ^ 2
      · have hSuccess := inline_Esgk_MaximallyCircularQuarticBootstrap__quartic_threshold_success n (σ + 1) N G.totalDegree
          (NumDistancesOrdered p) C hn hGdegreePos hSelection
          (hCurveSelected hThreshold) hDistances
        calc
          n ≤ (16 * C) * (σ + 1) ^ 4 := hSuccess
          _ ≤ A * (σ + 1) ^ 4 := Nat.mul_le_mul_right _ hAsuccess
      · have hFailure := inline_Esgk_MaximallyCircularQuarticBootstrap__quartic_threshold_failure n (σ + 1) N G.totalDegree T
          hGdegreePos hSelection hGdegree (Nat.lt_of_not_ge hThreshold)
        have hFailure' := inline_Esgk_MaximallyCircularQuarticBootstrap__quartic_failure_to_linear n (σ + 1) T hspos hslt hFailure
        calc
          n ≤ (32 * T) * (σ + 1) ^ 4 := hFailure'
          _ ≤ A * (σ + 1) ^ 4 := Nat.mul_le_mul_right _ hAfailure

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


theorem real_irreducible_nonabsolute_point_bound :
    RealIrreducibleNotAbsolutelyIrreduciblePointBoundStatement := by
  exact real_irreducible_not_absolutely_irreducible_point_bound













end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


open EuclideanGeometry Filter

namespace Esgk

 
theorem distinct_distances_deficiency_quartic_bound :
    ∃ A : ℕ, 0 < A ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          ∃ σ : ℕ,
            (n - 1) + σ = 3 * EuclideanGeometry.distinctDistances (Config.toFinset p) ∧
            n ≤ A * (σ + 1) ^ 4 := by
  exact distinct_distances_deficiency_quartic_bound_of_curve_bound
    real_irreducible_nonabsolute_point_bound maximally_circular_quartic_distance_bound


end Esgk

end


open EuclideanGeometry Filter Esgk

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          (n : ℝ) / 3 + c * Real.rpow (n : ℝ) (1 / 4 : ℝ) ≤
            (EuclideanGeometry.distinctDistances (Config.toFinset p) : ℝ) := by
    obtain ⟨c, hc, hmain⟩ :=
      eventually_fourth_root_excess_of_quartic_bound
        (P := Config)
        (Q := fun _n p ↦
          Function.Injective p ∧ InGeneralPosition (Config.toFinset p))
        (K := fun _n p ↦ EuclideanGeometry.distinctDistances (Config.toFinset p))
        (by
          obtain ⟨A, hA, hbound⟩ := distinct_distances_deficiency_quartic_bound
          refine ⟨A, hA, ?_⟩
          filter_upwards [hbound] with n hn p hp
          obtain ⟨σ, hsigma, hquartic⟩ := hn p hp.1 hp.2
          exact ⟨σ, hsigma, hquartic⟩)
    refine ⟨c, hc, ?_⟩
    filter_upwards [hmain] with n hn p hp hgp
    exact hn p ⟨hp, hgp⟩
