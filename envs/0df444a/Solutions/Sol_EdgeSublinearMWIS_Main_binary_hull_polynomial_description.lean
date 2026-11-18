-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.binary_hull_polynomial_description
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:08:00.488937+00:00
-- url     : https://prove2.me/submissions/fb969a06-e04f-424d-ada5-d98ba2b5e740

import Definitions.Def_EdgeSublinearMWIS_Main_Ellipsoid
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Hull
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Convex.Topology

-- Solutions.CompactExtremePositive
noncomputable section

set_option autoImplicit false
open Set
namespace EdgeSublinearMWIS.Main.ConvexTools

theorem positive_extreme {n : ℕ} {P : Set (Fin n → ℝ)}
    (hcompact : IsCompact P) (hconvex : Convex ℝ P)
    (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) (hf : Continuous f)
    (hpositive : ∃ x ∈ P, 0 < f x) :
    ∃ x ∈ P.extremePoints ℝ, 0 < f x := by
  by_contra h
  push_neg at h
  have hext : P.extremePoints ℝ ⊆ {x | f x ≤ 0} := by
    intro x hx
    exact h x hx
  have hc : convexHull ℝ (P.extremePoints ℝ) ⊆ {x | f x ≤ 0} :=
    convexHull_min hext (convex_halfSpace_le ⟨f.map_add, fun c x => f.map_smul c x⟩ 0)
  have hclosed : IsClosed {x | f x ≤ 0} := isClosed_le hf continuous_const
  have hP : P ⊆ {x | f x ≤ 0} := by
    rw [← closure_convexHull_extremePoints hcompact hconvex]
    exact closure_minimal hc hclosed
  obtain ⟨x, hx, hp⟩ := hpositive
  exact (hP hx).not_gt hp

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.IntegerVertexScale
noncomputable section

open scoped BigOperators Classical
open Matrix LinearOptimization
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

def integerConstraints {ι : Type} {n : ℕ} (A : ι → Fin n → ℤ) (b : ι → ℤ) :
    ι → LinearConstraint n := fun i => ⟨fun j => (A i j : ℝ), (b i : ℝ), .le⟩

theorem det_unit_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j, |A i j| ≤ 1) : |A.det| ≤ (n.factorial : ℤ) := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) hA
  simpa using h

theorem integer_extreme_scale {ι : Type} [Fintype ι] {n : ℕ}
    (A : ι → Fin n → ℤ) (b : ι → ℤ)
    (hA : ∀ i j, |A i j| ≤ 1) (hb : ∀ i, |b i| ≤ 1)
    (x : Fin n → ℝ)
    (hx : x ∈ (constraintSet (integerConstraints A b)).extremePoints ℝ) :
    ∃ (u : Fin n → ℤ) (t : ℝ), 0 < t ∧
      (∀ j, (u j : ℝ) = t * x j) ∧ ∀ j, |u j| ≤ (n.factorial : ℤ) := by
  have hxP := extremePoints_subset hx
  have hB : IsBasicFeasibleSolution (integerConstraints A b) x :=
    ((lp_vertex_extreme_bfs_equiv (integerConstraints A b) x ⟨x,hxP⟩ hxP).out 1 2).mp hx
  obtain ⟨s, hs, hactive, hlin⟩ := hB.1.2
  let e : Fin n ≃ s := (Fintype.equivFinOfCardEq (by simpa using hs)).symm
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => A (e i).1 j
  let B : Fin n → ℤ := fun i => b (e i).1
  let R : Matrix (Fin n) (Fin n) ℝ := M.map (Int.cast : ℤ → ℝ)
  have hrows : LinearIndependent ℝ R.row := by
    have he := hlin.comp e e.injective
    exact he
  have hdet : R.det ≠ 0 := by
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    rwa [Matrix.isUnit_iff_isUnit_det,isUnit_iff_ne_zero] at hu
  have hsolve : R *ᵥ x = fun i => (B i : ℝ) := by
    funext i
    exact hactive (e i).1 (e i).2
  have hcr : ∀ j, ((M.cramer B j : ℤ) : ℝ) = R.det * x j := by
    intro j
    have h := congrFun (congrArg (fun v => R.adjugate *ᵥ v) hsolve) j
    have hc : R.cramer (fun i => (B i : ℝ)) = R.det • x := by
      rw [Matrix.cramer_eq_adjugate_mulVec, ← hsolve, Matrix.mulVec_mulVec,
        Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hcast : ((M.cramer B j : ℤ) : ℝ) = R.cramer (fun i => (B i : ℝ)) j := by
      simp only [Matrix.cramer_apply]
      rw [Int.cast_det]
      congr 1
      ext i k
      simp [Matrix.updateCol_apply,R]
    rw [hcast,hc]
    rfl
  have hbound : ∀ j, |M.cramer B j| ≤ (n.factorial : ℤ) := by
    intro j
    rw [Matrix.cramer_apply]
    apply det_unit_bound
    intro i k
    by_cases hk : k=j
    · subst k
      simpa [Matrix.updateCol_apply,B] using hb (e i).1
    · rw [Matrix.updateCol_ne hk]
      exact hA (e i).1 k
  by_cases hp : 0 < R.det
  · exact ⟨M.cramer B,R.det,hp,hcr,hbound⟩
  · refine ⟨fun j => - M.cramer B j,- R.det,neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hdet),?_,?_⟩
    · intro j
      rw [Int.cast_neg,hcr]
      ring
    · intro j
      simpa only [abs_neg] using hbound j
end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.BinaryDualPolytope
noncomputable section

open scoped BigOperators Classical
open Matrix LinearOptimization Set
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.BinaryDual
open ConvexTools

def binaryVector {d : ℕ} (v : Fin d → Bool) : Fin d → ℝ := fun i => if v i then 1 else 0

def liftedNormal {d : ℕ} (v : Fin d → Bool) : Fin (d+1) → ℤ :=
  Fin.cons (-1) (fun i => if v i then 1 else 0)

abbrev indices {d : ℕ} (V : Finset (Fin d → Bool)) := V ⊕ (Fin (d+1) × Bool)

def normal {d : ℕ} (V : Finset (Fin d → Bool)) : indices V → Fin (d+1) → ℤ
  | .inl v => liftedNormal v.1
  | .inr (j,b) => Pi.single j (if b then 1 else -1)

def rhs {d : ℕ} (V : Finset (Fin d → Bool)) : indices V → ℤ
  | .inl _ => 0
  | .inr _ => 1

abbrev dualPolytope {d : ℕ} (V : Finset (Fin d → Bool)) :=
  constraintSet (integerConstraints (normal V) (rhs V))

theorem normal_bound {d : ℕ} (V : Finset (Fin d → Bool)) :
    ∀ i j, |normal V i j| ≤ 1 := by
  intro i j
  cases i with
  | inl v =>
    refine Fin.cases ?_ (fun k => ?_) j
    · norm_num [normal,liftedNormal]
    · cases h : v.1 k <;> norm_num [normal,liftedNormal,h]
  | inr k =>
    rcases k with ⟨k,b⟩
    by_cases hj : j=k
    · subst j
      cases b <;> norm_num [normal]
    · simp [normal,Pi.single_apply,hj]

theorem rhs_bound {d : ℕ} (V : Finset (Fin d → Bool)) :
    ∀ i, |rhs V i| ≤ 1 := by
  intro i
  cases i <;> norm_num [rhs]

theorem mem_dual_iff {d : ℕ} (V : Finset (Fin d → Bool)) (u : Fin (d+1) → ℝ) :
    u ∈ dualPolytope V ↔
      (∀ v ∈ V, (fun i => (liftedNormal v i : ℝ)) ⬝ᵥ u ≤ 0) ∧
      ∀ j, -1 ≤ u j ∧ u j ≤ 1 := by
  constructor
  · intro h
    constructor
    · intro v hv
      simpa [integerConstraints,normal,rhs,LinearConstraint.IsSatisfiedAt] using h (.inl ⟨v,hv⟩)
    · intro j
      have hhi := h (.inr (j,true))
      have hlo := h (.inr (j,false))
      simp only [integerConstraints,normal,rhs,LinearConstraint.IsSatisfiedAt,
        Bool.false_eq_true,if_false,if_true,
        Bool.false_eq_true,if_false,if_true,
          Pi.single_apply,Int.cast_ite,Int.cast_neg,Int.cast_one,Int.cast_zero,
        dotProduct,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,one_mul,neg_mul] at hlo hhi
      constructor <;> linarith
  · rintro ⟨hV,hbox⟩ i
    cases i with
    | inl v => simpa [integerConstraints,normal,rhs,LinearConstraint.IsSatisfiedAt] using hV v.1 v.2
    | inr k =>
      rcases k with ⟨j,b⟩
      cases b <;>
        simp only [integerConstraints,normal,rhs,LinearConstraint.IsSatisfiedAt,
          Bool.false_eq_true,if_false,if_true,
          Pi.single_apply,Int.cast_ite,Int.cast_neg,Int.cast_one,Int.cast_zero,
          dotProduct,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true,one_mul,neg_mul]
      · linarith [(hbox j).1]
      · exact (hbox j).2

theorem dual_closed {d : ℕ} (V : Finset (Fin d → Bool)) : IsClosed (dualPolytope V) := by
  change IsClosed {x | ∀ i : indices V, (fun j => (normal V i j : ℝ)) ⬝ᵥ x ≤ (rhs V i : ℝ)}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_le _ continuous_const
  unfold dotProduct
  fun_prop

theorem dual_convex {d : ℕ} (V : Finset (Fin d → Bool)) : Convex ℝ (dualPolytope V) := by
  change Convex ℝ {x | ∀ i : indices V, (fun j => (normal V i j : ℝ)) ⬝ᵥ x ≤ (rhs V i : ℝ)}
  simp only [setOf_forall]
  apply convex_iInter
  intro i
  apply convex_halfSpace_le
  constructor
  · intro x y
    exact dotProduct_add _ _ _
  · intro c x
    simp only [dotProduct_smul,smul_eq_mul]

theorem dual_compact {d : ℕ} (V : Finset (Fin d → Bool)) : IsCompact (dualPolytope V) := by
  apply (isCompact_Icc : IsCompact (Icc (fun _ : Fin (d+1) => (-1 : ℝ)) (fun _ => 1))).of_isClosed_subset (dual_closed V)
  intro u hu
  have hb := (mem_dual_iff V u).mp hu
  exact ⟨fun j => (hb.2 j).1,fun j => (hb.2 j).2⟩

end EdgeSublinearMWIS.Main.BinaryDual
end

-- Solutions.BinaryHullSeparator
noncomputable section

open scoped BigOperators Classical
open Matrix LinearOptimization Set
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.BinaryDual
open ConvexTools

theorem binaryHull_eq_image {d : ℕ} (V : Finset (Fin d → Bool)) :
    binaryHull V = convexHull ℝ (binaryVector '' (V : Set (Fin d → Bool))) := by
  unfold binaryHull
  congr 1
  ext z
  simp only [mem_setOf_eq,mem_image,Finset.mem_coe]
  constructor
  · rintro ⟨v,hv,hz⟩
    exact ⟨v,hv,funext hz |>.symm⟩
  · rintro ⟨v,hv,rfl⟩
    exact ⟨v,hv,fun _ => rfl⟩

theorem binaryHull_closed {d : ℕ} (V : Finset (Fin d → Bool)) : IsClosed (binaryHull V) := by
  rw [binaryHull_eq_image]
  exact (V.finite_toSet.image binaryVector).isClosed_convexHull (𝕜 := ℝ)

theorem functional_as_dot {d : ℕ} (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (x : Fin d → ℝ) :
    f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
  have hx : x = ∑ i : Fin d, x i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply,eq_comm]
  conv_lhs => rw [hx]
  simp [dotProduct,mul_comm]

theorem normalized_dual_positive {d : ℕ} (V : Finset (Fin d → Bool))
    (z : Fin d → ℝ) (hz : z ∉ binaryHull V) :
    ∃ u ∈ dualPolytope V, 0 < (Fin.cons (-1) z) ⬝ᵥ u := by
  obtain ⟨f,b,hV,hz'⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (binaryHull_closed V) hz
  let a : Fin d → ℝ := fun i => f (Pi.single i 1)
  let u : Fin (d+1) → ℝ := Fin.cons b a
  let D : ℝ := (∑ j, |u j|)+1
  have hD : 0 < D := by dsimp [D]; positivity
  let t : ℝ := D⁻¹
  have ht : 0 < t := inv_pos.mpr hD
  have hrepr : ∀ x, f x = a ⬝ᵥ x := fun x => functional_as_dot f.toLinearMap x
  have huv : ∀ v ∈ V, (fun i => (liftedNormal v i : ℝ)) ⬝ᵥ u ≤ 0 := by
    intro v hv
    have hvH : binaryVector v ∈ binaryHull V := subset_convexHull ℝ _ ⟨v,hv,fun _ => rfl⟩
    have hf := hV (binaryVector v) hvH
    rw [hrepr] at hf
    simp only [dotProduct,Fin.sum_univ_succ,liftedNormal,Fin.cons_zero,
      Fin.cons_succ,Int.cast_neg,Int.cast_one,Int.cast_ite,Int.cast_zero,u,
      neg_one_mul]
    have he : (∑ i, (if v i = true then (1:ℝ) else 0) * a i) = a ⬝ᵥ binaryVector v := by
      simp [dotProduct,binaryVector,mul_comm]
    rw [he]
    linarith
  refine ⟨t • u,(mem_dual_iff V _).mpr ⟨?_,?_⟩,?_⟩
  · intro v hv
    rw [dotProduct_smul,smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos ht.le (huv v hv)
  · intro j
    have hj : |u j| ≤ ∑ i, |u i| := Finset.single_le_sum (f := fun i => |u i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have ha : |(t • u) j| ≤ 1 := by
      simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_pos ht]
      rw [← div_eq_inv_mul]
      apply (div_le_one hD).mpr
      dsimp only [D]
      linarith
    exact abs_le.mp ha
  · rw [dotProduct_smul,smul_eq_mul]
    apply mul_pos ht
    have he : (Fin.cons (-1) z) ⬝ᵥ u = a ⬝ᵥ z-b := by
      simp [dotProduct,Fin.sum_univ_succ,u,mul_comm,sub_eq_add_neg,add_comm]
    rw [he,← hrepr]
    linarith

theorem integer_separator {d : ℕ} (V : Finset (Fin d → Bool))
    (z : Fin d → ℝ) (hz : z ∉ binaryHull V) :
    ∃ (a : Fin d → ℤ) (b : ℤ),
      (∀ i, |a i| ≤ ((d+1).factorial : ℤ)) ∧ |b| ≤ ((d+1).factorial : ℤ) ∧
      (∀ v ∈ V, (fun i => (a i : ℝ)) ⬝ᵥ binaryVector v ≤ (b : ℝ)) ∧
      (b : ℝ) < (fun i => (a i : ℝ)) ⬝ᵥ z := by
  let objective : (Fin (d+1) → ℝ) →ₗ[ℝ] ℝ :=
    dotProductBilin ℝ ℝ (Fin.cons (-1) z)
  have hobj : Continuous objective := by
    change Continuous (fun u => (Fin.cons (-1) z) ⬝ᵥ u)
    unfold dotProduct
    fun_prop
  obtain ⟨x,hx,hpx⟩ := positive_extreme (dual_compact V) (dual_convex V) objective hobj
    (normalized_dual_positive V z hz)
  obtain ⟨u,t,ht,hux,hub⟩ := integer_extreme_scale (normal V) (rhs V)
    (normal_bound V) (rhs_bound V) x hx
  have hxP := (mem_dual_iff V x).mp (extremePoints_subset hx)
  refine ⟨fun i => u i.succ,u 0,fun i => hub i.succ,hub 0,?_,?_⟩
  · intro v hv
    have h := mul_nonpos_of_nonneg_of_nonpos ht.le (hxP.1 v hv)
    have he : (fun i => (u i : ℝ)) = t • x := by ext i; exact hux i
    have hh : (fun i => (liftedNormal v i : ℝ)) ⬝ᵥ (fun i => (u i : ℝ)) ≤ 0 := by
      rw [he,dotProduct_smul,smul_eq_mul]
      exact h
    simp only [dotProduct,Fin.sum_univ_succ,liftedNormal,Fin.cons_zero,
      Fin.cons_succ,Int.cast_neg,Int.cast_one,Int.cast_ite,Int.cast_zero,
      neg_one_mul] at hh
    have heq : (∑ i, (if v i = true then (1:ℝ) else 0) * (u i.succ : ℝ)) =
        (fun i => (u i.succ : ℝ)) ⬝ᵥ binaryVector v := by
      simp [dotProduct,binaryVector,mul_comm]
    rw [heq] at hh
    linarith
  · have h := mul_pos ht hpx
    have he : (fun i => (u i : ℝ)) = t • x := by ext i; exact hux i
    have hh : 0 < (Fin.cons (-1) z) ⬝ᵥ (fun i => (u i : ℝ)) := by
      rw [he,dotProduct_smul,smul_eq_mul]
      exact h
    simp only [dotProduct,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,neg_one_mul] at hh
    have heq : (∑ i, z i * (u i.succ : ℝ)) = (fun i => (u i.succ : ℝ)) ⬝ᵥ z := by
      simp only [dotProduct,mul_comm]
    rw [heq] at hh
    linarith

end EdgeSublinearMWIS.Main.BinaryDual
end

-- Solutions.IntegerHalfspaceEncoding
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryDual

theorem factorial_lt_two_pow_square (D : ℕ) : D.factorial < 2 ^ (D*D+1) := by
  calc
    D.factorial ≤ D^D := Nat.factorial_le_pow D
    _ ≤ (2^D)^D := Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self)) D
    _ = 2^(D*D) := (pow_mul 2 D D).symm
    _ < 2^(D*D+1) := Nat.pow_lt_pow_right (by decide) (by omega)

theorem integer_rat_encoding_bound (D : ℕ) (z : ℤ) (hz : |z| ≤ (D.factorial : ℤ)) :
    (encodeRat (z : ℚ)).length ≤ 2*(D*D+1)+5 := by
  have hnat : z.natAbs ≤ D.factorial := by
    rw [← Int.natCast_natAbs] at hz
    exact_mod_cast hz
  have hbits : (natBits z.natAbs).length ≤ D*D+1 := by
    simp only [natBits,List.length_map]
    apply (Nat.digits_length_le_iff (by decide : 1<2) _).mpr
    exact hnat.trans_lt (factorial_lt_two_pow_square D)
  have hone : (natBits 1).length=1 := by decide
  simp only [encodeRat,Rat.num_intCast,Rat.den_intCast,encodeInt,encodeNat,
    List.length_append,List.length_replicate,List.length_singleton,hone]
  omega

def integralHalfspace {d : ℕ} (u : Fin (d+1) → ℤ) : RationalHalfspace d :=
  ⟨fun i => (u i.succ : ℚ),(u 0 : ℚ)⟩

theorem integralHalfspace_bits {d : ℕ} (u : Fin (d+1) → ℤ)
    (hu : ∀ i, |u i| ≤ ((d+1).factorial : ℤ)) :
    (integralHalfspace u).bits.length ≤ 10*(d+1)^3 := by
  have hs : (∑ i : Fin d, (encodeRat (u i.succ : ℚ)).length) ≤
      d*(2*((d+1)*(d+1)+1)+5) := by
    calc
      _ ≤ ∑ _i : Fin d, (2*((d+1)*(d+1)+1)+5) :=
        Finset.sum_le_sum (fun i _ => integer_rat_encoding_bound (d+1) (u i.succ) (hu i.succ))
      _ = _ := by simp
  have hb := integer_rat_encoding_bound (d+1) (u 0) (hu 0)
  have he : (integralHalfspace u).bits.length =
      (∑ i : Fin d, (encodeRat (u i.succ : ℚ)).length)+(encodeRat (u 0 : ℚ)).length := by
    simp [RationalHalfspace.bits,vectorBits,integralHalfspace,List.length_flatten,
      List.map_ofFn,List.sum_ofFn]
  rw [he]
  nlinarith [sq_nonneg (d:ℤ)]

end EdgeSublinearMWIS.Main.BinaryDual
end

-- Solutions.BinaryHullDescription
noncomputable section

open scoped BigOperators Classical
open Matrix Set
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.BinaryDual

def candidates (d : ℕ) : Finset (Fin (d+1) → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-((d+1).factorial : ℤ)) ((d+1).factorial : ℤ))

theorem mem_candidates {d : ℕ} (u : Fin (d+1) → ℤ) :
    u ∈ candidates d ↔ ∀ i, |u i| ≤ ((d+1).factorial : ℤ) := by
  simp [candidates,Fintype.mem_piFinset,abs_le]

def validOn {d : ℕ} (V : Finset (Fin d → Bool)) (u : Fin (d+1) → ℤ) : Prop :=
  ∀ v ∈ V, (fun i => (u i.succ : ℝ)) ⬝ᵥ binaryVector v ≤ (u 0 : ℝ)

def description {d : ℕ} (V : Finset (Fin d → Bool)) : List (RationalHalfspace d) :=
  ((candidates d).toList.filter (fun u => decide (validOn V u))).map integralHalfspace

theorem description_mem {d : ℕ} (V : Finset (Fin d → Bool)) (c : RationalHalfspace d) :
    c ∈ description V ↔ ∃ u ∈ candidates d, validOn V u ∧ c=integralHalfspace u := by
  simp only [description,List.mem_map,List.mem_filter,Finset.mem_toList,decide_eq_true_eq]
  constructor
  · rintro ⟨u,⟨hu,hv⟩,hc⟩
    exact ⟨u,hu,hv,hc.symm⟩
  · rintro ⟨u,hu,hv,rfl⟩
    exact ⟨u,⟨hu,hv⟩,rfl⟩

theorem description_bitbound {d : ℕ} (V : Finset (Fin d → Bool)) :
    ∀ c ∈ description V, c.bits.length ≤ 10*(d+1)^3 := by
  intro c hc
  obtain ⟨u,hu,hv,rfl⟩ := (description_mem V c).mp hc
  exact integralHalfspace_bits u ((mem_candidates u).mp hu)

theorem integralHalfspace_eval {d : ℕ} (u : Fin (d+1) → ℤ) (z : Fin d → ℝ) :
    (integralHalfspace u).evalReal z=(fun i => (u i.succ : ℝ)) ⬝ᵥ z := by
  simp [RationalHalfspace.evalReal,integralHalfspace,dotProduct]

theorem integralHalfspace_bound {d : ℕ} (u : Fin (d+1) → ℤ) :
    ((integralHalfspace u).bound : ℝ)=(u 0 : ℝ) := by
  simp [integralHalfspace]

theorem description_exact {d : ℕ} (V : Finset (Fin d → Bool)) (z : Fin d → ℝ) :
    z ∈ binaryHull V ↔ ∀ c ∈ description V, c.evalReal z ≤ (c.bound : ℝ) := by
  constructor
  · intro hz c hc
    obtain ⟨u,hu,hvalid,rfl⟩ := (description_mem V c).mp hc
    rw [integralHalfspace_eval,integralHalfspace_bound]
    have hH : binaryHull V ⊆ {x | (fun i => (u i.succ : ℝ)) ⬝ᵥ x ≤ (u 0 : ℝ)} := by
      rw [binaryHull_eq_image]
      apply convexHull_min
      · rintro _ ⟨v,hv,rfl⟩
        exact hvalid v hv
      · apply convex_halfSpace_le
        constructor
        · intro a b
          exact dotProduct_add _ _ _
        · intro a b
          simp only [dotProduct_smul,smul_eq_mul]
    exact hH hz
  · intro h
    by_contra hz
    obtain ⟨a,b,ha,hb,hv,hstrict⟩ := integer_separator V z hz
    let u : Fin (d+1) → ℤ := Fin.cons b a
    have hu : u ∈ candidates d := by
      apply (mem_candidates u).mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hb
      · exact ha j
    have hvalid : validOn V u := hv
    have hc : integralHalfspace u ∈ description V :=
      (description_mem V _).mpr ⟨u,hu,hvalid,rfl⟩
    have hh := h _ hc
    rw [integralHalfspace_eval,integralHalfspace_bound] at hh
    exact hstrict.not_ge hh

end EdgeSublinearMWIS.Main.BinaryDual

namespace EdgeSublinearMWIS.Main

theorem binary_hull_description_bound :
    BinaryHullDescriptions (Polynomial.C 10 * Polynomial.X^3) := by
  intro d V
  refine ⟨BinaryDual.description V,?_,BinaryDual.description_exact V⟩
  intro c hc
  simpa using BinaryDual.description_bitbound V c hc

end EdgeSublinearMWIS.Main
end

-- Solutions.Sol_binary_description
noncomputable section

theorem solution : EdgeSublinearMWIS.Main.BinaryHullDescriptions
    (Polynomial.C 10 * Polynomial.X^3) :=
  EdgeSublinearMWIS.Main.binary_hull_description_bound
end
