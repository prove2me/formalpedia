-- Prove2me | solution 1 for CurveSymmetry.family_branch_points
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:04:28.563318+00:00
-- url     : https://prove2.me/submissions/ea4a15ba-1a0d-4256-926b-f7e497f5f875

-- Solution generated from lean/FamilyBranchPoints.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Theorems.Thm_CurveSymmetry_familyH_roots_card
import Theorems.Thm_CurveSymmetry_placeCenter_primeValuationSubring
import Theorems.Thm_CurveSymmetry_place_eq_infinity_of_t_notMem
import Theorems.Thm_CurveSymmetry_quadPlace_X_inv_mem_iff
import Theorems.Thm_CurveSymmetry_quad_finite_place_classification
import Theorems.Thm_CurveSymmetry_quad_points_over
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint.Basic

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
section Generic
variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]
/-- An element of the center has no inverse in the valuation subring. -/
lemma inv_notMem_of_mem_placeCenter (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O)
    {a : A} (ha : a ∈ placeCenter K O hO) (ha0 : algebraMap A K a ≠ 0) :
    (algebraMap A K a)⁻¹ ∉ O := by
  intro hinv
  rw [mem_placeCenter] at ha
  have h1 := (O.valuation_le_one_iff _).mpr hinv
  rw [map_inv₀] at h1
  have hpos : 0 < O.valuation (algebraMap A K a) := by
    rw [Valuation.pos_iff]
    exact ha0
  exact absurd ((inv_le_one₀ hpos).mp h1) (not_le.mpr ha)
end Generic
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityMap_t :
    familyInfinityMap m α (algebraMap ℂ[X] (QuadField (familyH m α)) X) =
      (algebraMap ℂ[X] (QuadField (familyH m (star α))) X)⁻¹ := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m α)),
    familyInfinityMap_of, RatFunc.algebraMap_X, ratInv_X, map_inv₀,
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m (star α))),
    RatFunc.algebraMap_X]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma mem_familyInfinityPlace (x : QuadField (familyH m α)) :
    x ∈ familyInfinityPlace m α ↔
      familyInfinityMap m α x ∈ quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α) :=
  Iff.rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityPlace_ne_top : familyInfinityPlace m α ≠ ⊤ := by
  intro htop
  apply ((quad_finite_place_classification (familyH m (star α))).1 0 0
    (familyH_star_zero_point m α)).1
  refine top_unique fun y _ => ?_
  obtain ⟨x, rfl⟩ := familyInfinityMap_surjective (m := m) (α := α) y
  have hx : x ∈ familyInfinityPlace m α := by
    rw [htop]
    exact ValuationSubring.mem_top _
  exact (mem_familyInfinityPlace x).mp hx
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityPlace_const (c : ℂ) :
    algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ familyInfinityPlace m α := by
  rw [mem_familyInfinityPlace, familyInfinityMap_polyC]
  exact ((quad_finite_place_classification (familyH m (star α))).1 0 0
    (familyH_star_zero_point m α)).2 _
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyInfinityPlace_t_notMem :
    algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ familyInfinityPlace m α := by
  rw [mem_familyInfinityPlace, familyInfinityMap_t]
  intro hmem
  exact ((quadPlace_X_inv_mem_iff _ 0 0 (familyH_star_zero_point m α)).mp hmem) rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- A place containing the constants and `t` is a point place (G07b-2c). -/
lemma place_eq_quadPlace_of_t_mem (O : ValuationSubring (QuadField (familyH m α)))
    (htop : O ≠ ⊤) (hconst : ∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O)
    (ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∈ O) :
    ∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd := by
  apply (quad_finite_place_classification (familyH m α)).2.1 O htop
  intro p
  induction p using Polynomial.induction_on with
  | C a => exact hconst a
  | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
  | monomial n a hn =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact mul_mem hn ht
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial OnePoint
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- In a point place, `1/p(t)` is integral iff `p` does not vanish at the point. -/
lemma quadPlace_poly_inv_mem_iff (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
    (c d : ℂ) (hd : d ^ 2 = h.eval c) (p : ℂ[X]) (hp : p ≠ 0) :
    (algebraMap ℂ[X] (QuadField h) p)⁻¹ ∈ quadPlace h c d hd ↔ p.eval c ≠ 0 := by
  have hA := algebraMap_mem_primeValuationSubring (K := QuadField h)
    (quadEval_ker_ne_bot h c d hd)
  have hcenter := placeCenter_primeValuationSubring (K := QuadField h)
    (RingHom.ker (quadEval h c d hd)) (quadEval_ker_ne_bot h c d hd)
  have hpeq : algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.of (quadPoly h) p) =
      algebraMap ℂ[X] (QuadField h) p :=
    ((quadRingMap h).commutes p)
  have hmem : AdjoinRoot.of (quadPoly h) p ∈ RingHom.ker (quadEval h c d hd) ↔ p.eval c = 0 := by
    rw [RingHom.mem_ker, quadEval_of]
  have hp0 : algebraMap ℂ[X] (QuadField h) p ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h)]
    exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
      (RatFunc.algebraMap_ne_zero hp)
  change (algebraMap ℂ[X] (QuadField h) p)⁻¹ ∈ primeValuationSubring (QuadField h)
    (RingHom.ker (quadEval h c d hd)) (quadEval_ker_ne_bot h c d hd) ↔ p.eval c ≠ 0
  rw [← hpeq]
  constructor
  · intro hinv hc
    have hin : AdjoinRoot.of (quadPoly h) p ∈ placeCenter (QuadField h)
        (primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
          (quadEval_ker_ne_bot h c d hd)) hA := by
      rw [hcenter, hmem]
      exact hc
    exact inv_notMem_of_mem_placeCenter _ hA hin (hpeq ▸ hp0) hinv
  · intro hc
    have hnot : AdjoinRoot.of (quadPoly h) p ∉ placeCenter (QuadField h)
        (primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
          (quadEval_ker_ne_bot h c d hd)) hA := by
      rw [hcenter, hmem]
      exact hc
    exact inv_mem_of_notMem_placeCenter _ hA hnot
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial OnePoint
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- Places over a finite point `c` are exactly the point places `(c, d)`. -/
lemma mem_familyPlacesOver_coe (c : ℂ) (O : ValuationSubring (QuadField (familyH m α))) :
    O ∈ familyPlacesOver m α (c : OnePoint ℂ) ↔
      ∃ (d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd := by
  have hfin := quad_finite_place_classification (familyH m α)
  have hXC : (X - C c : ℂ[X]) ≠ 0 := X_sub_C_ne_zero c
  constructor
  · rintro ⟨htop, hconst, hlie, hinv⟩
    have ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∈ O := by
      have he : algebraMap ℂ[X] (QuadField (familyH m α)) X =
          algebraMap ℂ[X] (QuadField (familyH m α)) (X - C c) +
            algebraMap ℂ[X] (QuadField (familyH m α)) (C c) := by
        rw [← map_add, sub_add_cancel]
      rw [he]
      exact add_mem hlie (hconst c)
    obtain ⟨c', d, hd, rfl⟩ := place_eq_quadPlace_of_t_mem O htop hconst ht
    have hc : c' = c := by
      by_contra hne
      apply hinv
      rw [quadPlace_poly_inv_mem_iff _ c' d hd _ hXC, eval_sub, eval_X, eval_C, sub_ne_zero]
      exact hne
    subst hc
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨(hfin.1 c d hd).1, fun c' => (hfin.1 c d hd).2 _, (hfin.1 c d hd).2 _, ?_⟩
    rw [quadPlace_poly_inv_mem_iff _ c d hd _ hXC, eval_sub, eval_X, eval_C, sub_self]
    exact fun h => h rfl
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial OnePoint
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- The places over `∞` are exactly the place at infinity. -/
lemma familyPlacesOver_infty : familyPlacesOver m α ∞ = {familyInfinityPlace m α} := by
  ext O
  simp only [familyPlacesOver, elim_infty, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨htop, hconst, ht⟩
    exact place_eq_infinity_of_t_notMem O htop hconst ht
  · rintro rfl
    exact ⟨familyInfinityPlace_ne_top, familyInfinityPlace_const, familyInfinityPlace_t_notMem⟩
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial OnePoint
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
lemma familyPlacesOver_coe_eq (c : ℂ) :
    familyPlacesOver m α (c : OnePoint ℂ) =
      Set.range (fun d : {d : ℂ // d ^ 2 = (familyH m α).eval c} =>
        quadPlace (familyH m α) c d.1 d.2) := by
  ext O
  rw [mem_familyPlacesOver_coe]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩
  · rintro ⟨⟨d, hd⟩, rfl⟩
    exact ⟨d, hd, rfl⟩
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open Polynomial OnePoint
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
/-- Two places over `c` when `h_α(c) ≠ 0`, one when `h_α(c) = 0`. -/
lemma familyPlacesOver_coe_ncard (c : ℂ) :
    (familyPlacesOver m α (c : OnePoint ℂ)).ncard =
      if (familyH m α).eval c = 0 then 1 else 2 := by
  have hinj : Function.Injective (fun d : {d : ℂ // d ^ 2 = (familyH m α).eval c} =>
      quadPlace (familyH m α) c d.1 d.2) := by
    intro d d' he
    exact Subtype.ext ((quad_finite_place_classification (familyH m α)).2.2 c d.1 c d'.1
      d.2 d'.2 he).2
  rw [familyPlacesOver_coe_eq, Set.ncard_range_of_injective hinj]
  obtain ⟨hne, hzero⟩ := quad_points_over (familyH m α) c
  split_ifs with hc
  · have hset : {d : ℂ | d ^ 2 = (familyH m α).eval c} = {0} := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact hzero hc d
    rw [show Nat.card {d : ℂ // d ^ 2 = (familyH m α).eval c} =
        Nat.card ({d : ℂ | d ^ 2 = (familyH m α).eval c} : Set ℂ) from rfl,
      Nat.card_coe_set_eq, hset, Set.ncard_singleton]
  · obtain ⟨d₀, hd₀, hiff⟩ := hne hc
    have hset : {d : ℂ | d ^ 2 = (familyH m α).eval c} = {d₀, -d₀} := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hiff d
    rw [show Nat.card {d : ℂ // d ^ 2 = (familyH m α).eval c} =
        Nat.card ({d : ℂ | d ^ 2 = (familyH m α).eval c} : Set ℂ) from rfl,
      Nat.card_coe_set_eq, hset, Set.ncard_pair hd₀]
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open Polynomial OnePoint
variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]
theorem solution :
    {p : OnePoint ℂ | IsFamilyBranchPoint m α p} =
        insert ∞ (((↑) : ℂ → OnePoint ℂ) '' ((familyH m α).roots.toFinset : Set ℂ)) ∧
      {p : OnePoint ℂ | IsFamilyBranchPoint m α p}.ncard = 2 * m + 2 ∧
      IsFamilyBranchPoint m α ∞ ∧ IsFamilyBranchPoint m α ((0 : ℂ) : OnePoint ℂ) ∧
      ∀ c : ℂ, (familyH m α).eval c ≠ 0 → (familyPlacesOver m α (c : OnePoint ℂ)).ncard = 2 := by
  have hh0 : familyH m α ≠ 0 := (familyH_squarefree_of hm.out ha.out).ne_zero
  have hbranch_coe (c : ℂ) : IsFamilyBranchPoint m α (c : OnePoint ℂ) ↔ (familyH m α).eval c = 0 := by
    unfold IsFamilyBranchPoint
    rw [familyPlacesOver_coe_ncard]
    split_ifs with hc <;> simp [hc]
  have hbranch_infty : IsFamilyBranchPoint m α ∞ := by
    unfold IsFamilyBranchPoint
    rw [familyPlacesOver_infty, Set.ncard_singleton]
    norm_num
  have hset : {p : OnePoint ℂ | IsFamilyBranchPoint m α p} =
      insert ∞ (((↑) : ℂ → OnePoint ℂ) '' ((familyH m α).roots.toFinset : Set ℂ)) := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp [hbranch_infty]
    | coe c =>
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image, Finset.mem_coe,
          Multiset.mem_toFinset, mem_roots hh0, IsRoot.def, hbranch_coe]
        constructor
        · intro hc
          exact Or.inr ⟨c, hc, rfl⟩
        · rintro (h | ⟨c', hc', he⟩)
          · exact absurd h (OnePoint.coe_ne_infty c)
          · rw [← OnePoint.coe_injective he]
            exact hc'
  refine ⟨hset, ?_, hbranch_infty, (hbranch_coe 0).mpr (familyH_eval_zero m α), fun c hc => ?_⟩
  · rw [hset, Set.ncard_insert_of_notMem, Set.ncard_image_of_injective _ OnePoint.coe_injective,
      Set.ncard_coe_finset, familyH_roots_card hm.out ha.out]
    · rintro ⟨c, -, hc⟩
      exact OnePoint.coe_ne_infty c hc
  · rw [familyPlacesOver_coe_ncard, if_neg hc]
end

#print axioms solution
