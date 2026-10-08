-- Prove2me | solution 1 for CurveSymmetry.family_metric_circle_card
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:59:30.716513+00:00
-- url     : https://prove2.me/submissions/911afb2d-76c0-4247-9cbb-76abb162ed28

-- Solution generated from lean/FamilyCircleSections.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_family_locus_eq
import Theorems.Thm_CurveSymmetry_family_point_of_norm
import Theorems.Thm_CurveSymmetry_family_root_symmetry
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma mul_star_eq_one_of_norm {a : ℂ} (ha : ‖a‖ = 1) : a * star a = 1 := by
  have hn : a ≠ 0 := by intro h; simp [h] at ha
  change a * (starRingEnd ℂ) a = 1
  rw [← Complex.inv_eq_conj ha, mul_inv_cancel₀ hn]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial
lemma star_real_cast (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
/-- Two points of the family on the same nonzero centered circle differ by
one of the 2m root rotations. No normalization of alpha is needed. -/
theorem family_equal_norm_ratio_root {m : ℕ} {α z w : ℂ}
    (ha : α ≠ star α) (hz : z ∈ extremalCurve m α) (hw : w ∈ extremalCurve m α)
    (hn : ‖z‖ = ‖w‖) (hw0 : w ≠ 0) : (z / w) ^ (2 * m) = 1 := by
  let b : ℂ := (‖w‖ : ℂ) ^ 2 + α
  have hb : b ≠ 0 := by
    intro h
    have hs := congrArg star h
    simp only [b, star_add, star_pow, star_real_cast, star_zero] at hs
    apply ha
    dsimp [b] at h
    linear_combination h - hs
  have hzre : (z ^ m * b).re = 0 := by
    change (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)).re = 0 at hz
    simpa [b, hn] using hz
  have hwre : (w ^ m * b).re = 0 := hw
  have he : (z / w) ^ m = (z ^ m * b) / (w ^ m * b) := by
    rw [div_pow]
    field_simp
  have him : ((z / w) ^ m).im = 0 := by
    rw [he, Complex.div_im, hzre, hwre]
    simp
  have hnorm : ‖(z / w) ^ m‖ = 1 := by
    simp [norm_pow, hn, norm_ne_zero_iff.mpr hw0]
  have hs : star ((z / w) ^ m) = (z / w) ^ m := Complex.conj_eq_iff_im.mpr him
  have hmul := mul_star_eq_one_of_norm hnorm
  rw [hs] at hmul
  calc
    (z / w) ^ (2 * m) = (z / w) ^ m * (z / w) ^ m := by rw [← pow_add]; congr 1; omega
    _ = 1 := hmul
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
/-- The circle section is a single free orbit of the root rotations. -/
def familyCircleRootEquiv {m : ℕ} [NeZero (2 * m)] (hm : 0 < m) {α w : ℂ}
    (ha : α ≠ star α) (hw : w ∈ extremalCurve m α) (hw0 : w ≠ 0) :
    rootsOfUnity (2 * m) ℂ ≃ {z : ℂ // z ∈ extremalCurve m α ∧ ‖z‖ = ‖w‖} :=
  Equiv.ofBijective
    (fun u =>
      have hs := family_root_symmetry hm ((mem_rootsOfUnity' _ _).mp u.property) α
      ⟨(u.val : ℂ) * w, by
        constructor
        · rw [← family_locus_eq] at hw ⊢
          simpa only [add_zero] using (hs.2 w).mpr hw
        · rw [norm_mul, hs.1, one_mul]⟩)
    ⟨by
        intro u v h
        apply rootsOfUnity.coe_injective
        exact mul_right_cancel₀ hw0 (congrArg Subtype.val h),
      by
        intro z
        have hr := family_equal_norm_ratio_root ha z.property.1 hw z.property.2 hw0
        refine ⟨rootsOfUnity.mkOfPowEq (z.val / w) hr, ?_⟩
        apply Subtype.ext
        exact div_mul_cancel₀ z.val hw0⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section
/-- Every positive-radius centered circle meets the family in exactly 2m points. -/
theorem family_circle_section_card {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) {r : ℝ} (hr : 0 < r) :
    Nat.card {z : ℂ // z ∈ extremalCurve m α ∧ ‖z‖ = r} = 2 * m := by
  let : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨w, hw, hwr⟩ := family_point_of_norm hm ha hr.le
  rw [family_locus_eq] at hw
  have hw0 : w ≠ 0 := by intro h; simp [h] at hwr; linarith
  rw [← hwr, ← Nat.card_congr (familyCircleRootEquiv hm ha hw hw0),
    Complex.card_rootsOfUnity]
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
theorem solution {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) {r : ℝ} (hr : 0 < r) :
    Nat.card ↥(extremalCurve m α ∩ Metric.sphere (0 : ℂ) r) = 2 * m := by
  change Nat.card {z : ℂ // z ∈ extremalCurve m α ∧ dist z 0 = r} = _
  simpa only [dist_zero_right] using
    family_circle_section_card hm ha hr
end

#print axioms solution
