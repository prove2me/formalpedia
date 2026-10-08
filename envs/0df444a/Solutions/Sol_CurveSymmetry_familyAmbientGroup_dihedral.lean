-- Prove2me | solution 1 for CurveSymmetry.familyAmbientGroup_dihedral
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T13:05:49.340225+00:00
-- url     : https://prove2.me/submissions/160880b8-b85c-4938-b05b-dea713c2a381

-- Solution generated from lean/FamilyDihedral.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_04_ProjectiveClosure
import Theorems.Thm_CurveSymmetry_family_mobius_self_filter
import Theorems.Thm_CurveSymmetry_family_sphere_dilation_filter
import Theorems.Thm_CurveSymmetry_family_sphere_inversion_filter
import Theorems.Thm_CurveSymmetry_mobius_antidiagonal_action
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
import Mathlib.GroupTheory.SpecificGroups.Dihedral
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
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma mobius_finite_formula (g : MobiusMatrix) (z : ℂ) :
    g • (z : Sphere) = if g 1 0 * z + g 1 1 = 0 then ∞
      else ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) :=
  OnePoint.smul_some_eq_ite
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint
lemma mobius_infinity_formula (g : MobiusMatrix) :
    g • (∞ : Sphere) = if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ) :=
  OnePoint.smul_infty_eq_ite g
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
lemma mobius_diagonal_action (g : MobiusMatrix) (hb : g 0 1 = 0) (hc : g 1 0 = 0) :
    g 0 0 / g 1 1 ≠ 0 ∧ ∀ p : Sphere, g • p = sphereDilation (g 0 0 / g 1 1) p := by
  have hn := g.det_ne_zero
  simp only [Matrix.det_fin_two, hb, hc, zero_mul, sub_zero, ne_eq, mul_eq_zero, not_or] at hn
  refine ⟨div_ne_zero hn.1 hn.2, ?_⟩
  intro p
  cases p using OnePoint.rec with
  | infty => simp [mobius_infinity_formula, hc, sphereDilation]
  | coe z =>
    simp [mobius_finite_formula, hb, hc, hn.2, sphereDilation, div_eq_mul_inv,
      mul_comm, mul_assoc]
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint
theorem family_sphere_dilation_mem_iff {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0)
    (hroot : c ^ (2 * m) = 1) (p : Sphere) :
    sphereDilation c p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  constructor
  · intro hp
    have hi : (c⁻¹) ^ (2 * m) = 1 := by rw [inv_pow, hroot, inv_one]
    have hback := (family_sphere_dilation_filter hm ha hα (inv_ne_zero hc)).mpr hi
      (sphereDilation c p) hp
    have he : sphereDilation c⁻¹ (sphereDilation c p) = p := by
      cases p using OnePoint.rec <;> simp [sphereDilation, hc]
    rwa [he] at hback
  · exact (family_sphere_dilation_filter hm ha hα hc).mpr hroot p
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint
lemma sphereInversion_involutive {c : ℂ} (hc : c ≠ 0) :
    Function.Involutive (sphereInversion c) := by
  intro p
  cases p using OnePoint.rec with
  | infty => simp [sphereInversion]
  | coe z =>
    by_cases hz : z = 0
    · simp [sphereInversion, hz]
    · simp only [sphereInversion, OnePoint.elim_some, if_neg hz,
        if_neg (div_ne_zero hc hz), OnePoint.coe_eq_coe]
      field_simp
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open MvPolynomial OnePoint
/-- The root condition preserves membership in both directions on the whole
sphere, since inversion exchanges zero and infinity and is an involution. -/
theorem family_sphere_inversion_mem_iff {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : ‖α‖ = 1) (ha : α ≠ star α) (hc : c ≠ 0)
    (hroot : c ^ (2 * m) = star α ^ 2) (p : Sphere) :
    sphereInversion c p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  have hmap := (family_sphere_inversion_filter hm hα ha hc).mpr hroot
  constructor
  · intro hp
    simpa only [sphereInversion_involutive hc p] using hmap (sphereInversion c p) hp
  · exact hmap p
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem mem_familyAmbientGroup_iff (m : ℕ) (α : ℂ) (f : Equiv.Perm Sphere) :
    f ∈ familyAmbientGroup m α ↔
      (∃ g : MobiusMatrix, ∀ p : Sphere, g • p = f p) ∧
        ∀ p, f p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  constructor
  · rintro ⟨⟨g, hg⟩, hf⟩
    exact ⟨⟨g, fun p => congrArg (fun k : Equiv.Perm Sphere => k p) hg⟩, hf⟩
  · rintro ⟨⟨g, hg⟩, hf⟩
    exact ⟨⟨g, Equiv.ext hg⟩, hf⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereDilationPerm_apply (c : ℂ) (hc : c ≠ 0) (p : Sphere) :
    sphereDilationPerm c hc p = sphereDilation c p := by
  exact (mobius_diagonal_action (dilationMatrix c hc) rfl rfl).2 p |>.trans
    (by simp [dilationMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero])
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereInversionPerm_apply (c : ℂ) (hc : c ≠ 0) (p : Sphere) :
    sphereInversionPerm c hc p = sphereInversion c p := by
  exact (mobius_antidiagonal_action (inversionMatrix c hc) rfl rfl).2 p |>.trans
    (by simp [inversionMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero])
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereDilationPerm_mem {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0) (hr : c ^ (2 * m) = 1) :
    sphereDilationPerm c hc ∈ familyAmbientGroup m α := by
  refine ⟨⟨dilationMatrix c hc, rfl⟩, ?_⟩
  intro p
  rw [sphereDilationPerm_apply]
  exact family_sphere_dilation_mem_iff hm ha hα hc hr p
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereInversionPerm_mem {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0)
    (hr : c ^ (2 * m) = star α ^ 2) :
    sphereInversionPerm c hc ∈ familyAmbientGroup m α := by
  refine ⟨⟨inversionMatrix c hc, rfl⟩, ?_⟩
  intro p
  rw [sphereInversionPerm_apply]
  exact family_sphere_inversion_mem_iff hm hα ha hc hr p
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
/-- The previously proved ambient completeness theorem now classifies the
elements of the independently defined actual transformation group. -/
theorem familyAmbientGroup_normal_forms {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (f : familyAmbientGroup m α) :
    ∃ c : ℂ, ∃ hc : c ≠ 0,
      (c ^ (2 * m) = 1 ∧ f.val = sphereDilationPerm c hc) ∨
      (c ^ (2 * m) = star α ^ 2 ∧ f.val = sphereInversionPerm c hc) := by
  obtain ⟨⟨g, hg⟩, hf⟩ := (mem_familyAmbientGroup_iff m α f.val).mp f.property
  have hi : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α := by
    intro p hp
    rw [hg]
    exact (hf p).mpr hp
  obtain ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ := (family_mobius_self_filter hm ha hα g).mp hi
  · refine ⟨c, hc, Or.inl ⟨hr, ?_⟩⟩
    ext p
    rw [sphereDilationPerm_apply, ← hg, he]
  · refine ⟨c, hc, Or.inr ⟨hr, ?_⟩⟩
    ext p
    rw [sphereInversionPerm_apply, ← hg, he]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereDilationPerm_injective {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : sphereDilationPerm a ha = sphereDilationPerm b hb) : a = b := by
  have he := congrArg (fun f : Equiv.Perm Sphere => f ((1 : ℂ) : Sphere)) h
  simpa [sphereDilationPerm_apply, sphereDilation] using he
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereInversionPerm_injective {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : sphereInversionPerm a ha = sphereInversionPerm b hb) : a = b := by
  have he := congrArg (fun f : Equiv.Perm Sphere => f ((1 : ℂ) : Sphere)) h
  simpa [sphereInversionPerm_apply, sphereInversion] using he
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereDilationPerm_ne_inversion (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereDilationPerm a ha ≠ sphereInversionPerm b hb := by
  intro h
  have he := congrArg (fun f : Equiv.Perm Sphere => f ((0 : ℂ) : Sphere)) h
  simp [sphereDilationPerm_apply, sphereInversionPerm_apply, sphereDilation, sphereInversion]
    at he
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereDilationPerm_mul (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereDilationPerm a ha * sphereDilationPerm b hb =
      sphereDilationPerm (a * b) (mul_ne_zero ha hb) := by
  ext p
  cases p using OnePoint.rec <;>
    simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply, sphereDilation, mul_assoc]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereDilationPerm_mul_inversion (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereDilationPerm a ha * sphereInversionPerm b hb =
      sphereInversionPerm (a * b) (mul_ne_zero ha hb) := by
  ext p
  cases p using OnePoint.rec with
  | infty => simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply,
      sphereInversionPerm_apply, sphereDilation, sphereInversion]
  | coe z =>
    by_cases hz : z = 0 <;>
      simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply, sphereInversionPerm_apply,
        sphereDilation, sphereInversion, hz, mul_div_assoc]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereInversionPerm_mul_dilation (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereInversionPerm a ha * sphereDilationPerm b hb =
      sphereInversionPerm (a / b) (div_ne_zero ha hb) := by
  ext p
  cases p using OnePoint.rec with
  | infty => simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply,
      sphereInversionPerm_apply, sphereDilation, sphereInversion]
  | coe z =>
    by_cases hz : z = 0 <;>
      simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply, sphereInversionPerm_apply,
        sphereDilation, sphereInversion, hz, hb, div_mul_eq_div_div]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem sphereInversionPerm_mul (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereInversionPerm a ha * sphereInversionPerm b hb =
      sphereDilationPerm (a / b) (div_ne_zero ha hb) := by
  ext p
  cases p using OnePoint.rec with
  | infty => simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply,
      sphereInversionPerm_apply, sphereDilation, sphereInversion]
  | coe z =>
    by_cases hz : z = 0 <;>
      simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply, sphereInversionPerm_apply,
        sphereDilation, sphereInversion, hz, hb, div_div_eq_mul_div, div_mul_eq_mul_div]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem rootCharacter_pow (n : ℕ) [NeZero n] (i : ZMod n) :
    rootCharacter n i ^ n = 1 :=
  (mem_rootsOfUnity' _ _).mp (complexRootEquiv n (Multiplicative.ofAdd i)).property
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem rootCharacter_add (n : ℕ) [NeZero n] (i j : ZMod n) :
    rootCharacter n (i + j) = rootCharacter n i * rootCharacter n j := by
  exact congrArg (fun u : rootsOfUnity n ℂ => (u.val : ℂ))
    ((complexRootEquiv n).map_mul (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem rootCharacter_sub (n : ℕ) [NeZero n] (i j : ZMod n) :
    rootCharacter n (i - j) = rootCharacter n i / rootCharacter n j := by
  simp [rootCharacter]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem rootCharacter_injective (n : ℕ) [NeZero n] :
    Function.Injective (rootCharacter n) := by
  intro i j h
  have he : complexRootEquiv n (Multiplicative.ofAdd i) =
      complexRootEquiv n (Multiplicative.ofAdd j) := rootsOfUnity.coe_injective h
  exact (complexRootEquiv n).injective he
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem rootCharacter_surjective (n : ℕ) [NeZero n] {c : ℂ} (hc : c ^ n = 1) :
    ∃ i : ZMod n, rootCharacter n i = c := by
  obtain ⟨i, hi⟩ := (complexRootEquiv n).surjective (rootsOfUnity.mkOfPowEq c hc)
  exact ⟨Multiplicative.toAdd i, congrArg (fun u : rootsOfUnity n ℂ => (u.val : ℂ)) hi⟩
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem dihedralSphereMap_mul (n : ℕ) [NeZero n] (b : ℂ) (hb : b ≠ 0)
    (x y : DihedralGroup n) :
    dihedralSphereMap n b hb (x * y) =
      dihedralSphereMap n b hb x * dihedralSphereMap n b hb y := by
  cases x with
  | r i =>
    cases y with
    | r j => simp [dihedralSphereMap, sphereDilationPerm_mul, rootCharacter_add]
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, dihedralSphereMap,
        sphereDilationPerm_mul_inversion]
      congr 1
      rw [rootCharacter_sub]
      field_simp
  | sr i =>
    cases y with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, dihedralSphereMap,
        sphereInversionPerm_mul_dilation]
      congr 1
      rw [rootCharacter_add]
      field_simp
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, dihedralSphereMap, sphereInversionPerm_mul]
      congr 1
      rw [rootCharacter_sub]
      field_simp
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem dihedralSphereMap_injective (n : ℕ) [NeZero n] (b : ℂ) (hb : b ≠ 0) :
    Function.Injective (dihedralSphereMap n b hb) := by
  intro x y h
  cases x with
  | r i =>
    cases y with
    | r j =>
      exact congrArg DihedralGroup.r (rootCharacter_injective n
        (sphereDilationPerm_injective _ _ h))
    | sr j => exact False.elim (sphereDilationPerm_ne_inversion _ _ _ _ h)
  | sr i =>
    cases y with
    | r j => exact False.elim (sphereDilationPerm_ne_inversion _ _ _ _ h.symm)
    | sr j =>
      have he := sphereInversionPerm_injective _ _ h
      have hr : rootCharacter n i = rootCharacter n j := by
        have hi := rootCharacter_ne_zero n i
        have hj := rootCharacter_ne_zero n j
        field_simp at he
        exact he.symm
      exact congrArg DihedralGroup.sr (rootCharacter_injective n hr)
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem dihedralSphereMap_mem {m : ℕ} [NeZero (2 * m)] (hm : 0 < m) {α b : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hb : b ≠ 0) (hbr : b ^ (2 * m) = star α ^ 2)
    (x : DihedralGroup (2 * m)) :
    dihedralSphereMap (2 * m) b hb x ∈ familyAmbientGroup m α := by
  cases x with
  | r i => exact sphereDilationPerm_mem hm ha hα _ (rootCharacter_pow _ i)
  | sr i =>
    apply sphereInversionPerm_mem hm ha hα
    simp [div_pow, rootCharacter_pow, hbr]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
theorem dihedralSphereMap_surjective {m : ℕ} [NeZero (2 * m)] (hm : 2 ≤ m)
    {α b : ℂ} (ha : α ≠ star α) (hα : ‖α‖ = 1) (hb : b ≠ 0)
    (hbr : b ^ (2 * m) = star α ^ 2) (f : familyAmbientGroup m α) :
    ∃ x : DihedralGroup (2 * m), dihedralSphereMap (2 * m) b hb x = f.val := by
  obtain ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ := familyAmbientGroup_normal_forms hm ha hα f
  · obtain ⟨i, hi⟩ := rootCharacter_surjective (2 * m) hr
    refine ⟨.r i, ?_⟩
    simp [dihedralSphereMap, ← he, hi]
  · have hbc : (b / c) ^ (2 * m) = 1 := by
      rw [div_pow, hbr, ← hr]
      exact div_self (pow_ne_zero _ hc)
    obtain ⟨i, hi⟩ := rootCharacter_surjective (2 * m) hbc
    refine ⟨.sr i, ?_⟩
    have hi' : b / rootCharacter (2 * m) i = c := by rw [hi]; field_simp
    simp [dihedralSphereMap, hi', he]
end
end CurveSymmetry

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section
/-- Explicit dihedral isomorphism once a base inversion coefficient is chosen. -/
def familyDihedralEquivOfRoot {m : ℕ} [NeZero (2 * m)] (hm : 2 ≤ m)
    {α b : ℂ} (ha : α ≠ star α) (hα : ‖α‖ = 1) (hb : b ≠ 0)
    (hbr : b ^ (2 * m) = star α ^ 2) :
    DihedralGroup (2 * m) ≃* familyAmbientGroup m α :=
  MulEquiv.ofBijective
    ({ toFun := fun x => ⟨dihedralSphereMap (2 * m) b hb x,
          dihedralSphereMap_mem (by omega) ha hα hb hbr x⟩
       map_one' := by
         apply Subtype.ext
         ext p
         change sphereDilationPerm (rootCharacter (2 * m) 0) _ p = p
         cases p using OnePoint.rec <;>
           simp [rootCharacter, sphereDilationPerm_apply, sphereDilation]
       map_mul' := by
         intro x y
         exact Subtype.ext (dihedralSphereMap_mul _ b hb x y) } :
       DihedralGroup (2 * m) →* familyAmbientGroup m α)
    ⟨fun _ _ h => dihedralSphereMap_injective _ b hb (congrArg Subtype.val h),
      fun f => by
        obtain ⟨x, hx⟩ := dihedralSphereMap_surjective hm ha hα hb hbr f
        exact ⟨x, Subtype.ext hx⟩⟩
end
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
open OnePoint
theorem solution {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    Nonempty (DihedralGroup (2 * m) ≃* familyAmbientGroup m α) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (star α ^ 2) (by omega : 0 < 2 * m)
  have ha0 : α ≠ 0 := by intro h; simp [h] at ha
  have hb0 : b ≠ 0 := by
    intro h
    have hz : star α ^ 2 = 0 := by simpa [h, Nat.ne_of_gt (by omega : 0 < 2 * m)] using hb.symm
    exact (pow_ne_zero 2 (star_ne_zero.mpr ha0)) hz
  exact ⟨familyDihedralEquivOfRoot hm ha hα hb0 hb⟩
end

#print axioms solution
