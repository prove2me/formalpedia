-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:49:17.984738+00:00
-- url     : https://prove2.me/submissions/c611a8aa-97ba-41a8-9f97-699bfdcce118

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_gauss
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_pi
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_shift
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_expand
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_ratpos
import Theorems.Thm_Formalism_HermitianLatticesTheory_thetaSummable_coercive_rat
import Theorems.Thm_Formalism_HermitianLatticesTheory_isAddTorsionFree_ringOfIntegers_submodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x))
    (L : Submodule (NumberField.RingOfIntegers K) V) [Submodule.IsLattice K L]
    (γ : V) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun x : L => Complex.exp (Real.pi * Complex.I * τ *
        ((Algebra.trace ℚ K (h (γ + x) (γ + x)) : ℚ) : ℂ))) := by
  classical
  haveI : Module.Finite (NumberField.RingOfIntegers K) L :=
    Module.Finite.iff_fg.mpr (Submodule.IsLattice.fg (A := K))
  haveI : Module.Finite ℤ L := Module.Finite.trans (NumberField.RingOfIntegers K) L
  haveI : IsAddTorsionFree L := isAddTorsionFree_ringOfIntegers_submodule L
  haveI : Module.IsTorsionFree ℤ L := by
    first
    | infer_instance
    | (constructor
       intro r hr a b hab
       have hr0 : r ≠ 0 := hr.ne_zero
       apply Subtype.ext
       have hab' : r • (a : V) = r • (b : V) := by
         have := congrArg (fun y : L => (y : V)) hab
         simpa using this
       have h1 : (r : K) • ((a : V) - (b : V)) = 0 := by
         rw [smul_sub, Int.cast_smul_eq_zsmul K, Int.cast_smul_eq_zsmul K, hab', sub_self]
       have hrK : (r : K) ≠ 0 := Int.cast_ne_zero.mpr hr0
       exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_left hrK))
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  obtain ⟨ι, _, _, ⟨b⟩⟩ : ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι),
      Nonempty (Module.Basis ι ℤ L) :=
    ⟨_, inferInstance, inferInstance, ⟨Module.Free.chooseBasis ℤ L⟩⟩
  let e : ι → V := fun i => ((b i : L) : V)
  let G : Matrix ι ι ℚ := fun i j => Algebra.trace ℚ K (h (e i) (e j))
  have hcoe : ∀ c : ι → ℤ, ((b.equivFun.symm c : L) : V) = ∑ i, c i • e i := by
    intro c
    rw [Module.Basis.equivFun_symm_apply]
    simp [e]
  have hQ : ∀ c : ι → ℤ,
      Algebra.trace ℚ K (h ((b.equivFun.symm c : L) : V) ((b.equivFun.symm c : L) : V)) =
        (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ)) := by
    intro c
    rw [hcoe c, thetaSummable_expand h e c]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, G]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hZ : ∀ c : ι → ℤ, c ≠ 0 → 0 < (fun i => (c i : ℚ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℚ)) := by
    intro c hc
    rw [← hQ c]
    apply hpos
    intro h0
    apply hc
    have h1 : b.equivFun.symm c = 0 := by
      apply Subtype.ext
      simpa using h0
    exact b.equivFun.symm.injective (h1.trans (map_zero _).symm)
  obtain ⟨l, hl, hcoer⟩ := thetaSummable_coercive_rat G (thetaSummable_ratpos G hZ)
  have hP : 0 < Real.pi * τ.im := mul_pos Real.pi_pos hτ
  have hδ : 0 < Real.pi * τ.im * l / 2 := by positivity
  have hre : ∀ q : ℚ, ((Real.pi : ℂ) * Complex.I * τ * (q : ℂ)).re = -(Real.pi * τ.im * (q : ℝ)) := by
    intro q
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ratCast_re, Complex.ratCast_im]
    ring
  have hsum : Summable (fun c : ι → ℤ =>
      Real.exp (Real.pi * τ.im * ((Algebra.trace ℚ K (h γ γ) : ℚ) : ℝ)) *
        ∏ i, Real.exp (-(Real.pi * τ.im * l / 2) * ((c i : ℤ) : ℝ) ^ 2)) :=
    (thetaSummable_pi (fun n => (Real.exp_pos _).le) (thetaSummable_gauss hδ)).mul_left _
  refine (Equiv.summable_iff b.equivFun.symm.toEquiv).mp ?_
  refine Summable.of_norm_bounded hsum (fun c => ?_)
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv]
  rw [Complex.norm_exp, hre, ← Real.exp_sum, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := thetaSummable_shift h hpos γ ((b.equivFun.symm c : L) : V)
  have hs' := (Rat.cast_le (K := ℝ)).mpr hs
  push_cast at hs'
  have hc := hcoer (fun i => (c i : ℚ))
  rw [← hQ c] at hc
  simp only [Rat.cast_intCast] at hc
  rw [← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hs' hP.le, mul_le_mul_of_nonneg_left hc hP.le]
end Formalism.HermitianLatticesTheory
