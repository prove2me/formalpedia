-- Prove2me | solution 1 for Formalism.SA.P.trace_pow_restrict_maxGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:37.130595+00:00
-- url     : https://prove2.me/submissions/63834078-b9b2-4c7a-addd-7e0e0fe27981

import Definitions.Def_Formalism_LatticeRigidity_StatementD
import Mathlib
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open Matrix Polynomial
open scoped ComplexOrder
variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
namespace Formalism.SA.P
theorem _root_.solution (f : Module.End K V) (μ : K) (j : ℕ) :
    LinearMap.trace K _ ((f ^ j).restrict
        (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ)) =
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  have h1 : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  have hpow : ∀ m : ℕ, ∀ z : f.maxGenEigenspace μ,
      (((f.restrict h1) ^ m) z : V) = (f ^ m) z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      first
      | rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      | rw [pow_succ', LinearMap.mul_apply, pow_succ', LinearMap.mul_apply, ← ih]
      rfl
  have hg : (f ^ j).restrict
      (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ) =
      (f.restrict h1) ^ j :=
    LinearMap.ext fun z => Subtype.ext (by rw [hpow]; rfl)
  rw [hg]
  have hxy : IsNilpotent (f.restrict h1 -
      algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
    convert Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ using 1
    refine LinearMap.ext fun z => Subtype.ext ?_
    first
    | rfl
    | simp [LinearMap.restrict_apply]
    | simp
  generalize f.restrict h1 = x at hxy ⊢
  have hc : Commute x (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) :=
    (Algebra.commutes μ x).symm
  have hnil : IsNilpotent
      (x ^ j - (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) := by
    rw [← hc.geom_sum₂_mul]
    have hcomm : Commute (∑ i ∈ Finset.range j, x ^ i *
        (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ (j - 1 - i))
        (x - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
      refine Commute.sub_right ?_ ?_
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
        | exact Commute.sum_left fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
        | exact Commute.sum_left fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
    first
    | exact hcomm.isNilpotent_mul_left hxy
    | exact hcomm.isNilpotent_mul_right hxy
    | exact hcomm.symm.isNilpotent_mul_left hxy
    | exact hcomm.symm.isNilpotent_mul_right hxy
  have h0 : LinearMap.trace K _ (x ^ j -
      (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) = 0 := by
    first
    | exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    | exact IsNilpotent.eq_zero (LinearMap.isNilpotent_trace_of_isNilpotent hnil)
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, ← map_pow (algebraMap K (Module.End K (f.maxGenEigenspace μ))),
    Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]
end Formalism.SA.P
