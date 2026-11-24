-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldlat_linInd_field
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:09.643164+00:00
-- url     : https://prove2.me/submissions/f3bbb8bf-e897-4354-9c72-b2201fbf46f0

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {F K : Type*} [Field F] [Field K] [Algebra F K] {σ ι : Type*}
    {v : ι → MvPolynomial σ F} (hv : LinearIndependent F v) :
    LinearIndependent K (fun i => map (algebraMap F K) (v i)) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (coeff m) hsum
    simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul, coeff_zero] at h1 ⊢
    have h2 := congrArg (fun x => B.repr x j) h1
    simp only [map_sum, map_zero, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero,
      Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this
end Formalism.GradedWeylDivisibility
