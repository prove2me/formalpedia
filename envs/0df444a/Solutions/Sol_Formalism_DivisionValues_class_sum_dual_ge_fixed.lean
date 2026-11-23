-- Prove2me | solution 1 for Formalism.DivisionValues.class_sum_dual_ge_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:56.550801+00:00
-- url     : https://prove2.me/submissions/e57c21af-15fa-4fd0-ad00-ca915108f0ff

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_mem_valLatF
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open exponent_index_lattice ValuationLatticeField
namespace Formalism.DivisionValues
theorem _root_.solution : ClassSumDualGeF := by
  intro K _ _ _ n H Cl _ V _ _ _ _ pair I g hg hCS Nab Del s hDel DG hdvd y hy
  rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
  intro x hx
  rw [LinearMap.map_smul_of_tower, hCS, Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨k, hk⟩ := hdvd c
  have hp : (s : 𝓞 K) • pair (I x c) (I y c) ∈ (1 : Submodule (𝓞 K) K) := by
    rw [← LinearMap.map_smul_of_tower]
    exact (Formalism.HermitianLatticesTheory.dualBasic_mem_dual pair (Nab c) _).mp (hDel c _ ((mem_valLatF I Del y).mp hy c)) _
      ((mem_valLatF I Nab x).mp hx c)
  have hg0 : (g c : K) ≠ 0 := by exact_mod_cast (hg c).ne'
  have : ((DG * s : ℕ) : 𝓞 K) • ((g c : K)⁻¹ * pair (I x c) (I y c)) =
      (k : 𝓞 K) • (s : 𝓞 K) • pair (I x c) (I y c) := by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_natCast, map_natCast, map_natCast, hk]
    push_cast
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ hp
end Formalism.DivisionValues
