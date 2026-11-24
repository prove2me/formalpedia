-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.limUnder_of_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.476298+00:00
-- url     : https://prove2.me/submissions/3559bd5c-18dd-42c9-ab65-1092ba2110b3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FirstFamilyOperatorEnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms localValuationFiltration hermitianFormColumns vectorCountBounds
namespace Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
theorem _root_.solution {u : ℕ → ℕ} {q e k₀ : ℕ} (hq : 0 < q)
    (h : ∀ k, k₀ ≤ k → u (k + 1) = q ^ e * u k) {k : ℕ} (hk : k₀ ≤ k) :
    limUnder atTop (fun k : ℕ => (u k : ℝ) / (q : ℝ) ^ (k * e)) = (u k : ℝ) / (q : ℝ) ^ (k * e) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hstep : ∀ j, k₀ ≤ j → (u (j + 1) : ℝ) / (q : ℝ) ^ ((j + 1) * e) =
      (u j : ℝ) / (q : ℝ) ^ (j * e) := by
    intro j hj
    rw [h j hj, Nat.cast_mul, Nat.cast_pow, div_eq_div_iff (pow_ne_zero _ hq') (pow_ne_zero _ hq'),
      add_mul, one_mul, pow_add]
    ring
  have hconst : ∀ j, k₀ ≤ j → (u j : ℝ) / (q : ℝ) ^ (j * e) = (u k₀ : ℝ) / (q : ℝ) ^ (k₀ * e) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [hstep j hj, ih]
  have ht : Tendsto (fun k : ℕ => (u k : ℝ) / (q : ℝ) ^ (k * e)) atTop
      (𝓝 ((u k : ℝ) / (q : ℝ) ^ (k * e))) := by
    rw [hconst k hk]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k₀] with j hj
    exact (hconst j hj).symm
  exact ht.limUnder_eq
end Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd
