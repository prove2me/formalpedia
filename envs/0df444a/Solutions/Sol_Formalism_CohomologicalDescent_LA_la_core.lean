-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:53.736643+00:00
-- url     : https://prove2.me/submissions/3a0c7fa2-c1e9-4aeb-8c0b-ed796a3a9718

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_xy_eq
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_coeff_binLat
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_arith
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_arith_conv
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_smul_monLat
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {n : ℕ} (s : Fin n) (d : ℕ) (g : MvPolynomial (Fin 2 × Fin n) ℤ) (hg : g ≠ 0)
    (l e : ℕ) (hl : l.Prime) :
    (∃ m : ℕ, ¬ l ∣ m ∧ ∀ x ∈ (la_monLat ℤ s d).map (LinearMap.mulLeft ℤ g),
      ((m * l ^ e : ℕ) : ℤ) • x ∈ (la_binLat ℤ s d).map (LinearMap.mulLeft ℤ g)) ↔
      Formalism.RankGapBounds.JumpSetsAlt.maxVal l d ≤ e := by
  constructor
  · rintro ⟨m, hm, h⟩
    refine la_arith_conv l d m e hl hm (fun i hi => ?_)
    have hy : la_xy ℤ s (d - i) i ∈ la_monLat ℤ s d :=
      Submodule.subset_span ⟨d - i, i, by omega, rfl⟩
    obtain ⟨z, hz, hgz⟩ := Submodule.mem_map.mp (h _ (Submodule.mem_map_of_mem hy))
    simp only [LinearMap.mulLeft_apply] at hgz
    have hz' : z = ((m * l ^ e : ℕ) : ℤ) • la_xy ℤ s (d - i) i := by
      apply mul_left_cancel₀ hg
      rw [hgz, mul_smul_comm]
    have hc := la_coeff_binLat s d z hz (d - i) i
    rw [hz', la_xy_eq, coeff_smul, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one,
      show d - i + i = d by omega] at hc
    exact_mod_cast hc
  · intro he
    obtain ⟨m, hm, hdiv⟩ := la_arith l d hl
    refine ⟨m, hm, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨((m * l ^ e : ℕ) : ℤ) • y,
      la_smul_monLat s d (m * l ^ e)
        (fun i hi => (hdiv i hi).trans (Nat.mul_dvd_mul_left m (Nat.pow_dvd_pow l he))) y hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    exact mul_smul_comm _ _ _
end Formalism.CohomologicalDescent.LA
