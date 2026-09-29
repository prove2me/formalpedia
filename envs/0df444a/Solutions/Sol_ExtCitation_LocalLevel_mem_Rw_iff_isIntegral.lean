-- Prove2me | solution 1 for ExtCitation.LocalLevel.mem_Rw_iff_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e2697f63-7191-55b5-a43f-86ee3bff6410

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral

set_option autoImplicit false
open scoped NNReal
open Polynomial

namespace Ws26T4

theorem norm_le_one_iff_isIntegral (p : ℕ) [Fact p.Prime] (x : PadicAlgCl p) :
    ‖x‖ ≤ 1 ↔ IsIntegral ℤ_[p] x := by
  have hxalg : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hnorm : ‖x‖ = spectralValue (minpoly ℚ_[p] x) := by rw [← PadicAlgCl.spectralNorm_eq]; rfl
  constructor
  · intro h
    rw [hnorm, spectralValue_le_one_iff (minpoly.monic hxalg)] at h
    have hlifts : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨(minpoly ℚ_[p] x).coeff n, h n⟩, rfl⟩
    obtain ⟨Q, hQmap, -, hQmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (minpoly.monic hxalg)
    refine ⟨Q, hQmonic, ?_⟩
    have h0 : Polynomial.aeval x Q = 0 := by
      rw [← Polynomial.aeval_map_algebraMap ℚ_[p], hQmap, minpoly.aeval]
    exact h0
  · intro h
    rw [hnorm, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] h,
      spectralValue_le_one_iff ((minpoly.monic h).map _)]
    intro n
    rw [Polynomial.coeff_map]
    exact PadicInt.norm_le_one _

end Ws26T4

open Ws26T4 ExtCitation.LocalLevel in
theorem solution (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (x : Kw) :
    x ∈ Rw q Kw ↔ IsIntegral ℤ_[q] (x : PadicAlgCl q) := by
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def,
    ← Ws26T4.norm_le_one_iff_isIntegral]
  rfl

end S_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral
end P2MW
export P2MW.S_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral (solution)
