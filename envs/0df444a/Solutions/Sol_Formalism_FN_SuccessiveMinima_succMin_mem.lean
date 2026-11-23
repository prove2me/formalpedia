-- Prove2me | solution 1 for Formalism.FN.SuccessiveMinima.succMin_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:09.03558+00:00
-- url     : https://prove2.me/submissions/b3ce5bcf-4464-4f48-9e38-64903f0dd0dd

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin
import Theorems.Thm_Formalism_FN_SuccessiveMinima_mem_smul_iff_gauge
import Theorems.Thm_Formalism_FN_SuccessiveMinima_finite_lat_inter
import Theorems.Thm_Formalism_FN_SuccessiveMinima_exists_gap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
open Formalism Formalism.FN Formalism.FN.SuccessiveMinima
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (L : Submodule ℤ E) [DiscreteTopology L] {K : Set E}
namespace Formalism.FN.SuccessiveMinima
theorem _root_.solution (hKc : IsCompact K) (hKv : Convex ℝ K) (hK0 : (0 : E) ∈ interior K)
    {i : ℕ} {T : ℝ}
    (hT : 0 ≤ T ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ T • K))) :
    0 ≤ succMin L K i ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ succMin L K i • K)) := by
  classical
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K))}
    with hS
  have hSne : S.Nonempty := ⟨T, hT⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hs0 : 0 ≤ sInf S := le_csInf hSne fun t ht => ht.1
  have hsT : sInf S ≤ T := csInf_le hSbdd hT
  show 0 ≤ sInf S ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ sInf S • K))
  refine ⟨hs0, ?_⟩
  rcases hsT.eq_or_lt with hsT | hsT
  · rw [hsT]; exact hT.2

  set B : Set E := {u | u ∈ (L : Set E) ∩ T • K ∧ sInf S < gauge K u} with hB
  have hBfin : B.Finite :=
    (finite_lat_inter L ((hKc.smul T).isBounded)).subset fun u hu => hu.1
  obtain ⟨m, hsm, hmT, hmB⟩ := exists_gap (gauge K) hBfin hsT fun u hu => hu.2
  obtain ⟨t, htS, htm⟩ := exists_lt_of_csInf_lt hSne hsm
  have hst : sInf S ≤ t := csInf_le hSbdd htS
  refine htS.2.trans (Submodule.finrank_mono (Submodule.span_mono ?_))
  rintro u ⟨huL, hut⟩
  have hgt : gauge K u ≤ t := (mem_smul_iff_gauge hKc hKv hK0 htS.1 u).mp hut
  refine ⟨huL, (mem_smul_iff_gauge hKc hKv hK0 hs0 u).mpr ?_⟩
  by_contra hlt
  push_neg at hlt
  have huT : u ∈ T • K :=
    (mem_smul_iff_gauge hKc hKv hK0 (hs0.trans hsT.le) u).mpr (by linarith)
  have := hmB u ⟨⟨huL, huT⟩, hlt⟩
  linarith
end Formalism.FN.SuccessiveMinima
