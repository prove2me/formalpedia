-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.dualSubset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:43.552818+00:00
-- url     : https://prove2.me/submissions/f8560c64-32bc-4b4a-94ea-7ff6afde473d

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_trace_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dd_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_mem_twLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dual_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_dual_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (h1 : Formalism.FourierDecayAlt.L.DualLatticeInclusion) (h2 : PowConjStable) (h3 : Between) : DualSubset := by
  intro E _ _ _ g ν s hg l hl
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have hd : dd E ≠ 0 := dd_ne_zero E
  rw [mem_twLat]
  refine ⟨dual_le E h1 h2 h3 g ν s hg hl, ?_⟩
  have e0 : idl E g 0 (-(ν + 1)) = FractionalIdeal.dual ℤ ℚ (dd E ^ ν) := by
    rw [dual_pow]; unfold idl; simp
  rw [e0, FractionalIdeal.mem_dual (zpow_ne_zero _ hd)]
  intro i hi
  have hic : complexConj E i ∈ dd E ^ ν := by
    have := h2 E g 0 ν i (by unfold idl; simpa using hi)
    unfold idl at this; simpa using this
  set ε : E := (-1) ^ s with hε
  have hεε : ε * ε = 1 := by rw [hε, ← pow_add, ← two_mul, pow_mul]; simp
  have hεc : complexConj E ε = ε := by rw [hε, map_pow, map_neg, map_one]
  have hεi : ε * complexConj E i ∈ dd E ^ ν := by
    rcases neg_one_pow_eq_or E s with h | h
    · rw [hε, h, one_mul]; exact hic
    · rw [hε, h, neg_one_mul]; exact (dd E ^ ν : FI E).coeToSubmodule.neg_mem hic
  have ht : (g : E) * (i + ε * complexConj E i) ∈ perLat E g ν s := by
    unfold perLat
    rw [mem_twLat]
    constructor
    · unfold idl
      rw [mul_comm (dd E ^ ν), FractionalIdeal.mem_singleton_mul]
      exact ⟨_, (dd E ^ ν : FI E).coeToSubmodule.add_mem hi hεi, by rw [zpow_one]⟩
    · have : (g : E) * (i + ε * complexConj E i)
          - (-1) ^ s * complexConj E ((g : E) * (i + ε * complexConj E i)) = 0 := by
        rw [← hε, map_mul, map_add, map_mul, hεc, complexConj_apply_apply, map_natCast]
        linear_combination (-(g : E) * i) * hεε
      rw [this]; exact (idl E g 2 ν).coeToSubmodule.zero_mem
  have := hl _ ht
  rw [Algebra.traceForm_apply]
  have e1 : l * ((g : E) * (i + ε * complexConj E i)) / g = l * i + ε * (l * complexConj E i) := by
    field_simp
  have e2 : Algebra.trace ℚ E (ε * (l * complexConj E i))
      = Algebra.trace ℚ E (ε * complexConj E l * i) := by
    rw [← trace_conj]
    congr 1
    rw [map_mul, map_mul, hεc, complexConj_apply_apply]; ring
  rw [e1, map_add, e2, ← map_add] at this
  convert this using 2
  rw [pow_succ, ← hε]; ring
end Formalism.FourierDecayAlt.P.S6x2
