-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.twistedIsRealOrderLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:13.32984+00:00
-- url     : https://prove2.me/submissions/8f622826-11cc-4092-82e9-2112974eb6d3

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_mem_twLat
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_conj_real
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_smul_mem_FI
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_exists_nat_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x5
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.TwIsFLattice := by
  intro E _ _ _ A B s hB hBA hconj
  refine ⟨fun a t ht => ?_, fun t => ?_⟩
  · rw [mem_twLat] at ht ⊢
    refine ⟨smul_mem_FI E A a t ht.1, ?_⟩
    have := smul_mem_FI E B a _ ht.2
    rw [map_mul, conj_real]
    convert this using 1
    ring
  · obtain ⟨n, hn, hmem⟩ := exists_nat_mul_mem E B hB t
    refine ⟨n, hn, ?_⟩
    rw [mem_twLat]
    refine ⟨hBA hmem, ?_⟩
    have h1 : complexConj E ((n : E) * t) ∈ B := hconj _ hmem
    have h2 : (-1 : E) ^ s * complexConj E ((n : E) * t) ∈ B := by
      rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
      · simpa using h1
      · rw [neg_one_mul]; exact B.coeToSubmodule.neg_mem h1
    exact B.coeToSubmodule.sub_mem hmem h2
end Formalism.FourierDecayAlt.P
