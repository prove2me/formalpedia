-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.lcv_nonvacuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:30:11.284525+00:00
-- url     : https://prove2.me/submissions/c3b108fc-e1ac-4871-bf78-1d67cc36ef04

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_covolume_ideal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution :
    letI : StarRing (CyclotomicField 3 ℚ) := starRingOfComm
    0 < lcvFin (K := CyclotomicField 3 ℚ) (V := CyclotomicField 3 ℚ) (fun _ : Fin 1 => 1)
      (idealSmul ((FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 (CyclotomicField 3 ℚ)))
        (2 : CyclotomicField 3 ℚ) : FractionalIdeal (nonZeroDivisors (𝓞 (CyclotomicField 3 ℚ)))
          (CyclotomicField 3 ℚ)) : Submodule (𝓞 (CyclotomicField 3 ℚ)) (CyclotomicField 3 ℚ))
        (Submodule.span (𝓞 (CyclotomicField 3 ℚ)) (Set.range fun _ : Fin 1 => 1))) := by
  let _ : StarRing (CyclotomicField 3 ℚ) := starRingOfComm
  have hcyc : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hTC : IsTotallyComplex (CyclotomicField 3 ℚ) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) (CyclotomicField 3 ℚ) (by norm_num)
  have he : LinearIndependent (CyclotomicField 3 ℚ)
      (fun _ : Fin 1 => (1 : CyclotomicField 3 ℚ)) :=
    LinearIndependent.of_subsingleton 0 one_ne_zero
  have hI : (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 (CyclotomicField 3 ℚ)))
      (2 : CyclotomicField 3 ℚ)) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact two_ne_zero
  rw [covolume_ideal (CyclotomicField 3 ℚ) (CyclotomicField 3 ℚ) Unit
    (Basis.singleton Unit (CyclotomicField 3 ℚ)) 1 _ _ he one_pos hI,
    FractionalIdeal.absNorm_span_singleton]
  have hn : Algebra.norm ℚ (2 : CyclotomicField 3 ℚ) =
      2 ^ Module.finrank ℚ (CyclotomicField 3 ℚ) := by
    have := Algebra.norm_algebraMap (S := CyclotomicField 3 ℚ) (2 : ℚ)
    rwa [map_ofNat] at this
  have hpos : 0 < Module.finrank ℚ (CyclotomicField 3 ℚ) := Module.finrank_pos
  have h1 : (1 : ℝ) < ((|Algebra.norm ℚ (2 : CyclotomicField 3 ℚ)| : ℚ) : ℝ) := by
    rw [hn, abs_of_pos (by positivity)]
    push_cast
    exact one_lt_pow₀ one_lt_two hpos.ne'
  have h2 := Real.log_pos h1
  have h3 : (0 : ℝ) < (Module.finrank ℚ (CyclotomicField 3 ℚ) : ℝ) := by exact_mod_cast hpos
  positivity
end Formalism.LFunctionChainParameters.LLcv
