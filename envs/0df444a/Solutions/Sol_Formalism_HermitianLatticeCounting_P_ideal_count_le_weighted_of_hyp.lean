-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_count_le_weighted_of_hyp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:29.996784+00:00
-- url     : https://prove2.me/submissions/2a54c732-d816-477f-bd33-9ca2456ac74c

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_count_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : IdealCountLeW' := by
  intro hS hOm E _ _ f y hf
  have h := DualLatticeIndexBis.count_le E (Module.finrank ℚ E) 1 y Module.finrank_pos hOm
    (fun n hn => by
      have h1 := hS E (𝓞 E) n hn
      have hset : {N : Submodule (𝓞 E) (𝓞 E) | N.toAddSubgroup.index = n} =
          {I : Ideal (𝓞 E) | Ideal.absNorm I = n} := by
        ext I
        have e1 : Ideal.absNorm I = (Submodule.toAddSubgroup I).index := by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
        simp only [Set.mem_ofPred_eq, e1]
      rw [hset, Module.finrank_self] at h1
      exact h1)
  rw [hf] at h
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  push_cast
  rfl
end Formalism.HermitianLatticeCounting.P
