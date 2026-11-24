-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.shear_hypothesis_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:09.412507+00:00
-- url     : https://prove2.me/submissions/587e6b72-6bc4-49e3-8770-9e2cb590c339

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearHypothesisTwo
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_isWH_rename
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_isWH_det
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_mem_H_iff
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_shear_det
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_PrincipalInjectiveCommonRange_shear_rename_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism.NormUnitaryCountingLemmas.PrincipalInjectiveCommonRange
namespace Formalism.NormUnitaryCountingLemmas
theorem _root_.solution : Formalism.NormUnitaryCountingLemmas.H2 := by
  intro R _ N N' hN ν F hF w
  rw [mem_H_iff] at hF ⊢
  obtain ⟨hFw, hFs⟩ := hF
  constructor
  · have := (isWH_rename hN ν F hFw).mul ((isWH_det (R := R) N').pow w)
    convert this using 1
    funext j
    simp [extW]
  · intro i j hij
    rw [map_mul, map_pow, shear_det i j hij.ne, shear_rename_inv hN F hFs i j hij, ← map_pow,
      ← map_mul]
end Formalism.NormUnitaryCountingLemmas
