-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fockLatticeProjection_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:53.445356+00:00
-- url     : https://prove2.me/submissions/718b7057-0b68-4338-b158-d88b8a309dbc

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_zero_mem_fockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_add_mem_fockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_smul_mem_fockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_divPow_mem_translateLattice
import Theorems.Thm_Formalism_CountingSumsFrames_zero_mem_translateLattice
import Theorems.Thm_Formalism_CountingSumsFrames_add_mem_translateLattice
import Theorems.Thm_Formalism_CountingSumsFrames_smul_mem_translateLattice
import Theorems.Thm_Formalism_CountingSumsFrames_pow_log_smul_harmonicProj_mem
import Theorems.Thm_Formalism_CountingSumsFrames_pow_log_smul_isotypicProj_mem
import Theorems.Thm_Formalism_CountingSumsFrames_divPow_mem_fockLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : FockProj := by
  intro K _ _ k A B p R g _ hp hR f _ hf
  have h0 := zero_mem_translateLattice (FockLat R) (zero_mem_fockLattice R) g
  have hadd := add_mem_translateLattice (FockLat R) (add_mem_fockLattice R) g
  have hs : ∀ r ∈ R, ∀ f ∈ latOf g (FockLat R), r • f ∈ latOf g (FockLat R) :=
    smul_mem_translateLattice R (FockLat R) (smul_mem_fockLattice R) g
  have hM := divPow_mem_translateLattice (FockLat R) (divPow_mem_fockLattice R) g
  exact ⟨pow_log_smul_harmonicProj_mem R p hp hR _ h0 hadd hs hM A B (A + B + k) le_rfl f hf,
    fun j hj => pow_log_smul_isotypicProj_mem R p hp hR _ h0 hadd hs hM A B j (hj.trans (min_le_left _ _)) f hf⟩
end Formalism.CountingSumsFrames
