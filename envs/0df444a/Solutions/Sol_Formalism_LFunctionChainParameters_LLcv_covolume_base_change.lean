-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.covolume_base_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:28.646074+00:00
-- url     : https://prove2.me/submissions/c82a5fb3-3da3-44b9-b486-6475ff2e6711

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_gram_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_covolume_basis_free
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_det_gramPl_baseChange
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_span_baseChange
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_linInd_baseChange
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq


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
theorem _root_.solution : LcvBaseChange := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e g M he hg hM hM0 hsp
  have hd : g.det ≠ 0 := hg.ne_zero
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
    rw [sizeMu_finrank_eq K]; push_cast; ring
  have hf : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  have hprod : ∏ v : InfinitePlace K, v g.det ^ 2 = |((Algebra.norm ℚ g.det : ℚ) : ℝ)| := by
    have h := InfinitePlace.prod_eq_abs_norm g.det
    rw [← Rat.cast_abs, ← h]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2
      (IsTotallyComplex.isComplex v))]
  have hinf : lcvInf b X (fun a => ∑ c, g c a • e c) = lcvInf b X e +
      2 / (Module.finrank ℚ K : ℝ) * Real.log |((Algebra.norm ℚ g.det : ℚ) : ℝ)| := by
    unfold lcvInf
    have h1 : ∀ v : InfinitePlace K,
        Real.log (gramPl b X v (fun a => ∑ c, g c a • e c)).det.re =
          Real.log (v g.det ^ 2) + Real.log (gramPl b X v e).det.re := by
      intro v
      obtain ⟨hp, him⟩ := gram_pos b X hX e he v
      rw [det_gramPl_baseChange b X v e g him, Real.log_mul _ hp.ne']
      exact pow_ne_zero _ ((map_ne_zero v).2 hd)
    simp only [h1]
    rw [Finset.sum_add_distrib, ← Real.log_prod (fun v _ =>
      pow_ne_zero _ ((map_ne_zero v).2 hd)), hprod, hn]
    field_simp
    ring
  refine ⟨hinf, ?_⟩
  have hfree := covolume_basis_free K V ι b X hX j j e (fun a => ∑ c, g c a • e c) M he
    (linInd_baseChange e he g hg) hM hM0 hsp (by rw [span_baseChange e g hg, hsp])
  unfold lcv at hfree
  linarith
end Formalism.LFunctionChainParameters.LLcv
