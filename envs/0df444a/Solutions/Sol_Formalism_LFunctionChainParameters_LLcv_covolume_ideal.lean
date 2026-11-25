-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.covolume_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:12.851402+00:00
-- url     : https://prove2.me/submissions/bc70b6ba-cf42-4c5e-8256-93658eef0770

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_log_covolume_slope_mu
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_covolume_free_module
import Theorems.Thm_Formalism_HN_HeightGram_rkK_span
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_fractional
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ne_bot_of_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_span_idealSmul
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_slopeLatticeData_finrank_pos__952bcff0eee0


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
theorem _root_.solution : LcvIdeal := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b j e I he hj hI
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  let X : InfinitePlace K → Matrix ι ι ℂ := fun _ => 1
  have hX : ∀ v, IsUnit (X v).det := fun v => by simp [X]
  have hE : (Submodule.span (𝓞 K) (Set.range e)).FG := Submodule.fg_span (Set.finite_range e)
  have hrk := HeightGram.rkK_span (K := K) e he
  have h0 : Submodule.span (𝓞 K) (Set.range e) ≠ ⊥ := ne_bot_of_rkK_pos (by rw [hrk]; exact hj)
  have hI0 : idealSmul (I : Submodule (𝓞 K) K) (Submodule.span (𝓞 K) (Set.range e)) ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI, hrk]; exact hj)
  obtain ⟨hr, -, -, -, h1⟩ := log_covolume_slope_mu K V ι b X hX j e _ he (idealSmul_fg I hE) hI0
    (by rw [span_idealSmul hI, Submodule.span_span_of_tower])
  have h2 := muDef_fractional b X hX hE h0 hI
  have h3 := (covolume_free_module K V ι b X hX j e he hj).2
  rw [h1, h3, hr, lcv] at h2
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos' (K := K)).ne'
  field_simp at h2 ⊢
  linarith
end Formalism.LFunctionChainParameters.LLcv
