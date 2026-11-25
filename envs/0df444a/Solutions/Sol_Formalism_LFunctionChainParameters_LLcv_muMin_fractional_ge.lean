-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.muMin_fractional_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:58.145732+00:00
-- url     : https://prove2.me/submissions/0aa87865-14ee-412c-adbd-863898a5f258

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_deg_fractional
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_rk_fractional
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_slope_characterization
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_fg_of_le
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_cancel_inv
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_inv_cancel
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_mono_right
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ne_bot_of_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥) {I : FI}
    (hI : I ≠ 0) :
    muMin (realize b X) L - Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) /
      (Module.finrank ℚ K : ℝ) ≤ muMin (realize b X) (idealSmul (I : Submodule (𝓞 K) K) L) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)
  have hILfg := idealSmul_fg I hL
  have hlat := (place_lattice_structure K V ι b X hX L hL).1
  have hlatI := (place_lattice_structure K V ι b X hX _ hILfg).1
  rw [(slope_characterization (𝓞 K) V _ (realize b X) _ hlatI hIL0).2.1]
  intro N hN
  have hI' : I⁻¹ ≠ 0 := inv_ne_zero hI
  set N' := idealSmul ((I⁻¹ : FI) : Submodule (𝓞 K) K) N with hN'
  have hN'L : N' ≤ L := by
    have := idealSmul_mono_right ((I⁻¹ : FI) : Submodule (𝓞 K) K) hN
    rwa [idealSmul_inv_cancel hI] at this
  have hNeq : N = idealSmul (I : Submodule (𝓞 K) K) N' := (idealSmul_cancel_inv hI N).symm
  have hN'fg : N'.FG := fg_of_le hL hN'L
  have hch := ((slope_characterization (𝓞 K) V _ (realize b X) L hlat hL0).2.1
    (muMin (realize b X) L)).1 le_rfl N' hN'L
  rw [hNeq, deg_fractional b X hX hL hI, deg_fractional b X hX hN'fg hI,
    rk_fractional b X hX hL hI, rk_fractional b X hX hN'fg hI]
  have r1 := (place_lattice_structure K V ι b X hX L hL).2.1
  have r2 := (place_lattice_structure K V ι b X hX N' hN'fg).2.1
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos' (K := K)).ne'
  have e1 : Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) *
      ((rk (realize b X) L : ℝ) - rk (realize b X) N') =
      ((rkK L : ℝ) - rkK N') * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
    rw [r1, r2]; push_cast; field_simp
  nlinarith [hch, e1]
end Formalism.LFunctionChainParameters.LLcv
