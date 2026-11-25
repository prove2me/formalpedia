-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.slope_via_lengths_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:30.797723+00:00
-- url     : https://prove2.me/submissions/1a756120-5657-49f1-b142-48b92a9c33e0

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealPow_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_slope_formula
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_slope_via_lengths
import Theorems.Thm_Formalism_HN_DualPolygon_twist_index
import Theorems.Thm_Formalism_HN_DualPolygon_twist_span_smul


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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (τ : FinPl K →₀ ℤ) (M : Submodule (𝓞 K) V) (hM : M.FG)
    (hM0 : M ≠ ⊥) (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    ∑ᶠ w : FinPl K, 2 * ell w * (((lenAt w (idealSmul ((idealPow τ :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M)
      (J • idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
        Submodule (𝓞 K) K) M)).toNat : ℝ) / (rkK M : ℝ)) =
      2 * Real.log (Ideal.absNorm J : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hτ := idealPow_ne_zero τ
  set M1 := idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) M with hM1
  have hM1fg : M1.FG := idealSmul_fg _ hM
  have hM1rk : rkK M1 = rkK M := rkK_idealSmul hτ M
  have hrk : rkK (J • M1) = rkK M := by
    rw [← hM1rk]; unfold rkK; rw [Formalism.HN.DualPolygon.twist_span_smul M1 J hJ]
  have hd : (rkK M : ℝ) ≠ 0 := by exact_mod_cast (rkK_pos hM0).ne'
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  have h1 := (slope_formula K V ι b X hX 0 τ M (J • M1) hM hM0 Submodule.smul_le_right hrk).2
  have h2 := (slope_via_lengths K V ι b X hX 0 τ M (J • M1)
    (fun w => ((lenAt w M1 (J • M1)).toNat : ℝ) / (rkK M : ℝ)) hM hM0 Submodule.smul_le_right hrk
    (fun w => by field_simp; rfl)).2.2.2
  rw [← hM1] at h1
  rw [h1, Formalism.HN.DualPolygon.twist_index M1 hM1fg J hJ] at h2
  have h3 : finrank K (Submodule.span K (M1 : Set V)) = rkK M := hM1rk
  rw [h3, Nat.cast_pow, Real.log_pow] at h2
  have h4 : 2 * ((rkK M : ℝ) * Real.log (Ideal.absNorm J : ℝ)) /
      ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) =
      2 * Real.log (Ideal.absNorm J : ℝ) / (Module.finrank ℚ K : ℝ) := by
    field_simp
  rw [h4] at h2
  linarith
end Formalism.LFunctionChainParameters.slopeLatticeData
