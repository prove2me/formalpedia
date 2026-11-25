-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.log_covolume_slope_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:49:04.780059+00:00
-- url     : https://prove2.me/submissions/9b214d06-335e-40bd-a910-cc91463789ae

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_gram_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_ht_lidx
import Theorems.Thm_Formalism_HN_height_gram_determinant
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_eq_log
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos


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
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution : LcvMu := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e M he hM hM0 hsp
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hrk : rkK M = j := by
    unfold rkK; rw [hsp, finrank_span_eq_card he, Fintype.card_fin]
  have hj : 0 < j := hrk ▸ rkK_pos hM0
  have hE : (Submodule.span (𝓞 K) (Set.range e)).FG := Submodule.fg_span (Set.finite_range e)
  have hsp' : Submodule.span K ((Submodule.span (𝓞 K) (Set.range e) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (M : Set V) := by
    rw [Submodule.span_span_of_tower, hsp]
  obtain ⟨hfin, hlog⟩ := ht_lidx b X hX hE hM hsp'
  refine ⟨hrk, hj, gram_pos b X hX e he, hfin, ?_⟩
  rw [muDef_eq_log b X hX hM hM0, hlog, (height_gram_determinant K V ι b X hX j e he).1,
    Real.log_prod (fun v _ => (gram_pos b X hX e he v).1.ne')]
  unfold lcv lcvInf lcvFin
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
    rw [sizeMu_finrank_eq K]; push_cast; ring
  have hf : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  have hj' : (rkK M : ℝ) ≠ 0 := by rw [hrk]; exact_mod_cast hj.ne'
  have hsum : ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
      (Real.log (Ideal.absNorm p.1 : ℝ) / (Module.finrank ℚ K : ℝ)) *
        (haveI := p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ)) =
      (1 / (Module.finrank ℚ K : ℝ)) * ∑ᶠ p : {p : Ideal (𝓞 K) // p.IsMaximal},
        Real.log (Ideal.absNorm p.1 : ℝ) *
        (haveI := p.2.isPrime; (lidx p.1 (Submodule.span (𝓞 K) (Set.range e)) M : ℝ)) := by
    rw [mul_finsum']
    · refine finsum_congr fun p => ?_
      ring
    · refine hfin.subset fun p hp => ?_
      rw [Function.mem_support] at hp ⊢
      intro h0
      apply hp
      rw [h0]; simp
  rw [hsum, hn]
  field_simp
end Formalism.LFunctionChainParameters.LLcv
