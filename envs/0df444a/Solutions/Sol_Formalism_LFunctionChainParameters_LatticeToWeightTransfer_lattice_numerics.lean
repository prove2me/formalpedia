-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.lattice_numerics
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:43:48.13198+00:00
-- url     : https://prove2.me/submissions/42928f78-afd8-42e7-84e4-8bc2795d454d

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_slope_le_max_slope


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer
theorem _root_.solution (u0 : U0) {K Wd κ κ₁ : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup Wd] [Module K Wd] [Module (𝓞 K) Wd] [IsScalarTower (𝓞 K) K Wd]
    [Fintype κ] [DecidableEq κ] [Fintype κ₁] [DecidableEq κ₁]
    {V ι : W u0 → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, Module (𝓞 K) (V i)]
    [∀ i, IsScalarTower (𝓞 K) K (V i)] [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (b' : Basis κ K Wd) (X' : InfinitePlace K → Matrix κ κ ℂ) (cc : Submodule (𝓞 K) Wd)
    (b : ∀ i, Basis (ι i) K (V i)) (X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ)
    (N : ∀ i, Submodule (𝓞 K) (V i)) (B : ∀ i, V i →ₗ[K] Wd)
    (v : InfinitePlace K) (Y : ∀ i, Matrix (ι i) (ι i) ℂ) (Y' : Matrix κ κ ℂ)
    (Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ)
    (hId : LatIdent D u0 b' X' cc b X N)
    (hG : MatrixLatticeEstimates.LatGeom b' X' cc b X N B (D.h u0) v Y Y' Ball (D.del u0))
    (hSide : SideF D u0) :
    MatrixLatticeEstimates.LatNum b' X' cc b X N (D.h u0) (D.s u0) (D.uF u0) (D.HH u0) := by
  obtain ⟨hd, hmuN, hmuMax, hcc, hmin⟩ := hId
  obtain ⟨-, -, -, -, -, s6, s7⟩ := hSide
  have hpos : (0 : ℝ) < ∑ i, (Fintype.card (ι i) : ℝ) := by
    exact_mod_cast hG.2.2.2.2.2.2.2.2.1
  have hs : D.s u0 = (∑ i, (Fintype.card (ι i) : ℝ) * (muDef (b i) (X i) (N i) - D.h u0 i))
      / ∑ i, (Fintype.card (ι i) : ℝ) := by
    unfold Data.s wmean
    simp only [hd, hmuN]
  have hle : ∀ i, muMaxDef (b i) (X i) (N i) - D.h u0 i ≤
      Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) := by
    intro i
    have := Finset.le_sup' (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) (Finset.mem_univ i)
    rw [← hmuMax i]
    exact this
  refine ⟨?_, ?_, ?_, ?_, s7.le⟩
  · rw [hs, div_mul_cancel₀ _ hpos.ne']
  · unfold Data.uF
    rw [sub_nonneg, hs, div_le_iff₀ hpos, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm _ (Fintype.card (ι i) : ℝ)]
    rcases Nat.eq_zero_or_pos (Fintype.card (ι i)) with h0 | h0
    · rw [h0]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 := MatrixLatticeEstimates.slope_le_max_slope (b i) (X i) (hG.2.1 i) (N i) (hG.2.2.2.2.2.2.1 i)
        (hG.2.2.2.2.2.2.2.1 i) h0
      have h2 := hle i
      linarith
  · intro i
    have h2 := hle i
    unfold Data.uF
    linarith
  · rw [← hmin]; exact s6
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
