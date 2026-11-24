-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.ht_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:28.311663+00:00
-- url     : https://prove2.me/submissions/330ef281-6c3d-4c07-a74e-bd6ae01fcd75

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_fg_of_le
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_pos
import Theorems.Thm_Formalism_HN_height_gram_determinant


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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {M N : Submodule (𝓞 K) V} (hM : M.FG) (hNM : N ≤ M)
    (hrk : rkK N = rkK M) :
    ht b X N = ht b X M * (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hN : N.FG := fg_of_le hM hNM
  obtain ⟨s, hsN, hspan, hli⟩ := exists_linearIndependent K (N : Set V)
  have hfin : s.Finite := hli.setFinite
  let _ : Fintype s := hfin.fintype
  let e : Fin (Fintype.card s) → V := fun i => ((Fintype.equivFin s).symm i : V)
  have he : LinearIndependent K e := hli.comp _ (Fintype.equivFin s).symm.injective
  have hrange : Set.range e = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin s).symm i).2
    · intro hx; exact ⟨Fintype.equivFin s ⟨x, hx⟩, by simp [e]⟩
  have hEN : Submodule.span (𝓞 K) (Set.range e) ≤ N := by
    rw [hrange]; exact Submodule.span_le.2 hsN
  have hrkN : rkK N = Fintype.card s := by
    have h0 : Submodule.span K (N : Set V) = Submodule.span K (Set.range e) := by
      rw [hrange, hspan]
    unfold rkK
    rw [h0, finrank_span_eq_card he, Fintype.card_fin]
  obtain ⟨-, hG⟩ := height_gram_determinant K V ι b X hX _ e he
  have h1 := hG N hN hEN hrkN
  have h2 := hG M hM (hEN.trans hNM) (hrk ▸ hrkN)
  have hE : 0 < ht b X (Submodule.span (𝓞 K) (Set.range e)) :=
    ht_pos b X hX (Submodule.fg_span (Set.finite_range e))
  have h3 := AddSubgroup.relIndex_mul_relIndex
    (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup N.toAddSubgroup M.toAddSubgroup
    ((Submodule.toAddSubgroup_le _ _).2 hEN) ((Submodule.toAddSubgroup_le _ _).2 hNM)
  rw [← h3, Nat.cast_mul] at h2
  have ha : ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex N.toAddSubgroup : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact hE.ne h1
  have h4 : ht b X N * ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex
      N.toAddSubgroup : ℝ) = (ht b X M * (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ)) *
      ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex N.toAddSubgroup : ℝ) := by
    rw [h1, ← h2]; ring
  exact mul_right_cancel₀ ha h4
end Formalism.LFunctionChainParameters.slopeLatticeData
