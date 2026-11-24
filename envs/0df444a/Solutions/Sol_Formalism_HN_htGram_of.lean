-- Prove2me | solution 1 for Formalism.HN.htGram_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:29.758083+00:00
-- url     : https://prove2.me/submissions/62557ef1-bdcf-4b16-8c5a-06a512bd1323

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Theorems.Thm_Formalism_HN_HeightGram_realize_injective
import Theorems.Thm_Formalism_HN_HeightGram_inner_realize
import Theorems.Thm_Formalism_HN_HeightGram_majAt_smul
import Theorems.Thm_Formalism_HN_HeightGram_det_gmat
import Theorems.Thm_Formalism_HN_HeightGram_abs_det_amat
import Theorems.Thm_Formalism_HN_HeightGram_zl_span_eq
import Theorems.Thm_Formalism_HN_HeightGram_linIndep_int
import Theorems.Thm_Formalism_HN_HeightGram_zl_mono
import Theorems.Thm_Formalism_HN_HeightGram_rkK_span
import Theorems.Thm_Formalism_HN_HeightGram_factor_one
import Theorems.Thm_Formalism_HN_HeightGram_norm_det_gramPl
import Theorems.Thm_Formalism_F_covolEqGram
import Theorems.Thm_Formalism_HN_PlaceLattice_linIndep_int
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_injective
import Theorems.Thm_Formalism_HN_PlaceLattice_zl_span_eq
import Theorems.Thm_Formalism_RankSupermodularCovolume_covol_eq_relIndex_mul_covol


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open HeightGram
namespace Formalism.HN
theorem _root_.solution (h1 : PlLat) : HtGram := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX j e he
  classical
  set N := Submodule.span (𝓞 K) (Set.range e) with hNdef
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range e)
  have hρ := realize_injective b X hX
  have hrkN : rkK N = j := rkK_span e he
  have hmain : ht b X N = ∏ v, (gramPl b X v e).det.re := by
    obtain ⟨⟨_, hdisc⟩, _, _⟩ := h1 K V ι b X hX N hNfg
    haveI := hdisc
    have hli := linIndep_int (Formalism.HermitianLatticesTheory.realize b X) hρ e he
    have hsp := zl_span_eq (K := K) (Formalism.HermitianLatticesTheory.realize b X) e
    let bN : Basis _ ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N) :=
      (Basis.span hli).map (LinearEquiv.ofEq _ _ hsp.symm)
    have hbN : ∀ p, (bN p : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) =
        Formalism.HermitianLatticesTheory.realize b X (integralBasis K p.1 • e p.2) := by
      intro p; simp [bN, Basis.span_apply]
    have hcov := Formalism.F.covolEqGram _ (zl (Formalism.HermitianLatticesTheory.realize b X) N) _ bN
    have hgram : Matrix.gram ℝ (fun p => (bN p : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        gmat (lamK K) (fun v => gramPl b X v e) := by
      ext p q
      simp only [Matrix.gram_apply, hbN, inner_realize, gmat, Matrix.of_apply, majAt_smul, gramPl,
        lamK]
    have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K)) =
        Fintype.card (InfinitePlace K × Fin 2) := by
      rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
        IsTotallyComplex.finrank, Fintype.card_prod, Fintype.card_fin,
        InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, mul_comm]
    let eS := Fintype.equivOfCardEq hcard
    have hdet := det_gmat (lamK K) (fun v => gramPl b X v e) eS
    rw [← hgram] at hdet
    have hsq : (Matrix.gram ℝ (fun p => (bN p : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))).det =
        (|(amat (lamK K) eS).det| ^ j * ∏ v, ‖(gramPl b X v e).det‖) ^ 2 := by
      rw [hdet, mul_pow, ← Finset.prod_pow]
      congr 1
      · rw [← pow_mul, mul_comm j 2, pow_mul, pow_mul, sq_abs]
      · exact Finset.prod_congr rfl fun v _ => Complex.normSq_eq_norm_sq _
    have hcov2 : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N) =
        |(amat (lamK K) eS).det| ^ j * ∏ v, ‖(gramPl b X v e).det‖ := by
      rw [hcov, hsq, Real.sqrt_sq (by positivity)]
    have hnPl : nPl K = InfinitePlace.nrComplexPlaces K := by
      unfold nPl
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
        IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have hD : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
    unfold ht
    rw [hcov2, abs_det_amat K eS, hrkN, hnPl]
    simp only [norm_det_gramPl]
    rw [← mul_assoc, factor_one _ _ hD, one_mul]
  refine ⟨hmain, ?_⟩
  intro L hLfg hNL hrkL
  obtain ⟨⟨_, hdiscN⟩, hrkNZ, _⟩ := h1 K V ι b X hX N hNfg
  obtain ⟨⟨_, hdiscL⟩, hrkLZ, _⟩ := h1 K V ι b X hX L hLfg
  haveI := hdiscL
  have hle := zl_mono (Formalism.HermitianLatticesTheory.realize b X) hNL
  have hrkeq : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) N) = Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) L) := by
    have h3 : rk (Formalism.HermitianLatticesTheory.realize b X) N = rk (Formalism.HermitianLatticesTheory.realize b X) L := by
      rw [hrkNZ, hrkLZ, hrkN, hrkL]
    exact h3
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol _ _ hle hrkeq
  have hidx : (zl (Formalism.HermitianLatticesTheory.realize b X) N).toAddSubgroup.relIndex
      (zl (Formalism.HermitianLatticesTheory.realize b X) L).toAddSubgroup = N.toAddSubgroup.relIndex L.toAddSubgroup := by
    simp only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hρ
  unfold ht
  rw [hrkN, hrkL, hcov, hidx]
  ring
end Formalism.HN
