-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.QMinOp.qminOpRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:29:56.789476+00:00
-- url     : https://prove2.me/submissions/cca3db76-944b-4a6e-ba11-a984e7c98533

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatQMinOp
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_QMinOp_qminorWordSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_QMinOp_pTerm_word
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_QMinOp_pTerm_word_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_QMinOp_inLie_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_QMinOp_foldr_max_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_sum_flatMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_sum_map_mul_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_coef
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.QMinOp
open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp
theorem _root_.solution {k r t κ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} (s : Finset ι)
    (a : Fin t → Fin (2 * r + k + 1)) (b : ι → Fin t → Fin (2 * r + k + 1)) (β : ι → B.Mat k r → ℂ)
    (hβ : ∀ j ∈ s, U.IsPolyDeg κ (β j)) (u : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ ∧ B.opOrder Θ = t ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn (t : ℕ∞) UU F → ∀ g ∈ UU, g ∈ B.GV k r →
        B.opApply Θ F g = ∑ j ∈ s, β j g • qminorOp (Q.EH k r) a (b j) u F g := by
  have h := fun j => qminorWordSum k r t a (b j) u
  choose L hL hE using h
  let Θ₁ : B.DiffOp k r Wp Wq :=
    s.toList.flatMap fun j => (L j).map fun cw => pTerm (fun g => β j g * cw.1) cw.2
  let T₀ : B.DTerm k r Wp Wq := pTerm (fun _ => 0) (List.replicate t 0)
  have hT₀ : T₀.word = List.replicate t 0 := pTerm_word (fun X hX => by
    rw [List.eq_of_mem_replicate hX]; exact inLie_zero)
  refine ⟨Θ₁ ++ [T₀], ?_, ?_, ?_⟩
  · intro Tm hTm
    rcases List.mem_append.1 hTm with h1 | h1
    · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at h1
      obtain ⟨j, hj, cw, hcw, rfl⟩ := h1
      refine ⟨(pTerm_word_le _ _).trans (hL j cw hcw).2, fun g => β j g * cw.1, ?_, fun g => rfl, fun g => rfl⟩
      have := Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mul (hβ j hj) (Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const cw.1 0)
      simpa using this
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨by rw [hT₀]; simp, fun _ => 0, Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const 0 κ, fun g => rfl, fun g => rfl⟩
  · unfold B.opOrder
    apply foldr_max_eq
    · intro x hx
      simp only [List.mem_map, List.mem_append, List.mem_singleton] at hx
      obtain ⟨Tm, hTm | rfl, rfl⟩ := hx
      · simp only [Θ₁, List.mem_flatMap, List.mem_map, Finset.mem_toList] at hTm
        obtain ⟨j, _, cw, hcw, rfl⟩ := hTm
        exact (pTerm_word_le _ _).trans (hL j cw hcw).2
      · rw [hT₀]; simp
    · simp only [List.mem_map, List.mem_append, List.mem_singleton]
      exact ⟨T₀, Or.inr rfl, by rw [hT₀]; simp⟩
  · intro UU F hF g hgU hg
    have hT₀a : T₀.coef g (B.Rw T₀.word F g) = 0 := by
      change ((0 : ℂ) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw T₀.word F g) = 0
      simp
    simp only [B.opApply, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hT₀a,
      add_zero, Θ₁]
    rw [sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hE j _ UU F hF g hgU hg, List.map_map, ← sum_map_mul_smul]
    congr 1
    apply List.map_congr_left
    intro cw hcw
    simp only [Function.comp_apply]
    rw [pTerm_word (fun X hX => ((hL j cw hcw).1 X hX).1)]
    change ((β j g * cw.1) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) (B.Rw cw.2 F g) = _
    rfl
end Formalism.FourierDecayAlt.P.CutMP.QMinOp
