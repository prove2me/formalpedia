-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.level_integral_formula_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:48.809177+00:00
-- url     : https://prove2.me/submissions/2eb41e13-1d58-4d23-b251-7ea3dcc86151

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSplitAssocMeasurePreserving
import Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_split_assoc_measurePreserving
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_integrand_split_point
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_product_preserves_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P5_integrable_of_quartic_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P5_ae_complex_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P5_complex_norm_eq_re_of_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P5_level_integrand_aestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P5_sesquilinear_polarization_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P5_top_density_add_left
import Theorems.Thm_Formalism_FourierDecayAlt_P5_top_density_add_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
section B
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
end B
section Main
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)} [SFinite μ]
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}
private lemma act_add_smul_hermitian_curvature (M : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))
    (x y : Ix S → RadSp P.k P.r z z' π π') (a : ℂ) : act M (x + a • y) = act M x + a • act M y := by
  funext b
  simp only [act, Pi.add_apply, Pi.smul_apply, map_add, map_smul, Finset.sum_add_distrib, Finset.smul_sum]
private lemma inK_add_smul_of_inK {Kc : Submodule ℂ (RadSp P.k P.r z z' π π')} {x y : Ix S → RadSp P.k P.r z z' π π'}
    (hx : InK Kc x) (hy : InK Kc y) (a : ℂ) : InK Kc (x + a • y) :=
  fun b => Kc.add_mem (hx b) (Kc.smul_mem a (hy b))
private lemma densNonneg_S_consequence (hN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hS : SliceIn (S := S) P z z' π π' L st K l0) (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w)
    (i : Fin (P.r + 1)) (u : Ix S → RadSp P.k P.r z z' π π') (hu : InK (K i) u) (c : Fin P.r → ℂ)
    (hc : c ∈ OmX P.r) (q : Cf P.r i × Mt P.k P.r) : 0 ≤ levelIntegrand L st w i u u c q := by
  unfold levelIntegrand
  by_cases h0 : ∀ j, q.1 j ≠ 0
  · have hg : glue i c q.1 ∈ OmX P.r := by
      simp only [OmX, Set.mem_setOf_eq]
      intro l
      unfold glue
      split_ifs with h
      · exact h0 _
      · exact hc l
    have hwt : (0 : ℂ) ≤ ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr (Finset.prod_nonneg fun l _ => zpow_nonneg (norm_nonneg _) _)
    exact mul_nonneg hwt (hN w hw _ (level_product_preserves_compact hS w hw i u hu) _ hg _)
  · push_neg at h0
    obtain ⟨j, hj⟩ := h0
    have h1 : (∏ l, ‖q.1 l‖ ^ (-2 : ℤ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, norm_zero]; exact zero_zpow _ (by norm_num))
    rw [h1]
    simp
end Main
end Formalism.FourierDecayAlt.P5
end
end

set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)} [SFinite μ]
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (hN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hS : SliceIn (S := S) P z z' π π' L st K l0) (hD : StepDens (S := S) P z z' π π' μ L st K l0)
    (hM : TopDensMeas S P z z' π π' μ L st K) (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w)
    (lf : Fin P.r) (ih : LevelIntegralFormula P z z' π π' μ L st K w lf.succ) :
    LevelIntegralFormula P z z' π π' μ L st K w lf.castSucc := by
  intro x y hx hy c hc
  have hE := coordinate_split_assoc_measurePreserving lf (β := Mt P.k P.r) μ
  have hEs := MeasurePreserving.symm (coordinateSplitAssoc lf) hE
  have hupd : ∀ t : ℂ, t ≠ 0 → Function.update c lf t ∈ OmX P.r := by
    intro t ht
    simp only [OmX, Set.mem_setOf_eq] at hc ⊢
    intro j
    by_cases hj : j = lf
    · subst hj
      simp [ht]
    · rw [Function.update_of_ne hj]
      exact hc j
  have hSl : ∀ u, InK (K lf.castSucc) u → InK (K lf.succ) (act (bTl L lf w) u) :=
    fun u hu => hS w hw lf u hu
  have hmeasF : ∀ u v, InK (K lf.castSucc) u → InK (K lf.castSucc) v →
      AEStronglyMeasurable (levelIntegrand L st w lf.castSucc u v c) (volume.prod μ) := fun u v hu hv =>
    level_integrand_aestronglyMeasurable hM w _ _ (level_product_preserves_compact hS w hw _ u hu) (level_product_preserves_compact hS w hw _ v hv) lf.castSucc c
  have hdiag : ∀ u, InK (K lf.castSucc) u → Integrable (levelIntegrand L st w lf.castSucc u u c) (volume.prod μ) := by
    intro u hu
    obtain ⟨φ, hφc, hφe, ⟨C, hC⟩, -⟩ := hD w hw lf u u hu hu c hc
    have hφi := integrable_of_quartic_decay φ hφc C hC
    rw [← hEs.integrable_comp_emb (coordinateSplitAssoc lf).symm.measurableEmbedding]
    refine (integrable_prod_iff ((hmeasF u u hu hu).comp_measurePreserving hEs)).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_complex_ne_zero] with t ht
      simp only [Function.comp_apply, level_integrand_split_point]
      exact ((ih _ _ (hSl u hu) (hSl u hu) _ (hupd t ht)).1).const_mul _
    · refine hφi.re.congr ?_
      filter_upwards [ae_complex_ne_zero] with t ht
      have hF := ih _ _ (hSl u hu) (hSl u hu) _ (hupd t ht)
      have hnn := fun q => densNonneg_S_consequence hN hS w hw lf.succ _ (hSl u hu) _ (hupd t ht) q
      have ha : (0 : ℝ) ≤ ‖t‖ ^ (-2 : ℤ) := zpow_nonneg (norm_nonneg _) _
      have hre : ∫ q, (levelIntegrand L st w lf.succ (act (bTl L lf w) u) (act (bTl L lf w) u)
          (Function.update c lf t) q).re ∂(volume.prod μ) =
          (∫ q, levelIntegrand L st w lf.succ (act (bTl L lf w) u) (act (bTl L lf w) u)
          (Function.update c lf t) q ∂(volume.prod μ)).re := by
        have := integral_re hF.1
        simpa using this
      calc RCLike.re (φ t) = (ph L st μ lf w u u c t).re := by rw [hφe t ht]; rfl
        _ = ‖t‖ ^ (-2 : ℤ) * (∫ q, levelIntegrand L st w lf.succ (act (bTl L lf w) u) (act (bTl L lf w) u)
              (Function.update c lf t) q ∂(volume.prod μ)).re := by
            rw [ph, hF.2, Complex.re_ofReal_mul]
        _ = ∫ q, ‖t‖ ^ (-2 : ℤ) * (levelIntegrand L st w lf.succ (act (bTl L lf w) u) (act (bTl L lf w) u)
              (Function.update c lf t) q).re ∂(volume.prod μ) := by
            rw [integral_const_mul, hre]
        _ = ∫ q, ‖(levelIntegrand L st w lf.castSucc u u c ∘ (coordinateSplitAssoc lf).symm) (t, q)‖ ∂(volume.prod μ) := by
            congr 1
            funext q
            rw [Function.comp_apply, level_integrand_split_point, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha,
              complex_norm_eq_re_of_nonneg (hnn q)]
  have hint : ∀ u v, InK (K lf.castSucc) u → InK (K lf.castSucc) v →
      Integrable (levelIntegrand L st w lf.castSucc u v c) (volume.prod μ) := by
    intro u v hu hv
    have hb := fun s : ℂ => hdiag (u + s • v) (inK_add_smul_of_inK hu hv s)
    refine (((((hb 1).norm.add (hb Complex.I).norm).add (hb (-1)).norm).add (hb (-Complex.I)).norm).div_const
      4).mono' (hmeasF u v hu hv) (Filter.Eventually.of_forall fun q => ?_)
    refine sesquilinear_polarization_norm (fun a b => levelIntegrand L st w lf.castSucc a b c q) (fun a a' b s => ?_)
      (fun a b b' s => ?_) u v
    · simp only [levelIntegrand, act_add_smul_hermitian_curvature, top_density_add_left]
      ring
    · simp only [levelIntegrand, act_add_smul_hermitian_curvature, top_density_add_right]
      ring
  refine ⟨hint x y hx hy, ?_⟩
  obtain ⟨φ, -, hφe, -, hφI⟩ := hD w hw lf x y hx hy c hc
  have hGi : Integrable (fun p => levelIntegrand L st w lf.castSucc x y c ((coordinateSplitAssoc lf).symm p))
      (volume.prod (volume.prod μ)) :=
    (hEs.integrable_comp_emb (coordinateSplitAssoc lf).symm.measurableEmbedding).mpr (hint x y hx hy)
  calc RRform L st μ lf.castSucc w x y c = ∫ t, φ t := hφI.symm
    _ = ∫ t, ∫ q, levelIntegrand L st w lf.castSucc x y c ((coordinateSplitAssoc lf).symm (t, q)) ∂(volume.prod μ) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_complex_ne_zero] with t ht
        rw [hφe t ht, ph, (ih _ _ (hSl x hx) (hSl y hy) _ (hupd t ht)).2]
        simp only [level_integrand_split_point]
        rw [integral_const_mul]
    _ = ∫ p, levelIntegrand L st w lf.castSucc x y c ((coordinateSplitAssoc lf).symm p) ∂(volume.prod (volume.prod μ)) :=
        (integral_prod _ hGi).symm
    _ = _ := hEs.integral_comp' _
end Formalism.FourierDecayAlt.P5
