-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.topCells_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:03.847873+00:00
-- url     : https://prove2.me/submissions/dd642672-8c5a-4122-a331-f3a262716114

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_taylor_integral
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_zjH_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_psiH
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_zjH
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_Lc_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_norm_psiH
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_wtH_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
private theorem iter_lemma {X Y V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {q : ℕ} {f : Y → V} (hf : ContDiff ℝ q f) (L : V →L[ℝ] V) (T : Y) (ι : X →L[ℝ] Y)
    {m : ℕ} (hm : m ≤ q) (x : X) :
    iteratedFDeriv ℝ m (fun y => L (f (T + ι y))) x =
      L.compContinuousMultilinearMap ((iteratedFDeriv ℝ m f (T + ι x)).compContinuousLinearMap fun _ => ι) := by
  have hm' : ((m : ℕ) : WithTop ℕ∞) ≤ (q : WithTop ℕ∞) := by exact_mod_cast hm
  have h1 : ContDiff ℝ q (fun z => f (T + z)) := hf.comp (contDiff_const.add contDiff_id)
  have h2 : ContDiff ℝ q ((fun z => f (T + z)) ∘ ι) := h1.comp ι.contDiff
  have e1 := L.iteratedFDeriv_comp_left (h2.contDiffAt (x := x)) hm'
  have e2 := ι.iteratedFDeriv_comp_right h1 x hm'
  have e3 := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) m T (ι x)
  calc iteratedFDeriv ℝ m (fun y => L (f (T + ι y))) x
      = L.compContinuousMultilinearMap (iteratedFDeriv ℝ m ((fun z => f (T + z)) ∘ ι) x) := e1
    _ = _ := by rw [e2, e3]
end Formalism.FourierDecayAlt.P.Ux13
end
end

set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
namespace Formalism.FourierDecayAlt.P.Ux13
theorem _root_.solution (hZ : ZjAffine) (hST : SizesTop) (hIT : IntTop) : TopCells := by
  intro p s β σ d hd hs q e he
  haveI i1 : OpensMeasurableSpace (Fin s → Fin p → ℂ) := inferInstance
  haveI i2 : OpensMeasurableSpace (Fin p → Fin s → ℂ) := inferInstance
  haveI i3 : OpensMeasurableSpace (LW σ → ℂ) := inferInstance
  haveI i4 : OpensMeasurableSpace (G.UT p → ℂ) := inferInstance
  haveI i5 : SecondCountableTopology (Fin s → Fin p → ℂ) := inferInstance
  haveI i6 : SecondCountableTopology (Fin p → Fin s → ℂ) := inferInstance
  haveI i7 : SecondCountableTopology (LW σ → ℂ) := inferInstance
  haveI i8 : SecondCountableTopology (G.UT p → ℂ) := inferInstance
  haveI i9 : OpensMeasurableSpace ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) := inferInstance
  haveI i10 : OpensMeasurableSpace ((LW σ → ℂ) × (G.UT p → ℂ)) := inferInstance
  haveI i11 : SecondCountableTopology ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) := inferInstance
  haveI i12 : SecondCountableTopology ((LW σ → ℂ) × (G.UT p → ℂ)) := inferInstance
  haveI : OpensMeasurableSpace (XiH p s σ) := inferInstance
  have hN : (1 : ℝ) ≤ ((p + s : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ p + s)
  have h5N : (0 : ℝ) < 5 * ((p + s : ℕ) : ℝ) := by positivity
  have hepos : ∀ i ≤ q, 0 ≤ e i := by
    intro i hi
    have h1 := he i hi
    have h2 : (0 : ℝ) ≤ 2 * ((p + s : ℕ) : ℝ) ^ 2 := by positivity
    have h3 : 0 < e i / (5 * ((p + s : ℕ) : ℝ)) := by linarith
    exact le_of_lt ((div_pos_iff_of_pos_right h5N).mp h3)
  choose C hC using fun i : ℕ => hST p s σ d hd hs (max (e i) 0) (le_max_right _ _)
  obtain ⟨Tm, hTm⟩ : ∃ Tm : XiH p s σ → G.Mat (p + s), Tm = fun η => Matrix.of.symm (ZjH σ d η 0) :=
    ⟨_, rfl⟩
  have hTc : Continuous Tm := by rw [hTm]; exact continuous_zjH σ d 0
  have hsplit : ∀ (η : XiH p s σ) (CC : G.Mat s),
      (Matrix.of.symm (ZjH σ d η CC) : G.Mat (p + s)) = Tm η + iotaC p s CC := by
    intro η CC
    rw [hTm]
    exact zjH_split hZ σ d η CC
  refine ⟨∑ k ∈ Finset.range (q + 1), ‖iotaC p s‖ ^ k * |C k| *
      ∫ η, wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ), ?_⟩
  intro V _ _ _ Φ0 K hΦ
  unfold DecayAll at hΦ ⊢
  obtain ⟨hcd, hbd⟩ := hΦ
  have hK : 0 ≤ K := by
    have h := hbd 0 (Nat.zero_le _) 0
    have h' := (norm_nonneg _).trans h
    simpa using h'
  have hexp : ∀ m ≤ q, ∀ (η : XiH p s σ) (x : G.Mat s),
      iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x =
        (Lc (psiH β σ η)).compContinuousMultilinearMap
          ((iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s) :=
    fun m hm η x => iter_lemma hcd (Lc (psiH β σ η)) (Tm η) (iotaC p s) hm x
  have hLc : ∀ η : XiH p s σ, ‖(Lc (psiH β σ η) : V →L[ℝ] V)‖ ≤ 1 := by
    intro η
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [Lc_apply, norm_smul, norm_psiH, one_mul]
  have hpt : ∀ m ≤ q, ∀ (η : XiH p s σ) (x : G.Mat s),
      ‖iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x‖ ≤
        ‖iotaC p s‖ ^ m * K * |C m| * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := by
    intro m hm η x
    rw [hexp m hm η x]
    have h1 := ContinuousLinearMap.norm_compContinuousMultilinearMap_le (Lc (psiH β σ η) : V →L[ℝ] V)
      ((iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s)
    have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)) (fun _ : Fin m => iotaC p s)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    have h3 := hbd m hm (Tm η + iotaC p s x)
    have hmx : mx (ZjH σ d η x) = ‖Tm η + iotaC p s x‖ := by
      unfold mx
      rw [hsplit]
    have h4 := hC m η x
    rw [max_eq_left (hepos m hm), hmx] at h4
    have hw := wtH_pos η
    have h5 : (wtH η * (1 + ‖x‖)) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) = wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) :=
      Real.mul_rpow hw.le (by positivity)
    rw [h5] at h4
    have hA : 0 ≤ wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := by positivity
    have hCabs : C m * (wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))) ≤
        |C m| * (wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hA
    have hι : 0 ≤ ‖iotaC p s‖ ^ m := by positivity
    calc _ ≤ ‖(Lc (psiH β σ η) : V →L[ℝ] V)‖ *
          ‖(iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s‖ := h1
      _ ≤ 1 * (‖iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)‖ * ‖iotaC p s‖ ^ m) :=
          mul_le_mul (hLc η) h2 (norm_nonneg _) zero_le_one
      _ ≤ 1 * ((K * (1 + ‖Tm η + iotaC p s x‖) ^ (-e m)) * ‖iotaC p s‖ ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_one
          exact mul_le_mul_of_nonneg_right h3 hι
      _ ≤ 1 * ((K * (|C m| * (wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))))) * ‖iotaC p s‖ ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_one
          refine mul_le_mul_of_nonneg_right ?_ hι
          exact mul_le_mul_of_nonneg_left (h4.trans hCabs) hK
      _ = _ := by ring
  have hmeasI : ∀ m ≤ q, ∀ x : G.Mat s, AEStronglyMeasurable
      (fun η : XiH p s σ => iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x) (muXiH p s σ) := by
    intro m hm x
    have hfun : (fun η : XiH p s σ => iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x) =
        fun η => psiH β σ η •
          ((iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s) := by
      funext η
      rw [hexp m hm η x]
      ext v
      rfl
    rw [hfun]
    refine Continuous.aestronglyMeasurable ?_
    refine (continuous_psiH β σ).smul ?_
    exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin m => iotaC p s)).continuous.comp
      ((hcd.continuous_iteratedFDeriv (by exact_mod_cast hm)).comp (hTc.add continuous_const))
  have hbndI : Integrable (fun η : XiH p s σ => ∑ k ∈ Finset.range (q + 1),
      ‖iotaC p s‖ ^ k * K * |C k| * wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ))))) (muXiH p s σ) :=
    integrable_finset_sum _ fun k hk => by
      have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact (hIT p s σ _ (he k hkq)).const_mul _
  have hle : ∀ m ≤ q, ∀ (η : XiH p s σ) (x : G.Mat s),
      ‖iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x‖ ≤
        ∑ k ∈ Finset.range (q + 1), ‖iotaC p s‖ ^ k * K * |C k| * wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))) := by
    intro m hm η x
    refine (hpt m hm η x).trans ?_
    have hx1 : (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
        (neg_nonpos.mpr (div_nonneg (hepos m hm) h5N.le))
    have h0 : 0 ≤ ‖iotaC p s‖ ^ m * K * |C m| :=
      mul_nonneg (mul_nonneg (by positivity) hK) (abs_nonneg _)
    have hw : 0 ≤ wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := Real.rpow_nonneg (wtH_pos η).le _
    have hterm : ‖iotaC p s‖ ^ m * K * |C m| * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) ≤
        ‖iotaC p s‖ ^ m * K * |C m| * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := by
      calc ‖iotaC p s‖ ^ m * K * |C m| * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))
          = (‖iotaC p s‖ ^ m * K * |C m| * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := by ring
        _ ≤ (‖iotaC p s‖ ^ m * K * |C m| * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))) * 1 :=
          mul_le_mul_of_nonneg_left hx1 (mul_nonneg h0 hw)
        _ = _ := mul_one _
    exact hterm.trans (Finset.single_le_sum
      (f := fun k => ‖iotaC p s‖ ^ k * K * |C k| * wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))))
      (fun k _ => mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hK) (abs_nonneg _))
        (Real.rpow_nonneg (wtH_pos η).le _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)))
  have hTI := taylor_integral (μ := muXiH p s σ) (q := q)
    (fun η x => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s x)))
    (fun η x m => iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x)
    (fun η => ContDiff.ftaylorSeries (by
      exact (Lc (psiH β σ η) : V →L[ℝ] V).contDiff.comp
        ((hcd.comp (contDiff_const.add contDiff_id)).comp (iotaC p s).contDiff)))
    hmeasI _ hbndI hle
  have hPhi : PhiTop β σ d Φ0 =
      fun x => ∫ η, Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s x)) ∂(muXiH p s σ) := by
    funext x
    unfold PhiTop
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show psiH β σ η • Φ0 (ZjH σ d η x) = psiH β σ η • Φ0 (Tm η + iotaC p s x)
    rw [← hsplit η x]
    rfl
  refine ⟨fun CC => ?_, ?_, fun i hi Z => ?_⟩
  · have hc : Continuous fun η : XiH p s σ => psiH β σ η • Φ0 (ZjH σ d η CC) :=
      (continuous_psiH β σ).smul (hcd.continuous.comp (continuous_zjH σ d CC))
    refine ((hIT p s σ _ (he 0 (Nat.zero_le _))).const_mul
      (‖iotaC p s‖ ^ 0 * K * |C 0| * (1 + ‖CC‖) ^ (-(e 0 / (5 * ((p + s : ℕ) : ℝ)))))).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)
    have h := hpt 0 (Nat.zero_le _) η CC
    rw [norm_iteratedFDeriv_zero] at h
    have e1 : Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s CC)) = psiH β σ η • Φ0 (ZjH σ d η CC) := by
      rw [Lc_apply, ← hsplit η CC]
      rfl
    rw [e1] at h
    exact h
  · rw [hPhi]
    exact hTI.contDiff
  · beta_reduce
    have hiq : ((i : ℕ) : WithTop ℕ∞) ≤ (q : WithTop ℕ∞) := by exact_mod_cast hi
    have heq := hTI.eq_iteratedFDeriv hiq Z
    rw [hPhi, ← heq]
    beta_reduce
    have hI : Integrable (fun η : XiH p s σ => (‖iotaC p s‖ ^ i * K * |C i| * (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ))))) *
        wtH η ^ (-(e i / (5 * ((p + s : ℕ) : ℝ))))) (muXiH p s σ) :=
      (hIT p s σ _ (he i hi)).const_mul _
    refine (norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall fun η => hpt i hi η Z)).trans ?_
    rw [integral_const_mul]
    have hsum := Finset.single_le_sum (s := Finset.range (q + 1))
      (f := fun k => ‖iotaC p s‖ ^ k * |C k| * ∫ η, wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ))
      (fun k _ => mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
        (integral_nonneg fun η => Real.rpow_nonneg (wtH_pos η).le _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    have hr : 0 ≤ (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) := by positivity
    calc ‖iotaC p s‖ ^ i * K * |C i| * (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) * ∫ η, wtH η ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ)
        = (‖iotaC p s‖ ^ i * |C i| * ∫ η, wtH η ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ)) * K * (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hK) hr
end Formalism.FourierDecayAlt.P.Ux13
