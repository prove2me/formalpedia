-- Prove2me | solution 1 for DeepONetError.error_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T10:09:18.246653+00:00
-- url     : https://prove2.me/submissions/676de1c4-c0fd-4c7b-b762-627564dfc505

import Mathlib
import Definitions.Def_DeepONetError_Basic

open MeasureTheory
open DeepONetError

namespace DeepONetAux

lemma edist_le_lipConst {α β : Type*} [MetricSpace α] [EMetricSpace β] (g : α → β) (x y : α) :
    edist (g x) (g y) ≤ lipConst g * edist x y := by
  by_cases h : x = y
  · subst h; simp
  · have h0 : edist x y ≠ 0 := (edist_pos.mpr h).ne'
    have ht : edist x y ≠ ⊤ := edist_ne_top x y
    have : edist (g x) (g y) / edist x y ≤ lipConst g := le_iSup₂_of_le x y le_rfl
    exact (ENNReal.div_le_iff h0 ht).mp this

lemma edist_le_holderConst {α β : Type*} [MetricSpace α] [EMetricSpace β] (a : ℝ) (ha : 0 < a)
    (g : α → β) (A : Set α) {x y : α} (hx : x ∈ A) (hy : y ∈ A) :
    edist (g x) (g y) ≤ holderConst a g A * edist x y ^ a := by
  by_cases h : x = y
  · subst h; simp
  · have h0 : edist x y ^ a ≠ 0 := (ENNReal.rpow_pos (edist_pos.mpr h) (edist_ne_top x y)).ne'
    have ht : edist x y ^ a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ha.le (edist_ne_top x y)
    have : edist (g x) (g y) / edist x y ^ a ≤ holderConst a g A :=
      le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
    exact (ENNReal.div_le_iff h0 ht).mp this

/-- Minkowski for three nonnegative functions in `L²`. -/
lemma l2_add3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g h : Ω → ENNReal)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (hh : AEMeasurable h μ) :
    (∫⁻ x, (f x + g x + h x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
      (∫⁻ x, f x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) + (∫⁻ x, g x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) +
        (∫⁻ x, h x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  have key : ∀ (u v : Ω → ENNReal), AEMeasurable u μ → AEMeasurable v μ →
      (∫⁻ x, (u x + v x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) ≤
        (∫⁻ x, u x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) + (∫⁻ x, v x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
    intro u v hu hv
    have := ENNReal.lintegral_Lp_add_le (p := 2) hu hv (by norm_num)
    simpa [ENNReal.rpow_two] using this
  calc (∫⁻ x, (f x + g x + h x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
      ≤ (∫⁻ x, (f x + g x) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) + (∫⁻ x, h x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) :=
        key (fun x => f x + g x) h (hf.add hg) hh
    _ ≤ _ := by gcongr; exact key f g hf hg

end DeepONetAux

open DeepONetAux

theorem solution {d n m p : ℕ} {Dset : Set (Fin d → ℝ)} {U : Set (Fin n → ℝ)}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (L2 U)] [BorelSpace (L2 U)]
    (iota : X →L[ℝ] L2 Dset) (mu : Measure X) (A : Set X) (G : X → L2 U)
    (hdata : IsDeepONetData Dset U iota mu A G) (alpha : ℝ) (halpha0 : 0 < alpha)
    (halpha1 : alpha ≤ 1)
    (E : X → EuclideanSpace ℝ (Fin m)) (hE : Measurable E)
    (Apx : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin p)) (hApx : Measurable Apx)
    (tau : Fin (p + 1) → L2 U)
    (Dec : EuclideanSpace ℝ (Fin m) → X) (hDec : Measurable Dec) (hDecA : ∀ u ∈ A, Dec (E u) ∈ A)
    (Proj : L2 U → EuclideanSpace ℝ (Fin p)) (hProj : Measurable Proj) :
    totalErr mu G (fun u => trunkRec tau (Apx (E u))) ≤
      holderConst alpha G A * lipConst (fun v => trunkRec tau (Proj v)) * encErr mu E Dec ^ alpha +
        lipConst (trunkRec tau) * approxErr mu G E Apx Dec Proj +
        recErr (mu.map G) (trunkRec tau) Proj := by
  obtain ⟨-, -, -, -, -, hprob, -, hAm, hA1, -, hGm, -⟩ := hdata
  have := hprob
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have hRc : Continuous (trunkRec tau) := by
    unfold trunkRec
    fun_prop
  set f : L2 U → L2 U := fun v => trunkRec tau (Proj v) with hf
  set LR := lipConst (trunkRec tau)
  set LRP := lipConst f
  set H := holderConst alpha G A
  have hAae : ∀ᵐ u ∂mu, u ∈ A := by
    have : mu Aᶜ = 0 := by rw [prob_compl_eq_zero_iff hAm]; exact hA1
    exact ae_iff.mpr this
  -- the three pieces
  set a : X → ENNReal := fun u => edist (f (G u)) (G u) with ha
  set b : X → ENNReal := fun u => LRP * (H * edist (Dec (E u)) u ^ alpha) with hb
  set c : X → ENNReal := fun u => LR * edist (Apx (E u)) (Proj (G (Dec (E u)))) with hc
  have hfm : Measurable f := hRc.measurable.comp hProj
  have ham : Measurable a := (hfm.comp hGm).edist hGm
  have hbm : Measurable b :=
    ((((hDec.comp hE).edist measurable_id).pow_const alpha).const_mul H).const_mul LRP
  have hcm : Measurable c :=
    ((hApx.comp hE).edist (hProj.comp (hGm.comp (hDec.comp hE)))).const_mul LR
  have hpt : ∀ u ∈ A, edist (G u) (trunkRec tau (Apx (E u))) ≤ a u + b u + c u := by
    intro u hu
    have h2 : edist (f (G u)) (f (G (Dec (E u)))) ≤ b u := by
      refine (edist_le_lipConst f _ _).trans ?_
      refine mul_le_mul' le_rfl ?_
      rw [edist_comm]
      exact edist_le_holderConst alpha halpha0 G A (hDecA u hu) hu
    have h3 : edist (f (G (Dec (E u)))) (trunkRec tau (Apx (E u))) ≤ c u := by
      refine (edist_le_lipConst (trunkRec tau) _ _).trans ?_
      rw [edist_comm (Proj (G (Dec (E u))))]
    calc edist (G u) (trunkRec tau (Apx (E u)))
        ≤ edist (G u) (f (G u)) + edist (f (G u)) (f (G (Dec (E u)))) +
            edist (f (G (Dec (E u)))) (trunkRec tau (Apx (E u))) := edist_triangle4 _ _ _ _
      _ ≤ a u + b u + c u := by
          rw [edist_comm (G u)]
          exact add_le_add (add_le_add le_rfl h2) h3
  -- step 1: pointwise bound and Minkowski
  have hstep1 : totalErr mu G (fun u => trunkRec tau (Apx (E u))) ≤
      (∫⁻ u, a u ^ 2 ∂mu) ^ ((1 : ℝ) / 2) + (∫⁻ u, b u ^ 2 ∂mu) ^ ((1 : ℝ) / 2) +
        (∫⁻ u, c u ^ 2 ∂mu) ^ ((1 : ℝ) / 2) := by
    refine le_trans ?_ (l2_add3 mu a b c ham.aemeasurable hbm.aemeasurable hcm.aemeasurable)
    unfold totalErr
    refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)
    filter_upwards [hAae] with u hu
    rw [← edist_eq_enorm_sub]
    exact pow_le_pow_left' (hpt u hu) 2
  -- the reconstruction term
  have hrec : (∫⁻ u, a u ^ 2 ∂mu) ^ ((1 : ℝ) / 2) = recErr (mu.map G) (trunkRec tau) Proj := by
    unfold recErr
    rw [lintegral_map _ hGm]
    · simp only [ha, hf, edist_eq_enorm_sub]
    · exact ((hfm.sub measurable_id).enorm).pow_const 2
  -- the approximation term
  have happ : (∫⁻ u, c u ^ 2 ∂mu) ^ ((1 : ℝ) / 2) = LR * approxErr mu G E Apx Dec Proj := by
    unfold approxErr
    rw [lintegral_map _ hE]
    · have hI : ∫⁻ u, c u ^ 2 ∂mu =
          LR ^ 2 * ∫⁻ u, ‖Apx (E u) - Proj (G (Dec (E u)))‖ₑ ^ 2 ∂mu := by
        simp only [hc, mul_pow, edist_eq_enorm_sub]
        exact lintegral_const_mul _ ((((hApx.comp hE).sub
          (hProj.comp (hGm.comp (hDec.comp hE)))).enorm).pow_const 2)
      rw [hI, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul]
      norm_num
    · exact ((hApx.sub (hProj.comp (hGm.comp hDec))).enorm).pow_const 2
  -- the encoding term
  have henc : (∫⁻ u, b u ^ 2 ∂mu) ^ ((1 : ℝ) / 2) ≤ H * LRP * encErr mu E Dec ^ alpha := by
    set e : X → ENNReal := fun u => edist (Dec (E u)) u with he
    have hem : Measurable e := (hDec.comp hE).edist measurable_id
    have hI : ∫⁻ u, b u ^ 2 ∂mu = (H * LRP) ^ 2 * ∫⁻ u, e u ^ (2 * alpha) ∂mu := by
      rw [← lintegral_const_mul _ (hem.pow_const _)]
      refine lintegral_congr fun u => ?_
      simp only [hb, he]
      rw [mul_comm 2 alpha, ENNReal.rpow_mul, ENNReal.rpow_two]
      ring
    have hL := eLpNorm'_le_eLpNorm'_of_exponent_le (f := e) (p := 2 * alpha) (q := 2)
      (by positivity) (by linarith) mu hem.aestronglyMeasurable
    simp only [eLpNorm', enorm_eq_self] at hL
    have hL2 := ENNReal.rpow_le_rpow hL halpha0.le
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hL2
    have hx : 1 / (2 * alpha) * alpha = 1 / 2 := by field_simp
    rw [hx] at hL2
    rw [hI, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
    refine mul_le_mul' le_rfl (le_of_le_of_eq hL2 ?_)
    unfold encErr
    rw [← ENNReal.rpow_mul]
    simp only [he, edist_eq_enorm_sub, ENNReal.rpow_two]
  calc totalErr mu G (fun u => trunkRec tau (Apx (E u)))
      ≤ _ := hstep1
    _ ≤ recErr (mu.map G) (trunkRec tau) Proj + H * LRP * encErr mu E Dec ^ alpha +
          LR * approxErr mu G E Apx Dec Proj := by
        rw [hrec, happ]; exact add_le_add (add_le_add le_rfl henc) le_rfl
    _ = _ := by ring
