-- Prove2me | solution 1 for BilateralProfitRegular.eq_55
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T15:46:41.331642+00:00
-- url     : https://prove2.me/submissions/81910d88-9a5b-40a4-bae5-53aeba2d772e

import Mathlib
import Definitions.Def_BilateralProfitRegular_ConvexBandit
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
import Theorems.Thm_BilateralProfitRegular_lemma_6_2
import Definitions.Def_BilateralProfitRegular_Auxiliary
import Theorems.Thm_BilateralProfitRegular_corollary_3_1
import Definitions.Def_BilateralProfitRegular_Stochastic


section BundlePart000



noncomputable section

namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private abbrev Vec2 := Fin 2 → ℝ

private def pairCoordinates : Vec2 ≃L[ℝ] (ℝ × ℝ) := ContinuousLinearEquiv.finTwoArrow ℝ ℝ

private def scaleHistory (δ : ℝ) {n : ℕ} (h : Fin n → (ℝ × ℝ) × ℝ) : Fin n → Vec2 × ℝ :=
  fun i => (pairCoordinates.symm (h i).1, δ * (h i).2)

private def unscaleHistory (δ : ℝ) {n : ℕ} (h : Fin n → Vec2 × ℝ) : Fin n → (ℝ × ℝ) × ℝ :=
  fun i => (pairCoordinates (h i).1, δ⁻¹ * (h i).2)

private theorem unscaleHistory_scaleHistory {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (h : Fin n → (ℝ × ℝ) × ℝ) :
    unscaleHistory δ (scaleHistory δ h) = h := by
  funext i
  simp [unscaleHistory, scaleHistory, ← mul_assoc, hδ.ne']

private theorem scaleHistory_snoc (δ : ℝ) {n : ℕ} (h : Fin n → (ℝ × ℝ) × ℝ)
    (x : ℝ × ℝ) (y : ℝ) :
    scaleHistory δ (Fin.snoc h (x, y)) =
      Fin.snoc (scaleHistory δ h) (pairCoordinates.symm x, δ*y) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [scaleHistory]

private def scaledEnvironment (δ : ℝ) (ν : ObsEnv (ℝ × ℝ)) : ObsEnv Vec2 :=
  fun n => ((ν n).comap (fun z => (unscaleHistory δ z.1, pairCoordinates z.2))
    ((measurable_pi_lambda _ fun i =>
      (pairCoordinates.continuous.measurable.comp
        (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst))).prodMk
        (measurable_const.mul (measurable_snd.comp
          ((measurable_pi_apply i).comp measurable_fst)))).prodMk
            (pairCoordinates.continuous.measurable.comp measurable_snd))).map (fun y => δ*y)

private theorem scaledEnvironment_apply (δ : ℝ) (ν : ObsEnv (ℝ × ℝ))
    (n : ℕ) (h : Fin n → Vec2 × ℝ) (z : Vec2) :
    scaledEnvironment δ ν n (h,z) =
      (ν n (unscaleHistory δ h, pairCoordinates z)).map (fun y => δ*y) := by
  unfold scaledEnvironment
  have hm : Measurable (fun y : ℝ => δ*y) := measurable_const.mul measurable_id
  erw [Kernel.map_apply _ hm]
  rfl

variable {Ω : Type} [MeasurableSpace Ω]

private def scaleQueryAlg (δ : ℝ) (A : BanditAlg Vec2 Ω) : BanditAlg (ℝ × ℝ) Ω where
  query n ω h := pairCoordinates (A.query n ω (scaleHistory δ h))
  measurable_query n := pairCoordinates.continuous.measurable.comp
    ((A.measurable_query n).comp (measurable_fst.prodMk
      (measurable_pi_lambda _ fun i =>
        (pairCoordinates.symm.continuous.measurable.comp
          (measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))).prodMk
          (measurable_const.mul (measurable_snd.comp
            ((measurable_pi_apply i).comp measurable_snd))))))

private theorem go_scaleQueryAlg {δ : ℝ} (hδ : 0 < δ) (A : BanditAlg Vec2 Ω)
    (ν : ObsEnv (ℝ × ℝ)) (g : ℝ × ℝ → ℝ≥0∞) (ω : Ω)
    (m n : ℕ) (h : Fin n → (ℝ × ℝ) × ℝ) :
    ENNReal.ofReal δ * (scaleQueryAlg δ A).go ν g (fun _ _ => 0) m n ω h =
      A.go (scaledEnvironment δ ν) (fun x => ENNReal.ofReal δ * g (pairCoordinates x))
        (fun _ _ => 0) m n ω (scaleHistory δ h) := by
  induction m generalizing n with
  | zero => simp [BanditAlg.go]
  | succ m ih =>
    simp only [BanditAlg.go, scaledEnvironment_apply, unscaleHistory_scaleHistory hδ, mul_add]
    let a := A.query n ω (scaleHistory δ h)
    change _ + ENNReal.ofReal δ * (∫⁻ y, (scaleQueryAlg δ A).go ν g (fun _ _ => 0)
      m (n+1) ω (Fin.snoc h (pairCoordinates a, y)) ∂(ν n (h, pairCoordinates a))) =
      _ + ∫⁻ y, A.go (scaledEnvironment δ ν)
        (fun x => ENNReal.ofReal δ * g (pairCoordinates x)) (fun _ _ => 0) m (n+1) ω
        (Fin.snoc (scaleHistory δ h) (a,y))
          ∂((ν n (h, pairCoordinates a)).map (fun y => δ*y))
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      (measurableEmbedding_mulLeft₀ hδ.ne').lintegral_map]
    congr 1
    apply lintegral_congr
    intro y
    rw [ih, scaleHistory_snoc, pairCoordinates.symm_apply_apply]

end BilateralProfitRegular
end
end BundlePart000


section BundlePart001






noncomputable section

namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory Set MechanismDesign.BilateralTrade
open scoped ENNReal

private theorem bounded_psi2 (Q : Measure ℝ) [IsProbabilityMeasure Q]
    {B a : ℝ} (hB : 0 < B) (h : ∀ᵐ y ∂Q, |y-a| ≤ B) :
    HighDimProb.Concentration.subgaussianNorm Q (fun y => y-a) ≤ ENNReal.ofReal (2*B) := by
  have hle : ∀ᵐ y ∂Q, Real.exp ((y-a)^2 / (2*B)^2) ≤ 2 := by
    filter_upwards [h] with y hy
    have hs : (y-a)^2 ≤ B^2 := sq_le_sq' (abs_le.mp hy).1 (abs_le.mp hy).2
    have he : (y-a)^2 / (2*B)^2 ≤ 1/4 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have hl : (1/4 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr (he.trans hl)
  have hI : Integrable (fun y : ℝ => Real.exp ((y-a)^2 / (2*B)^2)) Q := by
    apply Integrable.of_bound (by fun_prop) 2
    filter_upwards [hle] with y hy
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hy
  have hi : (∫ y, Real.exp ((y-a)^2 / (2*B)^2) ∂Q) ≤ 2 := by
    have hh := integral_mono_ae hI (integrable_const (2:ℝ)) hle
    simpa using hh
  unfold HighDimProb.Concentration.subgaussianNorm
  exact iInf_le_of_le (2*B)
    (iInf_le_of_le (by positivity) (iInf_le_of_le hI (iInf_le_of_le hi le_rfl)))

private theorem regret_succ_ge {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : BanditAlg X Ω) (ν : ObsEnv X) (Pω : Measure Ω) (n : ℕ)
    (L : X → ℝ) (K : Set X) : A.regret ν Pω n L K ≤ A.regret ν Pω (n+1) L K := by
  unfold BanditAlg.regret
  apply lintegral_mono
  intro ω
  have hh (m τ : ℕ) (h : Fin τ → X × ℝ) :
      A.go ν (fun x => ENNReal.ofReal (L x - sInf (L '' K))) (fun _ _ => 0) m τ ω h ≤
      A.go ν (fun x => ENNReal.ofReal (L x - sInf (L '' K))) (fun _ _ => 0) (m+1) τ ω h := by
    induction m generalizing τ with
    | zero => simp [BanditAlg.go]
    | succ m ih =>
      simp only [BanditAlg.go]
      exact add_le_add (le_refl _) (lintegral_mono fun y => ih _ _)
  exact hh n 0 Fin.elim0

private theorem scaled_regret {Ω : Type} [MeasurableSpace Ω]
    {δ : ℝ} (hδ : 0 < δ) (A : BanditAlg Vec2 Ω) (ν : ObsEnv (ℝ × ℝ))
    (Pω : Measure Ω) (n : ℕ) (L : ℝ × ℝ → ℝ) {K : Set (ℝ × ℝ)}
    (hne : K.Nonempty) (hb : BddBelow (L '' K)) :
    ENNReal.ofReal δ * (scaleQueryAlg δ A).regret ν Pω n L K =
      A.regret (scaledEnvironment δ ν) Pω n (fun x => δ * L (pairCoordinates x))
        (pairCoordinates ⁻¹' K) := by
  have hImg : (fun x => δ * L (pairCoordinates x)) '' (pairCoordinates ⁻¹' K) =
      (fun y => δ*y) '' (L '' K) := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨L (pairCoordinates x), mem_image_of_mem _ hx, rfl⟩
    · rintro ⟨_, ⟨x,hx,rfl⟩,rfl⟩
      refine ⟨pairCoordinates.symm x, ?_, by simp⟩
      change pairCoordinates (pairCoordinates.symm x) ∈ K
      simpa using hx
  have hm : Monotone (fun y : ℝ => δ*y) :=
    fun _ _ h => mul_le_mul_of_nonneg_left h hδ.le
  have hInf : δ * sInf (L '' K) = sInf ((fun y => δ*y) '' (L '' K)) :=
    hm.map_csInf_of_continuousAt
    (Cf := (continuous_const.mul continuous_id).continuousAt) (hne.image L) hb
  unfold BanditAlg.regret
  rw [hImg, ← hInf]
  simp only [← mul_sub, ENNReal.ofReal_mul hδ.le]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro ω
  have he : scaleHistory δ (Fin.elim0 : Fin 0 → (ℝ × ℝ) × ℝ) = Fin.elim0 :=
    Subsingleton.elim _ _
  exact he ▸ go_scaleQueryAlg hδ A ν (fun x => ENNReal.ofReal (L x - sInf (L '' K)))
    ω n 0 Fin.elim0

private theorem aux_open : IsOpen intT := by
  exact ((isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const)))

private theorem eq_55 :
    ∀ C₁ : ℝ, 0 < C₁ → ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → ∀ K : Set (ℝ × ℝ), K.Nonempty → IsCompact K → Convex ℝ K → K ⊆ intT →
      ∀ n : ℕ, 1 ≤ n →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (alg : BanditAlg (ℝ × ℝ) Ω),
        alg.QueriesIn K ∧
        ∀ E : Environment, RegularUnit E → ∀ lam : ℝ, 0 < lam →
          (∀ x ∈ K, 99 / 100 * δ ≤ auxProfit E lam x ∧ auxProfit E lam x ≤ 6 * δ) →
          ∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) K →
            ν.ValuesIn K (Set.Icc 0 (C₁ / δ)) →
            alg.regret ν Pω n (fun x => 1 / auxProfit E lam x) K ≤
              ENNReal.ofReal (C / δ * Real.sqrt n * Real.log (2 * n) ^ 2) := by
  intro C₁ hC₁
  obtain ⟨C₀, hC₀, hBandit⟩ := corollary_3_1 2 2 (by norm_num)
  let γ : NNReal := ⟨2*(C₁+2), by positivity⟩
  let C := 2*C₀*(1+(γ : ℝ))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro δ hδ K hne hK hcv hSub n hn
  let S := pairCoordinates ⁻¹' K
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨pairCoordinates.symm x, by simpa [S] using hx⟩
  have hSc : IsCompact S := pairCoordinates.toHomeomorph.isClosedEmbedding.isCompact_preimage hK
  have hSv : Convex ℝ S := hcv.linear_preimage pairCoordinates.toLinearMap
  have hDim : Module.finrank ℝ (vectorSpan ℝ S) ≤ 2 := by
    exact (Submodule.finrank_le (vectorSpan ℝ S)).trans (by simp)
  obtain ⟨Ω, mΩ, Pω, hpω, A, hA, hR⟩ :=
    hBandit 2 S hSne hSc hSv hDim 0 γ (n+1) (by omega)
  let B := scaleQueryAlg δ A
  refine ⟨Ω, mΩ, Pω, hpω, B, fun τ ω h => hA τ ω (scaleHistory δ h), ?_⟩
  intro E hE lam hlam hSafe ν hMean hValues
  let L : ℝ × ℝ → ℝ := fun x => 1 / auxProfit E lam x
  let L' : Vec2 → ℝ := fun x => δ * L (pairCoordinates x)
  have hCv0 : ConvexOn ℝ intT L := (lemma_6_2 E hE lam hlam).1
  have hCont : ContinuousOn L K := (hCv0.continuousOn aux_open).mono hSub
  have hCv : ConvexOn ℝ K L := hCv0.subset hSub hcv
  have hCv' : ConvexOn ℝ S L' :=
    (hCv.comp_affineMap pairCoordinates.toLinearMap.toAffineMap).smul hδ.le
  have hCont' : ContinuousOn L' S :=
    continuousOn_const.mul (hCont.comp pairCoordinates.continuous.continuousOn (fun _ hx => hx))
  have hRange : ∀ x ∈ S, 0 ≤ L' x ∧ L' x ≤ 0 + 2 := by
    intro x hx
    have hu := (hSafe (pairCoordinates x) hx).1
    have hpos : 0 < auxProfit E lam (pairCoordinates x) :=
      (mul_pos (by norm_num : (0 : ℝ) < 99 / 100) hδ).trans_le hu
    change 0 ≤ δ * (1 / auxProfit E lam (pairCoordinates x)) ∧
      δ * (1 / auxProfit E lam (pairCoordinates x)) ≤ 0 + 2
    refine ⟨by positivity, ?_⟩
    rw [mul_one_div, zero_add, div_le_iff₀ hpos]
    linarith
  let ν' := scaledEnvironment δ ν
  have hs : Measurable (fun y : ℝ => δ*y) := measurable_const.mul measurable_id
  have hk (τ : ℕ) : IsMarkovKernel (ν' τ) := by
    have hMarkov : IsMarkovKernel (ν τ) := hMean.1 τ
    constructor
    rintro ⟨h, x⟩
    change IsProbabilityMeasure (scaledEnvironment δ ν τ (h, x))
    rw [scaledEnvironment_apply]
    exact Measure.isProbabilityMeasure_map hs.aemeasurable
  have hMean' : ν'.MeanOn L' S := by
    refine ⟨hk, ?_⟩
    intro τ h x hx
    have hp := hMean.2 τ (unscaleHistory δ h) (pairCoordinates x) hx
    rw [show ν' τ (h,x) =
      (ν τ (unscaleHistory δ h, pairCoordinates x)).map (fun y => δ*y) from
      scaledEnvironment_apply δ ν τ h x]
    refine ⟨(integrable_map_measure measurable_id.aestronglyMeasurable hs.aemeasurable).mpr
      (hp.1.const_mul δ), ?_⟩
    change (∫ y, id y ∂((ν τ (unscaleHistory δ h, pairCoordinates x)).map (fun y => δ*y))) = _
    rw [integral_map hs.aemeasurable measurable_id.aestronglyMeasurable]
    change (∫ y, δ * y ∂(ν τ (unscaleHistory δ h, pairCoordinates x))) = _
    rw [integral_const_mul, hp.2]
  have hNorm' : ∀ τ h, ∀ x ∈ S,
      HighDimProb.Concentration.subgaussianNorm (ν' τ (h,x)) (fun y => y - L' x) ≤ γ := by
    intro τ h x hx
    have hMarkov : IsMarkovKernel (ν' τ) := hk τ
    rw [ENNReal.coe_nnreal_eq γ]
    change _ ≤ ENNReal.ofReal (2*(C₁+2))
    refine bounded_psi2 _ (by positivity) ?_
    have hRaw : ∀ᵐ y ∂ν τ (unscaleHistory δ h,pairCoordinates x), y ∈ Icc 0 (C₁/δ) :=
      ae_iff.mpr (hValues τ (unscaleHistory δ h) (pairCoordinates x) hx)
    change ∀ᵐ y ∂(scaledEnvironment δ ν τ (h,x)), |y-L' x| ≤ C₁+2
    have hMeas : MeasurableSet {y : ℝ | |y - L' x| ≤ C₁ + 2} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [scaledEnvironment_apply, ae_map_iff hs.aemeasurable hMeas]
    filter_upwards [hRaw] with y hy
    have h0 : 0 ≤ δ*y := mul_nonneg hδ.le hy.1
    have h1 : δ*y ≤ C₁ := (mul_le_mul_of_nonneg_left hy.2 hδ.le).trans_eq (by
      field_simp)
    have hr := hRange x hx
    exact abs_le.mpr ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hBdd : BddBelow (L '' K) := (hK.image_of_continuousOn hCont).bddBelow
  have hη := hR L' hCont' hCv' hRange ν' hMean' hNorm'
  have hmul := scaled_regret hδ A ν Pω (n+1) L hne hBdd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log ((n+1 : ℕ) : ℝ) ^ 2 ≤ Real.log (2*(n:ℝ)) ^ 2 := by
    have hlog0 : 0 ≤ Real.log ((n+1 : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith only [hn'])
    have hlog1 : Real.log ((n+1 : ℕ) : ℝ) ≤ Real.log (2*(n:ℝ)) :=
      Real.log_le_log (by positivity) (by push_cast; linarith)
    nlinarith
  have hsqrt : Real.sqrt ((n+1 : ℕ) : ℝ) ≤ 2*Real.sqrt n := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    push_cast
    norm_num
    linarith
  have hz : ENNReal.ofReal δ ≠ 0 := by simpa using hδ
  apply (ENNReal.mul_le_mul_iff_right hz ENNReal.ofReal_ne_top).mp
  calc
    _ ≤ ENNReal.ofReal δ * B.regret ν Pω (n+1) L K := by
      gcongr
      exact regret_succ_ge B ν Pω n L K
    _ ≤ _ := by
      rw [show ENNReal.ofReal δ * B.regret ν Pω (n+1) L K = _ from hmul]
      refine hη.trans ?_
      rw [← ENNReal.ofReal_mul hδ.le]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ C₀ * (1+(γ : ℝ)) * (2*Real.sqrt n) * Real.log (2*(n:ℝ)) ^ 2 := by gcongr
        _ = _ := by dsimp [C]; field_simp

end BilateralProfitRegular
end
end BundlePart001

open BilateralProfitRegular
open MeasureTheory MechanismDesign.BilateralTrade

theorem solution :
    ∀ C₁ : ℝ, 0 < C₁ → ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → ∀ K : Set (ℝ × ℝ), K.Nonempty → IsCompact K → Convex ℝ K → K ⊆ intT →
      ∀ n : ℕ, 1 ≤ n →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (alg : BanditAlg (ℝ × ℝ) Ω),
        alg.QueriesIn K ∧
        ∀ E : Environment, RegularUnit E → ∀ lam : ℝ, 0 < lam →
          (∀ x ∈ K, 99 / 100 * δ ≤ auxProfit E lam x ∧ auxProfit E lam x ≤ 6 * δ) →
          ∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) K →
            ν.ValuesIn K (Set.Icc 0 (C₁ / δ)) →
            alg.regret ν Pω n (fun x => 1 / auxProfit E lam x) K ≤
              ENNReal.ofReal (C / δ * Real.sqrt n * Real.log (2 * n) ^ 2) := by
  exact BilateralProfitRegular.eq_55
