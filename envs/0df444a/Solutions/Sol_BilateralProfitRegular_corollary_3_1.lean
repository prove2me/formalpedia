-- Prove2me | solution 1 for BilateralProfitRegular.corollary_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T15:26:12.663209+00:00
-- url     : https://prove2.me/submissions/470e17a1-6ce5-4b8f-b9f9-e2838720a21e

import Mathlib
import Definitions.Def_BilateralProfitRegular_ConvexBandit
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm_v2
import Theorems.Thm_BilateralProfitMHR_corollary_3_1


section BundlePart000




noncomputable section

namespace BilateralProfitRegular

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

private theorem coordinates_in_affine_span {d k : ℕ} (K : Set (Fin d → ℝ))
    (hne : K.Nonempty) (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdim : Module.finrank ℝ (vectorSpan ℝ K) ≤ k) :
    ∃ m ≤ k, ∃ S : Set (EuclideanSpace ℝ (Fin m)),
      ∃ f : EuclideanSpace ℝ (Fin m) →ᵃ[ℝ] (Fin d → ℝ),
        S.Nonempty ∧ IsCompact S ∧ Convex ℝ S ∧ Continuous f ∧ f '' S = K := by
  classical
  obtain ⟨p, hp⟩ := hne
  let V := vectorSpan ℝ K
  let m := Module.finrank ℝ V
  let e₀ : (Fin m → ℝ) ≃ₗ[ℝ] V := (Module.finBasis ℝ V).equivFun.symm
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] V :=
    ((EuclideanSpace.equiv (Fin m) ℝ).toLinearEquiv.trans e₀).toContinuousLinearEquiv
  let f := (V.subtype.comp e.toLinearEquiv.toLinearMap).toAffineMap +
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin m)) p
  let S := f ⁻¹' K
  have hf_apply (y : EuclideanSpace ℝ (Fin m)) : f y = (e y : Fin d → ℝ) + p := rfl
  let K₀ := (fun x => x - p) '' K
  have hsub : IsCompact ((Subtype.val : V → Fin d → ℝ) ⁻¹' K₀) := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' (hK.image (continuous_id.sub continuous_const))
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x-p, vsub_mem_vectorSpan ℝ hx hp⟩, rfl⟩
  have hSeq : S = e ⁻¹' ((Subtype.val : V → Fin d → ℝ) ⁻¹' K₀) := by
    ext y
    change f y ∈ K ↔ (e y : Fin d → ℝ) ∈ K₀
    rw [hf_apply]
    constructor
    · intro hy
      exact ⟨_, hy, add_sub_cancel_right _ _⟩
    · rintro ⟨x, hx, heq⟩
      exact (sub_eq_iff_eq_add.mp heq) ▸ hx
  have hc : IsCompact S := hSeq ▸ e.toHomeomorph.isClosedEmbedding.isCompact_preimage hsub
  have himage : f '' S = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      let x' : V := ⟨x-p, vsub_mem_vectorSpan ℝ hx hp⟩
      have heq : f (e.symm x') = x := by
        rw [hf_apply, e.apply_symm_apply]
        exact sub_add_cancel x p
      exact ⟨e.symm x', show f (e.symm x') ∈ K from heq.symm ▸ hx, heq⟩
  refine ⟨m, ?_, S, f, ?_, hc, hcv.affine_preimage f,
    f.continuous_of_finiteDimensional, himage⟩
  · exact hdim
  · rw [← himage] at hp
    obtain ⟨y, hy, _⟩ := hp
    exact ⟨y, hy⟩

section History

variable {X Y Ω : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]

private def transportQueryAlg (f : Y → X) (hf : Measurable f)
    (A : BilateralProfitMHR.QueryAlg Y Ω) : BanditAlg X Ω where
  query τ ω h := f (A.query τ ω (fun i => (h i).2))
  measurable_query τ :=
    hf.comp ((A.query_measurable τ).comp (measurable_fst.prodMk
      (measurable_pi_lambda _ fun i => measurable_snd.comp
        ((measurable_pi_apply i).comp measurable_snd))))

private def transportedObs (f : Y → X) (ν : ObsEnv X) : BilateralProfitMHR.ObsKernel Y :=
  fun τ xs ys z => ν τ ((fun i => (f (xs i), ys i)), f z)

private theorem transportedObs_measurable (f : Y → X) (hf : Measurable f) (ν : ObsEnv X) :
    (transportedObs f ν).IsMeasurable := by
  intro τ
  refine (ν τ).measurable.comp (Measurable.prodMk (measurable_pi_lambda _ ?_)
    (hf.comp (measurable_snd.comp measurable_snd)))
  intro i
  exact (hf.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))

private def liftedHistory (f : Y → X) (A : BilateralProfitMHR.QueryAlg Y Ω) (ω : Ω)
    {τ : ℕ} (ys : Fin τ → ℝ) : Fin τ → X × ℝ :=
  fun i => (f (A.pastQueries ω ys i), ys i)

private theorem liftedHistory_snoc (f : Y → X) (A : BilateralProfitMHR.QueryAlg Y Ω) (ω : Ω)
    {τ : ℕ} (ys : Fin τ → ℝ) (y : ℝ) :
    liftedHistory f A ω (Fin.snoc ys y) =
      Fin.snoc (liftedHistory f A ω ys) (f (A.query τ ω ys), y) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [liftedHistory, BilateralProfitMHR.QueryAlg.pastQueries, Fin.snoc_last]
    congr 3
    funext k
    change Fin.snoc (α := fun _ => ℝ) ys y k.castSucc = ys k
    simp only [Fin.snoc_castSucc]
  · simp only [liftedHistory, BilateralProfitMHR.QueryAlg.pastQueries, Fin.snoc_castSucc]
    congr 3
    funext k
    change Fin.snoc (α := fun _ => ℝ) ys y (Fin.castLE j.isLt.le k).castSucc =
      ys (Fin.castLE j.isLt.le k)
    simp only [Fin.snoc_castSucc]

private theorem go_eq_cumLoss (f : Y → X) (hf : Measurable f)
    (A : BilateralProfitMHR.QueryAlg Y Ω) (ν : ObsEnv X) (c : X → ℝ≥0∞)
    (ω : Ω) (n τ : ℕ) (ys : Fin τ → ℝ) :
    (transportQueryAlg f hf A).go ν c (fun _ _ => 0) n τ ω (liftedHistory f A ω ys) =
      BilateralProfitMHR.cumLoss A (transportedObs f ν) (c ∘ f) ω n τ ys := by
  induction n generalizing τ with
  | zero => rfl
  | succ n ih =>
    simp only [BanditAlg.go, BilateralProfitMHR.cumLoss]
    change c (f (A.query τ ω ys)) +
      (∫⁻ y, (transportQueryAlg f hf A).go ν c (fun _ _ => 0) n (τ+1) ω
        (Fin.snoc (liftedHistory f A ω ys) (f (A.query τ ω ys), y))
        ∂(transportedObs f ν τ (A.pastQueries ω ys) ys (A.query τ ω ys))) = _
    congr 1
    exact lintegral_congr fun y => (liftedHistory_snoc f A ω ys y).symm ▸ ih (τ+1) (Fin.snoc ys y)

end History

private theorem corollary_3_1 :
    ∀ (k : ℕ) (ℓ : ℝ), 0 < ℓ → ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (K : Set (Fin d → ℝ)), K.Nonempty → IsCompact K → Convex ℝ K →
      Module.finrank ℝ (vectorSpan ℝ K) ≤ k →
      ∀ (b : ℝ) (γ : NNReal) (n : ℕ), 2 ≤ n →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (alg : BanditAlg (Fin d → ℝ) Ω),
        alg.QueriesIn K ∧
        ∀ L : (Fin d → ℝ) → ℝ, ContinuousOn L K → ConvexOn ℝ K L →
          (∀ x ∈ K, b ≤ L x ∧ L x ≤ b + ℓ) →
          ∀ ν : ObsEnv (Fin d → ℝ), ν.MeanOn L K →
            (∀ τ h, ∀ x ∈ K,
              HighDimProb.Concentration.subgaussianNorm (ν τ (h, x)) (fun y => y - L x) ≤ γ) →
            alg.regret ν Pω n L K ≤
              ENNReal.ofReal (C * (1 + γ) * Real.sqrt n * Real.log n ^ 2) := by
  classical
  intro k ℓ hℓ
  choose C hC using fun m : ℕ => BilateralProfitMHR.corollary_3_1 m ℓ hℓ
  let C' : ℝ := 1 + ∑ m ∈ Finset.range (k+1), max 0 (C m)
  have hC' : 0 < C' := by
    dsimp [C']
    have hh : 0 ≤ ∑ m ∈ Finset.range (k+1), max 0 (C m) :=
      Finset.sum_nonneg fun m _ => le_max_left _ _
    linarith
  refine ⟨C', hC', ?_⟩
  intro d K hne hc hcv hdim b γ n hn
  obtain ⟨m, hm, S, f, hSne, hSc, hSv, hf, himage⟩ :=
    coordinates_in_affine_span K hne hc hcv hdim
  obtain ⟨Ω, mΩ, Pω, hPω, A, hA, hreg⟩ :=
    hC m S hSne hSc hSv b γ γ.2 n hn
  have hmap : MapsTo f S K := fun x hx => himage ▸ mem_image_of_mem f hx
  refine ⟨Ω, mΩ, Pω, hPω, transportQueryAlg f hf.measurable A,
    fun τ ω h => hmap (hA τ ω _), ?_⟩
  intro L hL hLv hRange ν hMean hNorm
  let L' : EuclideanSpace ℝ (Fin m) → ℝ := L ∘ f
  have hL' : ContinuousOn L' S := hL.comp hf.continuousOn hmap
  have hLv' : ConvexOn ℝ S L' := (hLv.comp_affineMap f).subset hmap hSv
  have hRange' : ∀ x ∈ S, L' x ∈ Icc b (b+ℓ) :=
    fun x hx => hRange (f x) (hmap hx)
  have hNoise : BilateralProfitMHR.NoiseCond S L' γ (transportedObs f ν) := by
    intro τ xs ys x _ hx
    haveI : IsMarkovKernel (ν τ) := hMean.1 τ
    have hPre := hMean.2 τ (fun i => (f (xs i), ys i)) (f x) (hmap hx)
    exact ⟨by unfold transportedObs; infer_instance, hPre.1, hPre.2,
      by simpa [L', transportedObs] using hNorm τ (fun i => (f (xs i), ys i)) (f x) (hmap hx)⟩
  have himg : L' '' S = L '' K := by
    change (L ∘ f) '' S = L '' K
    exact (Set.image_image L f S).symm.trans (congrArg (fun a => L '' a) himage)
  have hEqual :
      (transportQueryAlg f hf.measurable A).regret ν Pω n L K =
        BilateralProfitMHR.expectedCumLoss A Pω (transportedObs f ν)
          (fun x => ENNReal.ofReal (L' x - sInf (L' '' S))) n := by
    unfold BanditAlg.regret BilateralProfitMHR.expectedCumLoss
    rw [himg]
    apply lintegral_congr
    intro ω
    have he : liftedHistory f A ω (Fin.elim0 : Fin 0 → ℝ) = Fin.elim0 :=
      Subsingleton.elim _ _
    exact he ▸ go_eq_cumLoss f hf.measurable A ν
      (fun x => ENNReal.ofReal (L x - sInf (L '' K))) ω n 0 Fin.elim0
  rw [hEqual]
  refine (hreg L' hL' hLv' hRange' (transportedObs f ν)
    (transportedObs_measurable f hf.measurable ν) hNoise).trans ?_
  have hCm : C m ≤ C' := by
    have hm' : m ∈ Finset.range (k+1) := Finset.mem_range.mpr (by omega)
    have hs : max 0 (C m) ≤ ∑ i ∈ Finset.range (k+1), max 0 (C i) :=
      Finset.single_le_sum (f := fun i => max 0 (C i)) (fun i _ => le_max_left _ _) hm'
    dsimp [C']
    linarith [le_max_right 0 (C m)]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCm (by positivity))
        (Real.sqrt_nonneg _)) (sq_nonneg _))

end BilateralProfitRegular
end
end BundlePart000

open BilateralProfitRegular
open MeasureTheory

theorem solution :
    ∀ (k : ℕ) (ℓ : ℝ), 0 < ℓ → ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (K : Set (Fin d → ℝ)), K.Nonempty → IsCompact K → Convex ℝ K →
      Module.finrank ℝ (vectorSpan ℝ K) ≤ k →
      ∀ (b : ℝ) (γ : NNReal) (n : ℕ), 2 ≤ n →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (alg : BanditAlg (Fin d → ℝ) Ω),
        alg.QueriesIn K ∧
        ∀ L : (Fin d → ℝ) → ℝ, ContinuousOn L K → ConvexOn ℝ K L →
          (∀ x ∈ K, b ≤ L x ∧ L x ≤ b + ℓ) →
          ∀ ν : ObsEnv (Fin d → ℝ), ν.MeanOn L K →
            (∀ τ h, ∀ x ∈ K,
              HighDimProb.Concentration.subgaussianNorm (ν τ (h, x)) (fun y => y - L x) ≤ γ) →
            alg.regret ν Pω n L K ≤
              ENNReal.ofReal (C * (1 + γ) * Real.sqrt n * Real.log n ^ 2) := by
  exact BilateralProfitRegular.corollary_3_1
