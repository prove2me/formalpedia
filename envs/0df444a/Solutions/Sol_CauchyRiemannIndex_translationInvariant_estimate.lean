-- Prove2me | solution 1 for CauchyRiemannIndex.translationInvariant_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T22:45:30.699147+00:00
-- url     : https://prove2.me/submissions/33bbccae-4827-4f73-a8fa-4c48b3fab342

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_derivative_estimate
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_Lp_bound
import Theorems.Thm_CauchyRiemannIndex_crOp_formalAdjoint
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_denseRange

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

section Bridge

noncomputable section


variable {n : ℕ}

/-- Matrices as continuous linear maps of `ℝ²ⁿ`, continuously in the matrix. -/
def matCLM (n : ℕ) : Mat n →ₗ[ℝ] (Vec n →L[ℝ] Vec n) :=
  (LinearMap.toContinuousLinearMap : (Vec n →ₗ[ℝ] Vec n) ≃ₗ[ℝ] (Vec n →L[ℝ] Vec n)).toLinearMap ∘ₗ
    (Matrix.toEuclideanLin : Mat n ≃ₗ[ℝ] (Vec n →ₗ[ℝ] Vec n)).toLinearMap

lemma matCLM_apply (A : Mat n) (v : Vec n) : matCLM n A v = Matrix.toEuclideanLin A v := rfl

lemma continuous_matCLM : Continuous (matCLM n) := LinearMap.continuous_of_finiteDimensional _

/-- A uniform operator bound for a continuous `1`-periodic matrix loop. -/
lemma exists_bound_loop (Sinf : ℝ → Mat n) (hc : Continuous Sinf) (hper : Function.Periodic Sinf 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t (v : Vec n), ‖Matrix.toEuclideanLin (Sinf t) v‖ ≤ M * ‖v‖ := by
  have hg : Continuous fun t => matCLM n (Sinf t) := continuous_matCLM.comp hc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t v => ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
  rw [← matCLM_apply, hty]
  calc ‖matCLM n (Sinf y) v‖ ≤ ‖matCLM n (Sinf y)‖ * ‖v‖ := (matCLM n (Sinf y)).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by
      gcongr
      exact (hC y (Set.Ico_subset_Icc_self hy)).trans (le_max_left _ _)

lemma exists_bound_mat (A : Mat n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : Vec n), ‖Matrix.toEuclideanLin A v‖ ≤ M * ‖v‖ :=
  ⟨‖matCLM n A‖, norm_nonneg _, fun v => (matCLM n A).le_opNorm v⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous map on `ℝ × ℝ` vanishing for large `|s|` is in `L^p` of the strip. -/
lemma memLp_of_vanish {E : Type*} [NormedAddCommGroup E] (g : ℝ × ℝ → E) (hg : Continuous g)
    (R : ℝ) (hR : ∀ s t, R < |s| → g (s, t) = 0) : MemLp g p cylMeasure := by
  set K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : K.indicator g =ᵐ[cylMeasure] g := by
    unfold cylMeasure
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ico) ?_
    rintro ⟨s, t⟩ ⟨-, ht⟩
    by_cases hx : (s, t) ∈ K
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have : R < |s| := by
        by_contra h
        push_neg at h
        exact hx ⟨abs_le.1 h, Set.Ico_subset_Icc_self ht⟩
      exact (hR s t this).symm
  refine (memLp_congr_ae hae).1 ((memLp_indicator_iff_restrict hKm).2 ?_)
  haveI : IsFiniteMeasure (cylMeasure.restrict K) := by
    refine isFiniteMeasure_restrict.2 (ne_of_lt (lt_of_le_of_lt ?_ (hKc.measure_lt_top (μ := (volume : Measure (ℝ × ℝ))))))
    exact Measure.le_iff'.1 Measure.restrict_le_self K
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C (ae_restrict_of_forall_mem hKm hC)

lemma partialS_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialS u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialS, hev.fderiv_eq]

lemma partialT_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialT u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialT, hev.fderiv_eq]

lemma IsTestSection.continuous {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Continuous u :=
  hu.1.continuous

lemma IsTestSection.continuous_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialS u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.continuous_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialT u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.memLp {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : MemLp u p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish u hu.continuous R hR

lemma IsTestSection.memLp_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialS u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialS R fun s t hs => partialS_eq_zero R hR hs

lemma IsTestSection.memLp_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialT u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialT R fun s t hs => partialT_eq_zero R hR hs

lemma IsTestSection.sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u - v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.sub hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u + v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.add hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    IsTestSection (c • u) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  refine ⟨ContDiff.const_smul c hu.1, fun s t => by simp [hu.2.1], R₁, fun s t hs => ?_⟩
  simp [h₁ s t hs]

lemma isTestSection_zero : IsTestSection (0 : ℝ × ℝ → Vec n) :=
  ⟨contDiff_const, fun _ _ => rfl, 0, fun _ _ _ => rfl⟩

lemma partialS_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u + v) = partialS u + partialS v := by
  funext x
  simp only [partialS, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u + v) = partialT u + partialT v := by
  funext x
  simp only [partialT, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u - v) = partialS u - partialS v := by
  funext x
  simp only [partialS, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u - v) = partialT u - partialT v := by
  funext x
  simp only [partialT, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialS (c • u) = c • partialS u := by
  funext x
  simp only [partialS, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialT_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialT (c • u) = c • partialT u := by
  funext x
  simp only [partialT, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialS_zero : partialS (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialS]

lemma partialT_zero : partialT (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialT]

end

end Bridge

end CauchyRiemannIndex

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ### The reflection `(s, t) ↦ (-s, t)` -/

/-- The reflection `(s, t) ↦ (-s, t)` of the cylinder. -/
def reflL : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (-(ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] lemma reflL_apply (x : ℝ × ℝ) : reflL x = (-x.1, x.2) := rfl

lemma reflL_reflL (x : ℝ × ℝ) : reflL (reflL x) = x := by simp

lemma measurePreserving_reflL : MeasurePreserving reflL cylMeasure cylMeasure := by
  have h1 : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) id) (volume : Measure (ℝ × ℝ)) volume :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id volume)
  have h2 : (reflL : ℝ × ℝ → ℝ × ℝ) = Prod.map (Neg.neg : ℝ → ℝ) id := by
    funext x; rfl
  have hs : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Ico (0 : ℝ) 1) :=
    MeasurableSet.univ.prod measurableSet_Ico
  have h3 := h1.restrict_preimage hs
  have hpre : Prod.map (Neg.neg : ℝ → ℝ) id ⁻¹' ((Set.univ : Set ℝ) ×ˢ Set.Ico (0 : ℝ) 1) =
      (Set.univ : Set ℝ) ×ˢ Set.Ico (0 : ℝ) 1 := by
    ext x; simp
  rw [hpre] at h3
  rw [h2]
  exact h3

lemma IsTestSection.comp_reflL {w : ℝ × ℝ → Vec n} (hw : IsTestSection w) :
    IsTestSection (w ∘ reflL) := by
  obtain ⟨R, hR⟩ := hw.2.2
  refine ⟨hw.1.comp reflL.contDiff, fun s t => ?_, R, fun s t hs => ?_⟩
  · simp [hw.2.1]
  · simp only [Function.comp_apply, reflL_apply]
    exact hR (-s) t (by simpa using hs)

lemma partialS_comp_reflL {w : ℝ × ℝ → Vec n} (hw : IsTestSection w) (x : ℝ × ℝ) :
    partialS (w ∘ reflL) x = -partialS w (reflL x) := by
  have hd : DifferentiableAt ℝ w (reflL x) :=
    (hw.1.differentiable (by simp)).differentiableAt
  unfold partialS
  rw [fderiv_comp x hd reflL.differentiableAt, ContinuousLinearMap.fderiv]
  have : reflL ((1 : ℝ), (0 : ℝ)) = -((1 : ℝ), (0 : ℝ)) := by simp
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, this, map_neg]

lemma partialT_comp_reflL {w : ℝ × ℝ → Vec n} (hw : IsTestSection w) (x : ℝ × ℝ) :
    partialT (w ∘ reflL) x = partialT w (reflL x) := by
  have hd : DifferentiableAt ℝ w (reflL x) :=
    (hw.1.differentiable (by simp)).differentiableAt
  unfold partialT
  rw [fderiv_comp x hd reflL.differentiableAt, ContinuousLinearMap.fderiv]
  have : reflL ((0 : ℝ), (1 : ℝ)) = ((0 : ℝ), (1 : ℝ)) := by simp
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, this]

/-- `∫ ⟨D u, w ∘ ρ⟩ = ∫ ⟨u, (D w) ∘ ρ⟩` for the reflection `ρ(s, t) = (-s, t)`. -/
lemma integral_inner_crOp_reflL (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    {u w : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hw : IsTestSection w) :
    ∫ x, inner ℝ (crOp (fun x : ℝ × ℝ => Sinf x.2) u x) (w (reflL x)) ∂cylMeasure =
      ∫ x, inner ℝ (u x) (crOp (fun x : ℝ × ℝ => Sinf x.2) w (reflL x)) ∂cylMeasure := by
  have h := crOp_formalAdjoint n (fun x : ℝ × ℝ => Sinf x.2) (hS.1.comp continuous_snd) u
    (w ∘ reflL) hu hw.comp_reflL
  simp only [Function.comp_apply] at h
  rw [h]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  congr 1
  rw [partialS_comp_reflL hw, partialT_comp_reflL hw, (hS.2.2 x.2).eq]
  simp [crOp]

/-! ### Continuity and integrability -/

lemma continuous_crOp (Sinf : ℝ → Mat n) (hc : Continuous Sinf) {w : ℝ × ℝ → Vec n}
    (hw : IsTestSection w) : Continuous (crOp (fun x : ℝ × ℝ => Sinf x.2) w) := by
  have h1 : Continuous fun x : ℝ × ℝ => matCLM n (J₀ n) (partialT w x) :=
    (matCLM n (J₀ n)).continuous.comp hw.continuous_partialT
  have h2 : Continuous fun x : ℝ × ℝ => matCLM n (Sinf x.2) (w x) :=
    (continuous_matCLM.comp (hc.comp continuous_snd)).clm_apply hw.continuous
  exact (hw.continuous_partialS.add h1).add h2

lemma crOp_eq_zero (Sinf : ℝ → Mat n) {w : ℝ × ℝ → Vec n} (R : ℝ)
    (hR : ∀ s t, R < |s| → w (s, t) = 0) {s t : ℝ} (hs : R < |s|) :
    crOp (fun x : ℝ × ℝ => Sinf x.2) w (s, t) = 0 := by
  simp [crOp, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs, hR s t hs]

/-! ### Hölder for the pointwise inner product -/

lemma enorm_integral_inner_le {μ : Measure (ℝ × ℝ)} {f g : ℝ × ℝ → Vec n}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) {p q : ℝ≥0∞}
    [ENNReal.HolderConjugate p q] :
    ‖∫ x, inner ℝ (f x) (g x) ∂μ‖ₑ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm]
  have := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (μ := μ) (p := p) (q := q) (r := 1) hf hg
    (fun a b : Vec n => inner ℝ a b) 1
    (ae_of_all _ fun x => by simpa using norm_inner_le_norm (𝕜 := ℝ) (f x) (g x))
  simpa using this

/-! ### Duality: the bound for `p` from the bound and density for the dual exponent -/

lemma rpow_sub_two_mul_sq {a P : ℝ} (ha : 0 ≤ a) (hP : 0 < P) :
    a ^ (P - 2) * a ^ 2 = a ^ P := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [Real.zero_rpow hP.ne']
  · rw [← Real.rpow_natCast, ← Real.rpow_add ha]; norm_num

lemma rpow_sub_two_mul {a P : ℝ} (ha : 0 ≤ a) (hP : 1 < P) :
    a ^ (P - 2) * a = a ^ (P - 1) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [Real.zero_rpow (by linarith : P - 1 ≠ 0)]
  · rw [← Real.rpow_add_one ha.ne']; ring_nf

theorem Lp_bound_of_dual (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p)
    (hp' : p ≠ ⊤) (c₂ : ℝ≥0)
    (hbound : ∀ w : ℝ × ℝ → Vec n, IsTestSection w →
      eLpNorm w (ENNReal.ofReal (p.toReal / (p.toReal - 1))) cylMeasure ≤
        c₂ * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) w)
          (ENNReal.ofReal (p.toReal / (p.toReal - 1))) cylMeasure)
    [Fact (1 ≤ ENNReal.ofReal (p.toReal / (p.toReal - 1)))]
    (hdense : ∀ f : LpCyl n (ENNReal.ofReal (p.toReal / (p.toReal - 1))), ∀ ε : ℝ, 0 < ε →
      ∃ w : ℝ × ℝ → Vec n, IsTestSection w ∧
        eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) w - ⇑f)
          (ENNReal.ofReal (p.toReal / (p.toReal - 1))) cylMeasure < ENNReal.ofReal ε)
    (u : ℝ × ℝ → Vec n) (hu : IsTestSection u) :
    eLpNorm u p cylMeasure ≤ c₂ * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure := by
  set P := p.toReal with hPdef
  set Q := P / (P - 1) with hQdef
  set q := ENNReal.ofReal Q with hqdef
  set D := fun v : ℝ × ℝ → Vec n => crOp (fun x : ℝ × ℝ => Sinf x.2) v with hDdef
  have hP1 : 1 < P := by
    have := (ENNReal.toReal_lt_toReal (by simp) hp').2 hp
    simpa using this
  have hP0 : 0 < P := by linarith
  have hpP : p = ENNReal.ofReal P := (ENNReal.ofReal_toReal hp').symm
  have hPQ : P.HolderConjugate Q := Real.HolderConjugate.conjExponent hP1
  haveI hpq : ENNReal.HolderConjugate p q := by rw [hpP]; exact hPQ.ennrealOfReal
  have hQ0 : 0 < Q := hPQ.symm.pos
  set N := eLpNorm u p cylMeasure with hNdef
  set F := eLpNorm (D u) p cylMeasure with hFdef
  have hNtop : N < ⊤ := (hu.memLp (p := p)).eLpNorm_lt_top
  -- the dual function `g = |u|^{P-2} u`
  set g : ℝ × ℝ → Vec n := fun x => ‖u x‖ ^ (P - 2) • u x with hgdef
  have hg_meas : AEStronglyMeasurable g cylMeasure :=
    (((hu.continuous.measurable.norm.pow_const (P - 2)).smul
      hu.continuous.measurable)).aestronglyMeasurable
  have hg_inner : ∀ x, inner ℝ (u x) (g x) = ‖u x‖ ^ P := by
    intro x
    simp only [hgdef, inner_smul_right, real_inner_self_eq_norm_sq]
    exact rpow_sub_two_mul_sq (norm_nonneg _) hP0
  have hg_norm : ∀ x, ‖g x‖ = ‖u x‖ ^ (P - 1) := by
    intro x
    simp only [hgdef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact rpow_sub_two_mul (norm_nonneg _) hP1
  have hgq : eLpNorm g q cylMeasure = N ^ (P - 1) := by
    rw [eLpNorm_congr_norm_ae (ae_of_all _ fun x => (hg_norm x).trans
      (Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)).symm)]
    rw [eLpNorm_norm_rpow u (by linarith : (0 : ℝ) < P - 1)]
    congr 2
    rw [hqdef, ← ENNReal.ofReal_mul hQ0.le, hpP, hQdef, div_mul_cancel₀ _ (by linarith)]
  have hg_memLp : MemLp g q cylMeasure :=
    ⟨hg_meas, by rw [hgq]; exact ENNReal.rpow_lt_top_of_nonneg (by linarith) hNtop.ne⟩
  -- `∫ ⟨u, g⟩ = N ^ P`
  have hint_norm : Integrable (fun x => ‖u x‖ ^ P) cylMeasure :=
    (hu.memLp (p := p)).integrable_norm_rpow (by positivity) hp'
  have hNP : ENNReal.ofReal (∫ x, inner ℝ (u x) (g x) ∂cylMeasure) = N ^ P := by
    simp_rw [hg_inner]
    rw [ofReal_integral_eq_lintegral_ofReal hint_norm
      (ae_of_all _ fun x => Real.rpow_nonneg (norm_nonneg _) _)]
    rw [hNdef, eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) hp', ← ENNReal.rpow_mul,
      ← hPdef, one_div_mul_cancel hP0.ne', ENNReal.rpow_one]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hP0.le]
  -- the reflected dual function as an element of `L^q`
  have hgr_memLp : MemLp (g ∘ reflL) q cylMeasure :=
    hg_memLp.comp_measurePreserving measurePreserving_reflL
  set h : LpCyl n q := hgr_memLp.toLp (g ∘ reflL) with hhdef
  have hh_ae : (h : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g ∘ reflL := hgr_memLp.coeFn_toLp
  have hhq : eLpNorm h q cylMeasure = N ^ (P - 1) := by
    rw [eLpNorm_congr_ae hh_ae, eLpNorm_comp_measurePreserving hg_meas measurePreserving_reflL,
      hgq]
  -- the main inequality, for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε →
      N ^ P ≤ F * (c₂ * (N ^ (P - 1) + ENNReal.ofReal ε)) + N * ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨w, hw, hwε⟩ := hdense h ε hε
    obtain ⟨Ru, hRu⟩ := hu.2.2
    obtain ⟨Rw, hRw⟩ := hw.2.2
    have hDw_cont : Continuous (D w) := continuous_crOp Sinf hS.1 hw
    have hDwr_meas : AEStronglyMeasurable (fun x => D w (reflL x)) cylMeasure :=
      (hDw_cont.comp reflL.continuous).aestronglyMeasurable
    -- integrability of `⟨u, (D w) ∘ ρ⟩`
    have hI1 : Integrable (fun x => inner ℝ (u x) (D w (reflL x))) cylMeasure := by
      rw [← memLp_one_iff_integrable]
      refine memLp_of_vanish _ ((hu.continuous.inner (hDw_cont.comp reflL.continuous))) Ru
        fun s t hs => by simp [hRu s t hs]
    have hI0 : Integrable (fun x => inner ℝ (u x) (g x)) cylMeasure :=
      hint_norm.congr (ae_of_all _ fun x => (hg_inner x).symm)
    have hsplit : ∫ x, inner ℝ (u x) (g x) ∂cylMeasure =
        ∫ x, inner ℝ (D u x) (w (reflL x)) ∂cylMeasure +
          ∫ x, inner ℝ (u x) (g x - D w (reflL x)) ∂cylMeasure := by
      rw [integral_inner_crOp_reflL Sinf hS hu hw]
      simp_rw [inner_sub_right]
      rw [integral_sub hI0 hI1]
      ring
    -- Hölder on both pieces
    have hA : ‖∫ x, inner ℝ (D u x) (w (reflL x)) ∂cylMeasure‖ₑ ≤
        F * eLpNorm w q cylMeasure := by
      have := enorm_integral_inner_le (μ := cylMeasure) (p := p) (q := q)
        (continuous_crOp Sinf hS.1 hu).aestronglyMeasurable
        (hw.continuous.comp reflL.continuous).aestronglyMeasurable
      refine this.trans (le_of_eq ?_)
      congr 1
      exact eLpNorm_comp_measurePreserving hw.continuous.aestronglyMeasurable
        measurePreserving_reflL
    have hB : ‖∫ x, inner ℝ (u x) (g x - D w (reflL x)) ∂cylMeasure‖ₑ ≤
        N * ENNReal.ofReal ε := by
      refine (enorm_integral_inner_le (μ := cylMeasure) (p := p) (q := q)
        hu.continuous.aestronglyMeasurable (hg_meas.sub hDwr_meas)).trans ?_
      gcongr
      have he : (g - fun x => D w (reflL x)) = (fun y => g (reflL y) - D w y) ∘ reflL := by
        funext x; simp [reflL_reflL]
      rw [he, eLpNorm_comp_measurePreserving (g := fun y => g (reflL y) - D w y)
        ((hg_meas.comp_measurePreserving measurePreserving_reflL).sub
          hDw_cont.aestronglyMeasurable) measurePreserving_reflL]
      have he2 : (fun y => g (reflL y) - D w y) =ᵐ[cylMeasure] -(D w - ⇑h) := by
        filter_upwards [hh_ae] with y hy
        simp [hy]
      rw [eLpNorm_congr_ae he2, eLpNorm_neg]
      exact hwε.le
    -- the bound for `w`
    have hwq : eLpNorm w q cylMeasure ≤ c₂ * (N ^ (P - 1) + ENNReal.ofReal ε) := by
      refine (hbound w hw).trans ?_
      gcongr
      have hDw_meas : AEStronglyMeasurable (D w - ⇑h) cylMeasure :=
        hDw_cont.aestronglyMeasurable.sub (Lp.aestronglyMeasurable h)
      calc eLpNorm (D w) q cylMeasure = eLpNorm ((D w - ⇑h) + ⇑h) q cylMeasure := by
            congr 1; abel
        _ ≤ eLpNorm (D w - ⇑h) q cylMeasure + eLpNorm h q cylMeasure :=
            eLpNorm_add_le hDw_meas (Lp.aestronglyMeasurable h) Fact.out
        _ ≤ ENNReal.ofReal ε + N ^ (P - 1) := by rw [hhq]; gcongr
        _ = N ^ (P - 1) + ENNReal.ofReal ε := add_comm _ _
    calc N ^ P = ENNReal.ofReal (∫ x, inner ℝ (u x) (g x) ∂cylMeasure) := hNP.symm
      _ ≤ ‖∫ x, inner ℝ (u x) (g x) ∂cylMeasure‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ _ := by rw [hsplit]; exact enorm_add_le _ _
      _ ≤ F * eLpNorm w q cylMeasure + N * ENNReal.ofReal ε := add_le_add hA hB
      _ ≤ F * (c₂ * (N ^ (P - 1) + ENNReal.ofReal ε)) + N * ENNReal.ofReal ε := by
          gcongr
  -- let `ε → 0`
  have hFtop : F < ⊤ := (memLp_of_vanish (p := p) _ (continuous_crOp Sinf hS.1 hu)
    hu.2.2.choose fun s t hs => crOp_eq_zero Sinf _ hu.2.2.choose_spec hs).eLpNorm_lt_top
  have hlim : N ^ P ≤ c₂ * F * N ^ (P - 1) := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    set K : ℝ≥0∞ := F * c₂ + N with hKdef
    have hKtop : K ≠ ⊤ := by
      rw [hKdef]; exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hFtop.ne ENNReal.coe_ne_top,
        hNtop.ne⟩
    set ε : ℝ := (δ : ℝ) / (K.toReal + 1) with hεdef
    have hε : 0 < ε := div_pos (by exact_mod_cast hδ) (by positivity)
    have hKε : K * ENNReal.ofReal ε ≤ δ := by
      rw [← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, hεdef,
        ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [ENNReal.toReal_nonneg (a := K), δ.coe_nonneg]
    calc N ^ P ≤ F * (c₂ * (N ^ (P - 1) + ENNReal.ofReal ε)) + N * ENNReal.ofReal ε := key ε hε
      _ = c₂ * F * N ^ (P - 1) + K * ENNReal.ofReal ε := by rw [hKdef]; ring
      _ ≤ c₂ * F * N ^ (P - 1) + δ := by gcongr
  -- cancel `N ^ (P - 1)`
  rcases eq_or_ne N 0 with hN0 | hN0
  · rw [hN0]; simp
  have hpow_ne0 : N ^ (P - 1) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hN0, hNtop.ne, show 0 < P - 1 by linarith]
  have hpow_top : N ^ (P - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hNtop.ne
  have hsplitP : N ^ P = N * N ^ (P - 1) := by
    conv_lhs => rw [show P = 1 + (P - 1) by ring]
    rw [ENNReal.rpow_add _ _ hN0 hNtop.ne, ENNReal.rpow_one]
  rw [hsplitP] at hlim
  exact (ENNReal.mul_le_mul_iff_left hpow_ne0 hpow_top).1 hlim

end

end CauchyRiemannIndex

open CauchyRiemannIndex MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure := by
  -- the zero-order bound
  have h0 : ∃ c₀ : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm u p cylMeasure ≤ c₀ * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure := by
    by_cases h2 : 2 ≤ p
    · exact translationInvariant_Lp_bound n p h2 hp' Sinf hS hnd
    · push_neg at h2
      set P := p.toReal with hPdef
      have hP1 : 1 < P := by
        have := (ENNReal.toReal_lt_toReal (by simp) hp').2 hp
        simpa using this
      have hP2 : P < 2 := by
        have := (ENNReal.toReal_lt_toReal hp' (by simp)).2 h2
        simpa using this
      have hQ2 : 2 ≤ P / (P - 1) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      have hq2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (P / (P - 1)) := by
        rw [← ENNReal.ofReal_ofNat 2]; exact ENNReal.ofReal_le_ofReal hQ2
      have hqtop : ENNReal.ofReal (P / (P - 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
      haveI : Fact (1 ≤ ENNReal.ofReal (P / (P - 1))) := ⟨le_trans (by norm_num) hq2⟩
      obtain ⟨c₂, hc₂⟩ := translationInvariant_Lp_bound n _ hq2 hqtop Sinf hS hnd
      refine ⟨c₂, fun u hu => Lp_bound_of_dual Sinf hS p hp hp' c₂ hc₂ ?_ u hu⟩
      intro f ε hε
      exact translationInvariant_denseRange n _ (lt_of_lt_of_le (by norm_num) hq2) hqtop Sinf
        hS hnd f ε hε
  obtain ⟨c₀, hc₀⟩ := h0
  obtain ⟨c₁, hc₁⟩ := translationInvariant_derivative_estimate n p hp hp' Sinf hS.1 hS.2.1
  refine ⟨c₁ + c₁ * c₀, fun u hu => ?_⟩
  calc w1pNorm p u ≤ c₁ * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure +
        c₁ * eLpNorm u p cylMeasure := hc₁ u hu
    _ ≤ c₁ * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure +
        c₁ * (c₀ * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure) := by
        gcongr; exact hc₀ u hu
    _ = ((c₁ + c₁ * c₀ : ℝ≥0) : ℝ≥0∞) *
        eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) p cylMeasure := by
        push_cast; ring
