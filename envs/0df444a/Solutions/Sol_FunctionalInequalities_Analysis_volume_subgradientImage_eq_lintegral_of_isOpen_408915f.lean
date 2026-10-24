-- Prove2me | solution 1 for FunctionalInequalities.Analysis.volume_subgradientImage_eq_lintegral_of_isOpen_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:14:21.965243+00:00
-- url     : https://prove2.me/submissions/5f984775-a039-49be-8ecd-5d633564dbc2

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_lintegral_subgradientImage_eq_of_map_gradient_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_subgradient_mem_of_ae_gradient_mem_408915f

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT14DAlexandrovIdentityOpen
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.t14d_isClosed_subgradientImage {u : E → ℝ} (hu : Continuous u)
    {S : Set E} (hS : IsCompact S) :
    IsClosed (subgradientImage u S) := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let C : Set (S × E) :=
    ⋂ y : E, {q | u q.1.1 + ⟪q.2, y - q.1.1⟫ ≤ u y}
  have hC : IsClosed C := by
    refine isClosed_iInter fun y => ?_
    exact isClosed_le
      ((hu.comp (continuous_subtype_val.comp continuous_fst)).add
        (continuous_snd.inner
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst))))
      continuous_const
  have himage : Prod.snd '' C = subgradientImage u S := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hq, rfl⟩
      refine ⟨x.1, x.2, ?_⟩
      exact mem_iInter.mp hq
    · rintro ⟨x, hx, hp⟩
      refine ⟨(⟨x, hx⟩, p), ?_, rfl⟩
      exact mem_iInter.mpr hp
  rw [← himage]
  exact isClosedMap_snd_of_compactSpace C hC
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Alexandrov identity on open sets for the moment potential** (weak Letwin route):
if `u` is convex, Lipschitz, `ν = e^{-u} dx` is normalised and `ν.map ∇u = μ = 1_K e^{-V} dx` for a closed convex
`K` and a measurable `V`, then the subgradient image of every open `G` has volume `∫_G e^{-u + V(∇u)}`. -/
theorem solution [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K) {V : E → ℝ} (hV : Measurable V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    {G : Set E} (hG : IsOpen G) :
    (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) =
      ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + V (gradient u x))) ∂(volume : Measure E) := by
  classical
  let ρ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-u x))
  let f : E → ℝ≥0∞ := K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))
  let g : E → ℝ≥0∞ := K.indicator fun p => ENNReal.ofReal (Real.exp (V p))
  let F : E → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-u x + V (gradient u x)))
  have hρ : Measurable ρ := hu.continuous.measurable.neg.exp.ennreal_ofReal
  have hf : Measurable f :=
    hV.neg.exp.ennreal_ofReal.indicator hK.measurableSet
  have hg : Measurable g :=
    hV.exp.ennreal_ofReal.indicator hK.measurableSet
  have hgrad : Measurable (gradient u) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
      (measurable_fderiv ℝ u)
  have htilt : (volume : Measure E).tilted (-u) = volume.withDensity ρ := by
    change (volume : Measure E).withDensity
      (fun x => ENNReal.ofReal
        (Real.exp (-u x) / ∫ y, Real.exp (-u y) ∂(volume : Measure E))) =
      volume.withDensity ρ
    simp only [hnorm, div_one, ρ]
  have hmap' :
      ((volume : Measure E).withDensity ρ).map (gradient u) =
        volume.withDensity f := by
    rw [← htilt]
    exact hmap
  have hμK : ∀ᵐ p ∂(volume : Measure E).withDensity f, p ∈ K := by
    apply (ae_withDensity_iff hf).2
    exact Filter.Eventually.of_forall fun p hp => by
      by_contra h
      exact hp (Set.indicator_of_notMem h _)
  have hνK :
      ∀ᵐ x ∂(volume : Measure E).withDensity ρ, gradient u x ∈ K := by
    apply ae_of_ae_map hgrad.aemeasurable
    rw [hmap']
    exact hμK
  have hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K := by
    have h := (ae_withDensity_iff hρ).1 hνK
    filter_upwards [h] with x hx
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (-u x))))
  have hsub (S : Set E) : FunctionalInequalities.Analysis.subgradientImage u S ⊆ K := by
    rintro p ⟨x, _, hp⟩
    exact FunctionalInequalities.Analysis.subgradient_mem_of_ae_gradient_mem_408915f hu hconv hK hKc hae hp
  have hcancel (p : E) (hp : p ∈ K) : (f * g) p = 1 := by
    change
      (K.indicator (fun q => ENNReal.ofReal (Real.exp (-V q))) p) *
        (K.indicator (fun q => ENNReal.ofReal (Real.exp (V q))) p) = 1
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]
  have hprod :
      (fun x => (ρ * (g ∘ gradient u)) x) =ᵐ[volume] F := by
    filter_upwards [hae] with x hx
    change ENNReal.ofReal (Real.exp (-u x)) *
      (K.indicator (fun p => ENNReal.ofReal (Real.exp (V p))) (gradient u x)) =
        ENNReal.ofReal (Real.exp (-u x + V (gradient u x)))
    rw [Set.indicator_of_mem hx,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  have hcompact {S : Set E} (hS : IsCompact S) :
      (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u S) =
        ((volume : Measure E).withDensity F) S := by
    have hT : MeasurableSet (FunctionalInequalities.Analysis.subgradientImage u S) :=
      (t14d_isClosed_subgradientImage hu.continuous hS).measurableSet
    have hleft :
        ∫⁻ p in FunctionalInequalities.Analysis.subgradientImage u S, g p ∂(volume : Measure E).withDensity f =
          (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u S) := by
      calc
        ∫⁻ p in FunctionalInequalities.Analysis.subgradientImage u S, g p ∂(volume : Measure E).withDensity f =
            ∫⁻ p in FunctionalInequalities.Analysis.subgradientImage u S, (f * g) p ∂(volume : Measure E) :=
          setLIntegral_withDensity_eq_setLIntegral_mul volume hf hg hT
        _ = ∫⁻ p in FunctionalInequalities.Analysis.subgradientImage u S, 1 ∂(volume : Measure E) :=
          setLIntegral_congr_fun hT fun p hp => hcancel p (hsub S hp)
        _ = (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u S) := by
          rw [lintegral_one, Measure.restrict_apply_univ]
    calc
      (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u S) =
          ∫⁻ p in FunctionalInequalities.Analysis.subgradientImage u S, g p ∂(volume : Measure E).withDensity f :=
        hleft.symm
      _ = ∫⁻ x in S, g (gradient u x) ∂(volume : Measure E).withDensity ρ :=
        FunctionalInequalities.Analysis.lintegral_subgradientImage_eq_of_map_gradient_408915f hu hconv
          (withDensity_absolutelyContinuous volume ρ) hmap'
          (withDensity_absolutelyContinuous volume f) hS g hg
      _ = ∫⁻ x in S, (ρ * (g ∘ gradient u)) x ∂(volume : Measure E) :=
        setLIntegral_withDensity_eq_setLIntegral_mul volume hρ
          (hg.comp hgrad) hS.measurableSet
      _ = ∫⁻ x in S, F x ∂(volume : Measure E) :=
        lintegral_congr_ae (ae_restrict_of_ae hprod)
      _ = ((volume : Measure E).withDensity F) S :=
        (withDensity_apply F hS.measurableSet).symm
  let : LocallyCompactSpace G := hG.locallyCompactSpace
  let S : ℕ → Set E := fun n => Subtype.val '' compactCovering G n
  have hScompact (n : ℕ) : IsCompact (S n) :=
    (isCompact_compactCovering G n).image continuous_subtype_val
  have hSmono : Monotone S := fun _ _ hij =>
    Set.image_mono (compactCovering_subset G hij)
  have hSunion : (⋃ n, S n) = G := by
    change (⋃ n, Subtype.val '' compactCovering G n) = G
    rw [← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe]
  have hTmono : Monotone (fun n => FunctionalInequalities.Analysis.subgradientImage u (S n)) := by
    intro i j hij p hp
    rcases hp with ⟨x, hx, hp⟩
    exact ⟨x, hSmono hij hx, hp⟩
  have hTunion : FunctionalInequalities.Analysis.subgradientImage u G = ⋃ n, FunctionalInequalities.Analysis.subgradientImage u (S n) := by
    rw [← hSunion]
    ext p
    constructor
    · rintro ⟨x, hx, hp⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n, x, hn, hp⟩
    · intro hp
      obtain ⟨n, x, hx, hp⟩ := mem_iUnion.mp hp
      exact ⟨x, mem_iUnion.mpr ⟨n, hx⟩, hp⟩
  calc
    (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u G) =
        (volume : Measure E) (⋃ n, FunctionalInequalities.Analysis.subgradientImage u (S n)) := by
      rw [hTunion]
    _ = ⨆ n, (volume : Measure E) (FunctionalInequalities.Analysis.subgradientImage u (S n)) :=
      hTmono.measure_iUnion
    _ = ⨆ n, ((volume : Measure E).withDensity F) (S n) := by
      congr 1
      funext n
      exact hcompact (hScompact n)
    _ = ((volume : Measure E).withDensity F) (⋃ n, S n) :=
      hSmono.measure_iUnion.symm
    _ = ((volume : Measure E).withDensity F) G := by rw [hSunion]
    _ = ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + V (gradient u x)))
        ∂(volume : Measure E) :=
      withDensity_apply F hG.measurableSet
