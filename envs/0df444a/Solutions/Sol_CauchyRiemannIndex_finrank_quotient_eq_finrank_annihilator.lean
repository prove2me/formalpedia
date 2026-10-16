-- Prove2me | solution 1 for CauchyRiemannIndex.finrank_quotient_eq_finrank_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T09:43:41.464718+00:00
-- url     : https://prove2.me/submissions/3f8ca810-7d9a-4b85-8bf1-21a9ff24ed4b

import Theorems.Thm_CauchyRiemannIndex_dense_of_forall_integral_inner_eq_zero
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- ===== Scratch/CokerA.lean =====
namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

noncomputable section

section Pairing

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

lemma cka_integrable (f : Lp E p μ) (g : Lp E q μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  have h := MemLp.of_bilin (r := 1) (fun a b => inner ℝ a b) 1 (Lp.memLp f) (Lp.memLp g)
    ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g))
    (Filter.Eventually.of_forall fun x => by
      rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
      exact norm_inner_le_norm _ _)
  exact memLp_one_iff_integrable.1 h

/-- The pairing `∫ ⟨f, g⟩` as a bilinear map. -/
def ckaPair : Lp E p μ →ₗ[ℝ] Lp E q μ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => ∫ x, inner ℝ (f x) (g x) ∂μ)
    (fun f f' g => by
      rw [← integral_add (cka_integrable f g) (cka_integrable f' g)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add f f'] with x hx
      rw [hx, Pi.add_apply, inner_add_left])
    (fun c f g => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c f] with x hx
      rw [hx, Pi.smul_apply, real_inner_smul_left])
    (fun f g g' => by
      rw [← integral_add (cka_integrable f g) (cka_integrable f g')]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add g g'] with x hx
      rw [hx, Pi.add_apply, inner_add_right])
    (fun c f g => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c g] with x hx
      rw [hx, Pi.smul_apply, real_inner_smul_right])

lemma ckaPair_apply (f : Lp E p μ) (g : Lp E q μ) :
    ckaPair f g = ∫ x, inner ℝ (f x) (g x) ∂μ := rfl

omit [p.HolderConjugate q] in
/-- An `L^q` function orthogonal to all of `L^p` vanishes. -/
lemma cka_sep [SigmaFinite μ] [CompleteSpace E] (hp' : p ≠ ⊤) (hq' : q ≠ ⊤) (g : Lp E q μ)
    (hg : ∀ f : Lp E p μ, ∫ x, inner ℝ (f x) (g x) ∂μ = 0) : g = 0 := by
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  have hint : ∀ s, MeasurableSet s → μ s < ⊤ → IntegrableOn (g : α → E) s μ := by
    intro s hs hμs
    haveI : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμs⟩
    exact ((Lp.memLp g).restrict s).integrable Fact.out
  have hae := ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (f := (g : α → E)) hint
    (fun s hs hμs => by
      rw [← inner_self_eq_zero (𝕜 := ℝ)]
      set e := ∫ x in s, (g : α → E) x ∂μ
      rw [← hg (indicatorConstLp p hs hμs.ne e)]
      calc inner ℝ e e = ∫ x in s, inner ℝ e ((g : α → E) x) ∂μ := by
            have := (innerSL ℝ e).integral_comp_comm (hint s hs hμs)
            simp only [innerSL_apply_apply] at this
            exact this.symm
        _ = ∫ x, s.indicator (fun x => inner ℝ e ((g : α → E) x)) x ∂μ :=
            (integral_indicator hs).symm
        _ = _ := by
            refine integral_congr_ae ?_
            filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs.ne) (c := e)]
              with x hx
            rw [hx]
            by_cases hxs : x ∈ s
            · simp [Set.indicator_of_mem hxs]
            · simp [Set.indicator_of_notMem hxs])
  exact (Lp.eq_zero_iff_ae_eq_zero).2 hae

end Pairing

theorem finrank_quotient_eq_finrank_annihilator_aux {α E : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp : 1 < p) (hp' : p ≠ ⊤) (M : Submodule ℝ (Lp E p μ))
    (hM : IsClosed (M : Set (Lp E p μ))) (N : Submodule ℝ (Lp E q μ))
    (hN : ∀ g : Lp E q μ, g ∈ N ↔ ∀ v ∈ M, ∫ x, inner ℝ (v x) (g x) ∂μ = 0)
    (hNfin : FiniteDimensional ℝ N) :
    FiniteDimensional ℝ (Lp E p μ ⧸ M) ∧
      Module.finrank ℝ (Lp E p μ ⧸ M) = Module.finrank ℝ N := by
  have hqt : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  -- `T f = (g ↦ ∫ ⟨f, g⟩)` on `N`
  let T : Lp E p μ →ₗ[ℝ] Module.Dual ℝ N :=
    (ckaPair (μ := μ) (E := E) (p := p) (q := q)).compl₂ N.subtype
  have hT : ∀ f (g : N), T f g = ∫ x, inner ℝ (f x) ((g : Lp E q μ) x) ∂μ := fun _ _ => rfl
  have hMT : M ≤ LinearMap.ker T := by
    intro f hf
    rw [LinearMap.mem_ker]
    ext g
    rw [hT, LinearMap.zero_apply]
    exact (hN g).1 g.2 f hf
  -- `T` is onto
  have hTs : Function.Surjective T := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ : ∃ φ : Module.Dual ℝ (Module.Dual ℝ N), φ ≠ 0 ∧
        LinearMap.range T ≤ LinearMap.ker φ := by
      obtain ⟨φ, hφ, hφ'⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
      exact ⟨φ, hφ, hφ'⟩
    obtain ⟨g, hg⟩ := (Module.evalEquiv ℝ N).surjective φ
    have hg0 : (g : Lp E q μ) = 0 := by
      refine cka_sep (p := p) hp' hqt _ fun f => ?_
      have := hφ (LinearMap.mem_range_self T f)
      rw [LinearMap.mem_ker, ← hg] at this
      exact this
    apply hφ0
    rw [← hg]
    have : g = 0 := Subtype.ext hg0
    rw [this, map_zero]
  -- preimages of a basis of the dual
  set k := Module.finrank ℝ (Module.Dual ℝ N)
  let bd := Module.finBasis ℝ (Module.Dual ℝ N)
  choose h hh using fun i : Fin k => hTs (bd i)
  set F : Submodule ℝ (Lp E p μ) := Submodule.span ℝ (Set.range h)
  haveI : FiniteDimensional ℝ F := FiniteDimensional.span_of_finite ℝ (Set.finite_range h)
  have hFk : Module.finrank ℝ F ≤ k := by
    have := finrank_range_le_card (R := ℝ) h
    simpa [Set.finrank] using this
  -- `M ⊔ F` is dense
  have hdense : Dense ((M ⊔ F : Submodule ℝ (Lp E p μ)) : Set (Lp E p μ)) := by
    refine dense_of_forall_integral_inner_eq_zero μ p q hp hp' _ fun g hg => ?_
    have hgN : g ∈ N := (hN g).2 fun v hv => hg v (Submodule.mem_sup_left hv)
    have hev : ∀ φ : Module.Dual ℝ N, φ ⟨g, hgN⟩ = 0 := by
      have : Module.Dual.eval ℝ N ⟨g, hgN⟩ = 0 := by
        refine bd.ext fun i => ?_
        rw [Module.Dual.eval_apply, LinearMap.zero_apply, ← hh i, hT]
        exact hg _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
      intro φ
      exact LinearMap.congr_fun this φ
    have := (Module.forall_dual_apply_eq_zero_iff ℝ (⟨g, hgN⟩ : N)).1 hev
    exact congrArg Subtype.val this
  -- the quotient is spanned by the image of `F`
  haveI : IsClosed (M : Set (Lp E p μ)) := hM
  let P : F →ₗ[ℝ] Lp E p μ ⧸ M := M.mkQ ∘ₗ F.subtype
  have hPs : Function.Surjective P := by
    rw [← LinearMap.range_eq_top]
    have hcl : IsClosed (LinearMap.range P : Set (Lp E p μ ⧸ M)) :=
      Submodule.closed_of_finiteDimensional _
    have hd : Dense (LinearMap.range P : Set (Lp E p μ ⧸ M)) := by
      have h1 : Dense (M.mkQ '' ((M ⊔ F : Submodule ℝ (Lp E p μ)) : Set (Lp E p μ))) :=
        (Submodule.Quotient.mk_surjective M).denseRange.dense_image
          M.continuous_mkQ hdense
      refine h1.mono ?_
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨m, hm, f, hf, rfl⟩ := Submodule.mem_sup.1 hv
      refine ⟨⟨f, hf⟩, ?_⟩
      simp only [P, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        Submodule.mkQ_apply, map_add]
      rw [(Submodule.Quotient.mk_eq_zero M).2 hm, zero_add]
    have := hcl.closure_eq
    rw [hd.closure_eq] at this
    exact SetLike.coe_injective (this.symm.trans Submodule.top_coe.symm)
  haveI : FiniteDimensional ℝ (Lp E p μ ⧸ M) := Module.Finite.of_surjective P hPs
  refine ⟨inferInstance, le_antisymm ?_ ?_⟩
  · calc Module.finrank ℝ (Lp E p μ ⧸ M) = Module.finrank ℝ (LinearMap.range P) := by
          rw [LinearMap.range_eq_top.2 hPs, finrank_top]
      _ ≤ Module.finrank ℝ F := LinearMap.finrank_range_le P
      _ ≤ k := hFk
      _ = Module.finrank ℝ N := Subspace.dual_finrank_eq
  · let L : (Lp E p μ ⧸ M) →ₗ[ℝ] Module.Dual ℝ N := M.liftQ T hMT
    have hLs : Function.Surjective L := by
      intro φ
      obtain ⟨f, rfl⟩ := hTs φ
      exact ⟨M.mkQ f, rfl⟩
    calc Module.finrank ℝ N = Module.finrank ℝ (Module.Dual ℝ N) := Subspace.dual_finrank_eq.symm
      _ = Module.finrank ℝ (LinearMap.range L) := by rw [LinearMap.range_eq_top.2 hLs, finrank_top]
      _ ≤ Module.finrank ℝ (Lp E p μ ⧸ M) := LinearMap.finrank_range_le L

end

end CauchyRiemannIndex

-- ===== Scratch/CokerASol.lean =====
open MeasureTheory
open scoped ENNReal

theorem solution {α E : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp : 1 < p) (hp' : p ≠ ⊤) (M : Submodule ℝ (Lp E p μ))
    (hM : IsClosed (M : Set (Lp E p μ))) (N : Submodule ℝ (Lp E q μ))
    (hN : ∀ g : Lp E q μ, g ∈ N ↔ ∀ v ∈ M, ∫ x, inner ℝ (v x) (g x) ∂μ = 0)
    (hNfin : FiniteDimensional ℝ N) :
    FiniteDimensional ℝ (Lp E p μ ⧸ M) ∧
      Module.finrank ℝ (Lp E p μ ⧸ M) = Module.finrank ℝ N :=
  CauchyRiemannIndex.finrank_quotient_eq_finrank_annihilator_aux μ p q hp hp' M hM N hN hNfin
