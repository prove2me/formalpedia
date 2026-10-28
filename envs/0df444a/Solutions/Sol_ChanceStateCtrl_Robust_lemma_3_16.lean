-- Prove2me | solution 1 for ChanceStateCtrl.Robust.lemma_3_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:38:29.945535+00:00
-- url     : https://prove2.me/submissions/7120ce43-bb11-476c-9744-403563f25c27

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory Filter Topology
open scoped CompactlySupported InnerProductSpace
open ChanceStateCtrl.Robust

/-- Riesz–Markov–Kakutani on a compact space, for a positive linear functional. -/
private lemma rmk_compact_lin {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (Λ : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ z : C(X, ℝ), (∀ q, 0 ≤ z q) → 0 ≤ Λ z) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ z : C(X, ℝ), ∫ q, z q ∂μ = Λ z := by
  let Lc : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => Λ (f : C(X, ℝ))
      map_add' := fun f g => by
        rw [← map_add]; rfl
      map_smul' := fun c f => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← smul_eq_mul, ← map_smul]; rfl }
  let Λc : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ Lc (fun f hf => hpos _ (fun q => hf q))
  refine ⟨RealRMK.rieszMeasure Λc, inferInstance, fun z => ?_⟩
  have := RealRMK.integral_rieszMeasure Λc (CompactlySupportedContinuousMap.continuousMapEquiv z)
  exact this.trans (congrArg Λ (ContinuousMap.ext fun _ => rfl))

theorem solution {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)] [CompactSpace Ξ]
    (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D)
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : ChanceStateCtrl.AlmostSure.IsSolutionOperator D Ainv) (α : ℝ)
    (F : ChanceStateCtrl.PDE.L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hD0 : D.Nonempty) (hΞ0 : Ξ.Nonempty) (us : ChanceStateCtrl.PDE.L2 D) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∃ s ∈ closure (convexHull ℝ
        (evalRep Ainv '' (Prod.fst '' argmaxSet (Ξ := Ξ) Ainv f0 phi us))),
        gradient F us + lam • s = 0) ↔
      ∃ μt : Measure (closure D × Ξ), IsProbabilityMeasure μt ∧
        μt (argmaxSet Ainv f0 phi us)ᶜ = 0 ∧
        ∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + lam * ∫ q, Ainv h q.1 ∂μt = 0 := by
  classical
  set M := argmaxSet (Ξ := Ξ) Ainv f0 phi us with hMdef
  set y := Shat (Ξ := Ξ) Ainv f0 phi us with hy
  haveI : Nonempty (closure D × Ξ) := by
    obtain ⟨x, hx⟩ := hD0
    obtain ⟨z, hz⟩ := hΞ0
    exact ⟨(⟨x, subset_closure hx⟩, ⟨z, hz⟩)⟩
  obtain ⟨q0, -, hq0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    y.continuous.continuousOn
  have hq0M : q0 ∈ M := fun q' => hq0 (Set.mem_univ q')
  haveI : Nonempty M := ⟨⟨q0, hq0M⟩⟩
  have hMclosed : IsClosed M := by
    have : M = ⋂ q', {q | y q' ≤ y q} := by
      ext q; simp only [hMdef, argmaxSet, Set.mem_setOf_eq, Set.mem_iInter, hy]
    rw [this]; exact isClosed_iInter fun q' => isClosed_le continuous_const y.continuous
  have hrep : ∀ x h, ⟪evalRep Ainv x, h⟫_ℝ = Ainv h x := by
    intro x h; simp [evalRep, InnerProductSpace.toDual_symm_apply]
  have hgrad : ∀ h, ⟪gradient F us, h⟫_ℝ = fderiv ℝ F us h := by
    intro h; simp [gradient, InnerProductSpace.toDual_symm_apply]
  have heq : ∀ s : ChanceStateCtrl.PDE.L2 D, (gradient F us + lam • s = 0 ↔
      ∀ h, fderiv ℝ F us h + lam * ⟪s, h⟫_ℝ = 0) := by
    intro s; constructor
    · intro h0 h
      have := congrArg (fun v => ⟪v, h⟫_ℝ) h0
      simpa [inner_add_left, real_inner_smul_left, hgrad] using this
    · intro hh
      apply ext_inner_right ℝ
      intro h
      rw [inner_add_left, real_inner_smul_left, hgrad, inner_zero_left]
      exact hh h
  have hbddM : ∀ g : C(closure D × Ξ, ℝ), BddAbove (Set.range fun q : M => g q) := by
    intro g
    refine (isCompact_range g.continuous).bddAbove.mono ?_
    rintro _ ⟨q, rfl⟩; exact ⟨q.1, rfl⟩
  have hint : ∀ (ν : Measure (closure D × Ξ)) [IsFiniteMeasure ν] (z : C(closure D × Ξ, ℝ)),
      Integrable (fun q => z q) ν := fun ν _ z =>
    z.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS_sub : ∀ q ∈ M, evalRep Ainv q.1 ∈ closure (convexHull ℝ
      (evalRep Ainv '' (Prod.fst '' argmaxSet (Ξ := Ξ) Ainv f0 phi us))) := fun q hq =>
    subset_closure (subset_convexHull ℝ _ ⟨q.1, ⟨q, hq, rfl⟩, rfl⟩)
  let T : ChanceStateCtrl.PDE.L2 D →ₗ[ℝ] C(closure D × Ξ, ℝ) :=
    { toFun := AhatBhat Ainv
      map_add' := fun a b => by ext; simp [AhatBhat]
      map_smul' := fun c a => by ext; simp [AhatBhat] }
  have hT : ∀ h q, T h q = Ainv h q.1 := fun h q => rfl
  constructor
  · rintro ⟨s, hsC, hs0⟩
    rw [heq] at hs0
    let N : C(closure D × Ξ, ℝ) → ℝ := fun g => ⨆ q : M, g q
    have hsle : ∀ h, ⟪s, h⟫_ℝ ≤ N (T h) := by
      intro h
      have hsub : closure (convexHull ℝ (evalRep Ainv '' (Prod.fst '' M))) ⊆
          {b | innerSL ℝ h b ≤ N (T h)} := by
        apply closure_minimal _ (isClosed_le (innerSL ℝ h).continuous continuous_const)
        apply convexHull_min _ (convex_halfSpace_le (innerSL ℝ h).toLinearMap.isLinear _)
        rintro _ ⟨x, ⟨q, hq, rfl⟩, rfl⟩
        show ⟪h, evalRep Ainv q.1⟫_ℝ ≤ N (T h)
        rw [real_inner_comm, hrep]
        exact le_ciSup (hbddM (T h)) ⟨q, hq⟩
      have := hsub hsC
      simpa [real_inner_comm] using this
    have hN0 : ∀ g : C(closure D × Ξ, ℝ), g = 0 → N g = 0 := by
      intro g hg; subst hg; simp [N]
    let ψ : ChanceStateCtrl.PDE.L2 D →ₗ[ℝ] ℝ := (innerSL ℝ s).toLinearMap
    have hψ : ∀ h, ψ h = ⟪s, h⟫_ℝ := fun h => rfl
    have hker : LinearMap.ker T ≤ LinearMap.ker ψ := by
      intro h hh
      rw [LinearMap.mem_ker] at hh ⊢
      have h1 := hsle h
      have h2 := hsle (-h)
      rw [hN0 _ hh] at h1
      rw [map_neg, hh, neg_zero, hN0 _ rfl, inner_neg_right] at h2
      rw [hψ]; linarith
    let f0' : C(closure D × Ξ, ℝ) →ₗ.[ℝ] ℝ :=
      { domain := LinearMap.range T
        toFun := ((LinearMap.ker T).liftQ ψ hker).comp
          (T.quotKerEquivRange.symm : LinearMap.range T →ₗ[ℝ] _) }
    have hf0T : ∀ h, f0' ⟨T h, LinearMap.mem_range_self T h⟩ = ⟪s, h⟫_ℝ := by
      intro h
      show ((LinearMap.ker T).liftQ ψ hker) (T.quotKerEquivRange.symm ⟨T h, _⟩) = _
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      rfl
    have Nhom : ∀ c : ℝ, 0 < c → ∀ g, N (c • g) = c * N g := by
      intro c hc g
      simp only [N, ContinuousMap.smul_apply, smul_eq_mul]
      rw [Real.mul_iSup_of_nonneg hc.le]
    have Nadd : ∀ g g', N (g + g') ≤ N g + N g' := by
      intro g g'
      exact ciSup_le fun q => add_le_add (le_ciSup (hbddM g) q) (le_ciSup (hbddM g') q)
    have hf0le : ∀ x : f0'.domain, f0' x ≤ N x := by
      rintro ⟨x, hx⟩
      obtain ⟨h, rfl⟩ := LinearMap.mem_range.1 hx
      rw [hf0T]; exact hsle h
    obtain ⟨L, hLext, hLle⟩ := exists_extension_of_le_sublinear f0' N Nhom Nadd hf0le
    have hLT : ∀ h, L (T h) = ⟪s, h⟫_ℝ := fun h => by
      rw [← hf0T]; exact hLext ⟨T h, LinearMap.mem_range_self T h⟩
    have hNnp : ∀ g : C(closure D × Ξ, ℝ), (∀ q, g q ≤ 0) → N g ≤ 0 :=
      fun g hg => ciSup_le fun q => hg q
    have hLpos : ∀ z : C(closure D × Ξ, ℝ), (∀ q, 0 ≤ z q) → 0 ≤ L z := by
      intro z hz
      have := (hLle (-z)).trans (hNnp _ (fun q => by simp; exact hz q))
      rw [map_neg] at this; linarith
    obtain ⟨μ, hμfin, hμ⟩ := rmk_compact_lin L hLpos
    -- total mass one
    let one : C(closure D × Ξ, ℝ) := ContinuousMap.const _ 1
    have hL1 : L one = 1 := by
      have h1 : L one ≤ 1 := (hLle one).trans (ciSup_le fun q => le_rfl)
      have h2 : L (-one) ≤ -1 := (hLle (-one)).trans (ciSup_le fun q => by simp [one])
      rw [map_neg] at h2; linarith
    have hμuniv : μ Set.univ = 1 := by
      have := hμ one
      simp only [one, ContinuousMap.const_apply, integral_const, smul_eq_mul, mul_one] at this
      rw [hL1] at this
      rw [measureReal_def, ENNReal.toReal_eq_one_iff] at this
      exact this
    haveI hprob : IsProbabilityMeasure μ := ⟨hμuniv⟩
    -- support in `M`
    have hzero : ∀ g : C(closure D × Ξ, ℝ), (∀ q ∈ M, g q = 0) → ∫ q, g q ∂μ ≤ 0 := by
      intro g hg
      rw [hμ]
      exact (hLle g).trans (ciSup_le fun q => (hg q.1 q.2).le)
    have hMc : μ Mᶜ = 0 := by
      let G : ℕ → C(closure D × Ξ, ℝ) := fun n =>
        ⟨fun q => min 1 ((n : ℝ) * Metric.infDist q M),
          continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt M))⟩
      have hG0 : ∀ n, ∫ q, G n q ∂μ = 0 := by
        intro n
        refine le_antisymm (hzero (G n) (fun q hq => ?_)) ?_
        · show min 1 ((n : ℝ) * Metric.infDist q M) = 0
          rw [Metric.infDist_zero_of_mem hq, mul_zero]; simp
        · exact integral_nonneg fun q => le_min zero_le_one
            (mul_nonneg (Nat.cast_nonneg n) Metric.infDist_nonneg)
      have hlim : Tendsto (fun n => ∫ q, G n q ∂μ) atTop
          (𝓝 (∫ q, Mᶜ.indicator (1 : closure D × Ξ → ℝ) q ∂μ)) := by
        refine tendsto_integral_of_dominated_convergence (fun _ => 1)
          (fun n => (G n).continuous.aestronglyMeasurable) (integrable_const 1)
          (fun n => Eventually.of_forall fun q => ?_) (Eventually.of_forall fun q => ?_)
        · have h0 : 0 ≤ G n q := le_min zero_le_one
            (mul_nonneg (Nat.cast_nonneg n) Metric.infDist_nonneg)
          rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact min_le_left _ _
        · by_cases hq : q ∈ M
          · have : ∀ n, G n q = 0 := fun n => by
              show min 1 ((n : ℝ) * Metric.infDist q M) = 0
              rw [Metric.infDist_zero_of_mem hq, mul_zero]; simp
            simp only [this, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hq)]
            exact tendsto_const_nhds
          · have hpos : 0 < Metric.infDist q M :=
              (hMclosed.notMem_iff_infDist_pos ⟨q0, hq0M⟩).1 hq
            rw [Set.indicator_of_mem (Set.mem_compl hq)]
            obtain ⟨N0, hN0'⟩ := exists_nat_gt (1 / Metric.infDist q M)
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [eventually_ge_atTop N0] with n hn
            show 1 = min 1 ((n : ℝ) * Metric.infDist q M)
            symm; apply min_eq_left
            have : (N0 : ℝ) ≤ n := by exact_mod_cast hn
            rw [div_lt_iff₀ hpos] at hN0'
            nlinarith
      simp only [hG0] at hlim
      have hval := tendsto_nhds_unique tendsto_const_nhds hlim
      rw [integral_indicator_one hMclosed.measurableSet.compl] at hval
      exact (measureReal_eq_zero_iff (measure_ne_top μ _)).1 hval.symm
    refine ⟨μ, hprob, hMc, fun h => ?_⟩
    have : ∫ q, Ainv h q.1 ∂μ = ⟪s, h⟫_ℝ := by
      rw [← hLT, ← hμ]; rfl
    rw [this]; exact hs0 h
  · rintro ⟨μt, hprob, hsupp, h67⟩
    have hintA : ∀ h, Integrable (fun q => Ainv h q.1) μt := fun h => hint μt (T h)
    let φl : ChanceStateCtrl.PDE.L2 D →ₗ[ℝ] ℝ :=
      { toFun := fun h => ∫ q, Ainv h q.1 ∂μt
        map_add' := fun a b => by
          simp only [map_add, ContinuousMap.add_apply]
          exact integral_add (hintA a) (hintA b)
        map_smul' := fun c a => by
          simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
          exact integral_const_mul c _ }
    let φ : StrongDual ℝ (ChanceStateCtrl.PDE.L2 D) := φl.mkContinuous ‖Ainv‖ (fun h => by
      have := norm_integral_le_of_norm_le_const (μ := μt) (f := fun q => Ainv h q.1)
        (C := ‖Ainv‖ * ‖h‖) (Eventually.of_forall fun q =>
          ((Ainv h).norm_coe_le_norm q.1).trans (Ainv.le_opNorm h))
      simp only [probReal_univ, mul_one] at this
      exact this)
    have hφ : ∀ h, φ h = ∫ q, Ainv h q.1 ∂μt := fun h => rfl
    set s := (InnerProductSpace.toDual ℝ (ChanceStateCtrl.PDE.L2 D)).symm φ with hsdef
    have hs : ∀ h, ⟪s, h⟫_ℝ = ∫ q, Ainv h q.1 ∂μt := fun h => by
      rw [hsdef, InnerProductSpace.toDual_symm_apply, hφ]
    refine ⟨s, ?_, (heq s).2 fun h => by rw [hs]; exact h67 h⟩
    by_contra hns
    obtain ⟨f, u, hfs, hfb⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ _).closure isClosed_closure hns
    set w := (InnerProductSpace.toDual ℝ (ChanceStateCtrl.PDE.L2 D)).symm f with hwdef
    have hfw : ∀ b, f b = ⟪w, b⟫_ℝ := fun b => by
      rw [hwdef, InnerProductSpace.toDual_symm_apply]
    have hae : ∀ᵐ q ∂μt, u ≤ Ainv w q.1 := by
      have hM : ∀ᵐ q ∂μt, q ∈ M := by rw [ae_iff]; exact hsupp
      filter_upwards [hM] with q hq
      have := hfb _ (hS_sub q hq)
      rw [hfw, real_inner_comm, hrep] at this
      exact this.le
    have hge : u ≤ ∫ q, Ainv w q.1 ∂μt := by
      have := integral_mono_ae (integrable_const u) (hintA w) hae
      simpa using this
    rw [hfw, real_inner_comm, hs] at hfs
    linarith
