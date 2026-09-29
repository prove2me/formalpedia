-- Prove2me | solution 1 for BertsekasDP.piecewise_adjoint_terminal_exists
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T21:17:51.139474+00:00
-- url     : https://prove2.me/submissions/56eb68a2-5a07-4700-87fd-a9435535ea9e

import Definitions.Def_BertsekasCTModel

open Set Filter MeasureTheory
open scoped Topology

-- The weighted Volterra construction below adapts the complete proof of
-- VectorSpaceOpt.integrable_backward_adjoint_exists (Prove2Me submission
-- 64b7009e-4d0f-4ea1-a60d-e666e8a21430); it is proved here from Mathlib.

private lemma integrable_positive_tail_small
    {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hf0 : ∀ s, 0 ≤ f s) :
    ∃ M : ℝ, 0 < M ∧
      IntervalIntegrable (fun s => max (f s - M) 0) volume a b ∧
      (∫ s in a..b, max (f s - M) 0) < 1 / 4 := by
  have hfi : IntegrableOn f (Icc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf
  have hmeas (M : ℝ) : AEStronglyMeasurable (fun s => max (f s - M) 0)
      (volume.restrict (Icc a b)) :=
    ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      hfi.aestronglyMeasurable
  have hnorm (M : ℝ) (hM : 0 ≤ M) (s : ℝ) : ‖max (f s - M) 0‖ ≤ f s := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (sub_le_self _ hM) (hf0 s)
  have hlim : Tendsto (fun M : ℝ => ∫ s in Icc a b, max (f s - M) 0)
      atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Icc a b)) (f := fun _ => (0 : ℝ)) f
      (Eventually.of_forall hmeas)
      ((eventually_ge_atTop 0).mono fun M hM => Eventually.of_forall (hnorm M hM)) hfi
      (Eventually.of_forall fun s => ?_)
    · simpa using h
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (f s)] with M hM
      simp [max_eq_right (sub_nonpos.mpr hM)]
  obtain ⟨M, hM, hsmall⟩ := ((eventually_gt_atTop 0).and
    (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4))).exists
  have hi : IntervalIntegrable (fun s => max (f s - M) 0) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hfi.mono' (hmeas M) (Eventually.of_forall (hnorm M hM.le))
  refine ⟨M, hM, hi, ?_⟩
  simpa [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using hsmall

private lemma exponential_integral_bound {t b L : ℝ} (hL : 0 < L) :
    Real.exp (L * t) * (∫ s in t..b, Real.exp (-L * s)) ≤ 1 / L := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hL.ne'), integral_exp]
  simp only [smul_eq_mul]
  have hx : Real.exp (L * t) * Real.exp (-L * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hp : 0 < Real.exp (L * t) * Real.exp (-L * b) := by positivity
  simp only [neg_mul] at hx hp
  field_simp
  nlinarith

private lemma exponential_kernel_small
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) (hf0 : ∀ s, 0 ≤ f s) :
    ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Icc a b,
      Real.exp (L * t) * (∫ s in t..b, f s * Real.exp (-L * s)) ≤ 1 / 2 := by
  obtain ⟨M, hM, hR, hsmall⟩ := integrable_positive_tail_small hab.le hf hf0
  let L := 8 * M
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro t ht
  let R : ℝ → ℝ := fun s => max (f s - M) 0
  have hsub : uIcc t b ⊆ uIcc a b :=
    uIcc_subset_uIcc (by simpa [uIcc_of_le hab.le] using ht) right_mem_uIcc
  have hRt : IntervalIntegrable R volume t b := hR.mono_set hsub
  have he : Continuous (fun s : ℝ => Real.exp (-L * s)) := by fun_prop
  have hsplit :
      Real.exp (L * t) * (∫ s in t..b, f s * Real.exp (-L * s)) ≤
        M * (Real.exp (L * t) * (∫ s in t..b, Real.exp (-L * s))) +
        Real.exp (L * t) * (∫ s in t..b, R s * Real.exp (-L * s)) := by
    calc
      _ ≤ Real.exp (L * t) * (∫ s in t..b,
          M * Real.exp (-L * s) + R s * Real.exp (-L * s)) := by
        gcongr
        apply intervalIntegral.integral_mono_on ht.2
          ((hf.mono_set hsub).mul_continuousOn he.continuousOn)
          (((he.intervalIntegrable t b).const_mul M).add
            (hRt.mul_continuousOn he.continuousOn))
        intro s hs
        have hfs : f s ≤ M + R s := by
          have := le_max_left (f s - M) 0
          dsimp [R]; linarith
        nlinarith [Real.exp_pos (-L * s)]
      _ = _ := by
        rw [intervalIntegral.integral_add ((he.intervalIntegrable t b).const_mul M)
          (hRt.mul_continuousOn he.continuousOn), intervalIntegral.integral_const_mul]
        ring
  have htail : Real.exp (L * t) * (∫ s in t..b, R s * Real.exp (-L * s)) < 1 / 4 := by
    calc
      _ = ∫ s in t..b, Real.exp (L * t) * (R s * Real.exp (-L * s)) :=
        (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ s in t..b, R s := by
        apply intervalIntegral.integral_mono_on ht.2
          ((hRt.mul_continuousOn he.continuousOn).const_mul _) hRt
        intro s hs
        have hprod : Real.exp (L * t) * Real.exp (-L * s) ≤ 1 := by
          rw [← Real.exp_add, Real.exp_le_one_iff]
          nlinarith [hs.1]
        have hr : 0 ≤ R s := le_max_right _ _
        nlinarith
      _ ≤ ∫ s in a..b, R s :=
        intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
          (Eventually.of_forall fun s => le_max_right _ _) hR
      _ < 1 / 4 := hsmall
  have hconst := mul_le_mul_of_nonneg_left (exponential_integral_bound (t := t) (b := b) hL) hM.le
  have hML : M * (1 / L) = 1 / 8 := by dsimp [L]; field_simp
  rw [hML] at hconst
  linarith


open scoped RealInnerProductSpace

private lemma integral_apply_integrable
    {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    {B : ℝ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))}
    (hB : IntervalIntegrable B volume a b)
    {x : ℝ → EuclideanSpace ℝ (Fin n)} (hx : ContinuousOn x (Icc a b)) :
    IntervalIntegrable (fun t => B t (x t)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hB ⊢
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  apply (hB.norm.mul_const C).mono'
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hB.aestronglyMeasurable.prodMk (hx.aestronglyMeasurable measurableSet_Icc))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (B t).le_opNorm (x t) |>.trans
      (mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _))

private lemma volterra_of_exponential_bound
    {n : ℕ} (a b : ℝ) (hab : a < b)
    (B : ℝ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hB : IntervalIntegrable B volume a b)
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : ContinuousOn g (Icc a b))
    (L : ℝ)
    (hL : ∀ t ∈ Icc a b,
      Real.exp (L * t) * (∫ s in t..b, ‖B s‖ * Real.exp (-L * s)) ≤ 1 / 2) :
    ∃ x : ℝ → EuclideanSpace ℝ (Fin n), ContinuousOn x (Icc a b) ∧
      ∀ t ∈ Icc a b, x t = g t + ∫ s in t..b, B s (x s) := by
  let U : C(Icc a b, EuclideanSpace ℝ (Fin n)) → ℝ → EuclideanSpace ℝ (Fin n) :=
    fun y t => Real.exp (-L * t) • IccExtend hab.le y t
  have hU (y : C(Icc a b, EuclideanSpace ℝ (Fin n))) : Continuous (U y) := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      y.continuous.Icc_extend'
  have hInt (y : C(Icc a b, EuclideanSpace ℝ (Fin n))) :
      IntervalIntegrable (fun s => B s (U y s)) volume a b :=
    integral_apply_integrable hab.le hB (hU y).continuousOn
  have hPrim (y : C(Icc a b, EuclideanSpace ℝ (Fin n))) :
      ContinuousOn (fun t => ∫ s in t..b, B s (U y s)) (Icc a b) := by
    have hi : IntegrableOn (fun s => B s (U y s)) (uIcc a b) volume := by
      rw [uIcc_of_le hab.le]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp (hInt y)
    simpa [uIcc_of_le hab.le] using intervalIntegral.continuousOn_primitive_interval_left hi
  let T : C(Icc a b, EuclideanSpace ℝ (Fin n)) → C(Icc a b, EuclideanSpace ℝ (Fin n)) := fun y =>
    ⟨fun t => Real.exp (L * (t : ℝ)) •
      (g t + ∫ s in (t : ℝ)..b, B s (U y s)),
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.smul
        (hg.add (hPrim y))).domRestrict⟩
  have hT : ContractingWith (1 / 2) T := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro y z
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro t
    have ht : (t : ℝ) ∈ Icc a b := t.property
    have hsub : uIcc (t : ℝ) b ⊆ uIcc a b :=
      uIcc_subset_uIcc (by simpa only [uIcc_of_le hab.le] using ht) right_mem_uIcc
    have hw : IntervalIntegrable (fun s => ‖B s‖ * Real.exp (-L * s)) volume (t : ℝ) b :=
      (hB.norm.mul_continuousOn (by fun_prop)).mono_set hsub
    have hbound :
        ‖∫ s in (t : ℝ)..b, B s (U y s) - B s (U z s)‖ ≤
          (∫ s in (t : ℝ)..b, ‖B s‖ * Real.exp (-L * s)) * dist y z := by
      rw [← intervalIntegral.integral_mul_const]
      apply intervalIntegral.norm_integral_le_of_norm_le ht.2
        (Filter.Eventually.of_forall fun s hs => ?_) (hw.mul_const _)
      rw [← map_sub]
      have hUsub : U y s - U z s = Real.exp (-L * s) •
          (IccExtend hab.le y s - IccExtend hab.le z s) := by
        simp only [U, smul_sub]
      rw [hUsub, map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      have hd : ‖IccExtend hab.le y s - IccExtend hab.le z s‖ ≤ dist y z := by
        show ‖y (projIcc a b hab.le s) - z (projIcc a b hab.le s)‖ ≤ dist y z
        rw [← dist_eq_norm]
        exact ContinuousMap.dist_apply_le_dist _
      calc
        _ ≤ Real.exp (-L * s) * (‖B s‖ *
            ‖IccExtend hab.le y s - IccExtend hab.le z s‖) := by
          gcongr; exact (B s).le_opNorm _
        _ ≤ Real.exp (-L * s) * (‖B s‖ * dist y z) := by gcongr
        _ = _ := by ring
    change dist (Real.exp (L * (t : ℝ)) • (g t + ∫ s in (t : ℝ)..b, B s (U y s)))
      (Real.exp (L * (t : ℝ)) • (g t + ∫ s in (t : ℝ)..b, B s (U z s))) ≤ _
    rw [dist_eq_norm, ← smul_sub, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub ((hInt y).mono_set hsub) ((hInt z).mono_set hsub),
      norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (L * (t : ℝ)) *
          ((∫ s in (t : ℝ)..b, ‖B s‖ * Real.exp (-L * s)) * dist y z) := by gcongr
      _ = (Real.exp (L * (t : ℝ)) *
          (∫ s in (t : ℝ)..b, ‖B s‖ * Real.exp (-L * s))) * dist y z := by ring
      _ ≤ (1 / 2 : ℝ) * dist y z := mul_le_mul_of_nonneg_right (hL t ht) dist_nonneg
      _ = _ := by norm_num
  let y := hT.fixedPoint T
  have hy : T y = y := hT.fixedPoint_isFixedPt
  refine ⟨U y, (hU y).continuousOn, ?_⟩
  intro t ht
  have hyt := congrArg (fun z : C(Icc a b, EuclideanSpace ℝ (Fin n)) => z ⟨t, ht⟩) hy
  change Real.exp (L * t) • (g t + ∫ s in t..b, B s (U y s)) = y ⟨t, ht⟩ at hyt
  dsimp only [U]
  rw [IccExtend_of_mem hab.le y ht, ← hyt, smul_smul]
  have hexp : Real.exp (-L * t) * Real.exp (L * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  rw [hexp, one_smul]


private lemma volterra_surjective
    {n : ℕ} (a b : ℝ) (hab : a < b)
    (B : ℝ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hB : IntervalIntegrable B volume a b)
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : ContinuousOn g (Icc a b)) :
    ∃ x : ℝ → EuclideanSpace ℝ (Fin n), ContinuousOn x (Icc a b) ∧
      ∀ t ∈ Icc a b, x t = g t + ∫ s in t..b, B s (x s) := by
  obtain ⟨L, _, hL⟩ := exponential_kernel_small hab hB.norm (fun s => norm_nonneg (B s))
  exact volterra_of_exponential_bound a b hab B hB g hg L hL


private lemma integrable_of_bounded_continuous_off_finset
    {E : Type*} [NormedAddCommGroup E] {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → E) (F : Finset ℝ)
    (hv : ContinuousOn v (Icc a b \ (F : Set ℝ)))
    (hbdd : Bornology.IsBounded (v '' Icc a b)) :
    IntervalIntegrable v volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hm : AEStronglyMeasurable v (volume.restrict (Icc a b)) := by
    have h := hv.aestronglyMeasurable (μ := volume) (measurableSet_Icc.diff F.finite_toSet.measurableSet)
    rwa [Measure.restrict_congr_set (sdiff_null_ae_eq_self (F.finite_toSet.measure_zero volume))] at h
  obtain ⟨C, hC⟩ := hbdd.exists_norm_le
  apply (integrable_const C).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC (v t) (mem_image_of_mem v ht)

private lemma continuous_comp_piecewise_integrable
    {n m : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b)
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (hx : ContinuousOn x (Icc a b))
    (hu : BertsekasPiecewiseContinuousOn u (Icc a b))
    (φ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) → E)
    (hφ : Continuous φ) :
    IntervalIntegrable (fun t => φ (x t, u t)) volume a b := by
  obtain ⟨hbu, F, hcu⟩ := hu
  apply integrable_of_bounded_continuous_off_finset hab _ F
  · exact hφ.comp_continuousOn ((hx.mono sdiff_subset).prodMk hcu)
  · have hK := (isCompact_Icc.image_of_continuousOn hx).prod hbu.isCompact_closure
    apply (hK.image hφ).isBounded.subset
    rintro z ⟨t, ht, rfl⟩
    exact mem_image_of_mem φ ⟨mem_image_of_mem x ht, subset_closure (mem_image_of_mem u ht)⟩

set_option backward.isDefEq.respectTransparency false in
private lemma hamiltonian_gradient
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (z : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin m))
    (p : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => BertsekasHamiltonian M y v p) z =
      ContinuousLinearMap.adjoint
        ((fderiv ℝ (Function.uncurry M.f) (z, v)).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))) p +
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
        ((fderiv ℝ (Function.uncurry M.g) (z, v)).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))) := by
  let A := (fderiv ℝ (Function.uncurry M.f) (z, v)).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let D := (fderiv ℝ (Function.uncurry M.g) (z, v)).comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  have hpair : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => (y, v))
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) z := by
    convert (hasFDerivAt_id z).prodMk (hasFDerivAt_const v z) using 1 <;> rfl
  have hF : HasFDerivAt (fun y => M.f y v) A z := by
    simpa [A, Function.comp_def] using
      ((hf.differentiable one_ne_zero (z, v)).hasFDerivAt).comp z hpair
  have hG : HasFDerivAt (fun y => M.g y v) D z := by
    simpa [D, Function.comp_def] using
      ((hg.differentiable one_ne_zero (z, v)).hasFDerivAt).comp z hpair
  have hH : HasFDerivAt (fun y => BertsekasHamiltonian M y v p)
      (D + (innerSL ℝ p).comp A) z :=
    hG.add ((innerSL ℝ p).hasFDerivAt.comp z hF)
  rw [hH.hasGradientAt.gradient]
  apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).injective
  ext w
  simp only [map_add, add_apply,
    LinearIsometryEquiv.apply_symm_apply, InnerProductSpace.toDual_apply_apply]
  change D w + ⟪p, A w⟫ = ⟪ContinuousLinearMap.adjoint A p, w⟫ + D w
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact add_comm _ _

theorem solution
    {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (u : ℝ → EuclideanSpace ℝ (Fin m))
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hu : BertsekasPiecewiseContinuousOn u (Set.Icc 0 M.T))
    (hx : ContinuousOn x (Set.Icc 0 M.T))
    (q : EuclideanSpace ℝ (Fin n)) :
    ∃ (p : ℝ → EuclideanSpace ℝ (Fin n)) (F : Finset ℝ),
      ContinuousOn p (Set.Icc 0 M.T) ∧ p M.T = q ∧
      ∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        HasDerivAt p
          (-gradient (fun y => BertsekasHamiltonian M y (u t) (p t)) (x t)) t := by
  classical
  let B : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := fun z =>
    ContinuousLinearMap.adjoint ((fderiv ℝ (Function.uncurry M.f) z).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))))
  let r : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →
      EuclideanSpace ℝ (Fin n) := fun z =>
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      ((fderiv ℝ (Function.uncurry M.g) z).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))))
  have hBcont : Continuous B :=
    ContinuousLinearMap.adjoint.continuous.comp
      ((hf.continuous_fderiv one_ne_zero).clm_comp continuous_const)
  have hrcont : Continuous r :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      ((hg.continuous_fderiv one_ne_zero).clm_comp continuous_const)
  have hBi := continuous_comp_piecewise_integrable M.hT.le x u hx hu B hBcont
  have hri := continuous_comp_piecewise_integrable M.hT.le x u hx hu r hrcont
  have hgcont : ContinuousOn (fun t => q + ∫ s in t..M.T, r (x s, u s)) (Icc 0 M.T) := by
    apply continuousOn_const.add
    have hi : IntegrableOn (fun s => r (x s, u s)) (uIcc 0 M.T) volume := by
      rw [uIcc_of_le M.hT.le]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le M.hT.le).mp hri
    simpa [uIcc_of_le M.hT.le] using intervalIntegral.continuousOn_primitive_interval_left hi
  obtain ⟨p, hp, hpInt⟩ := volterra_surjective 0 M.T M.hT
    (fun t => B (x t, u t)) hBi _ hgcont
  have hBpi := integral_apply_integrable M.hT.le hBi hp
  let k : ℝ → EuclideanSpace ℝ (Fin n) := fun t => B (x t, u t) (p t) + r (x t, u t)
  have hki : IntervalIntegrable k volume 0 M.T := hBpi.add hri
  have hpEq (t : ℝ) (ht : t ∈ Icc 0 M.T) :
      p t = q + ∫ s in t..M.T, k s := by
    have hsub : uIcc t M.T ⊆ uIcc 0 M.T :=
      uIcc_subset_uIcc (by simpa [uIcc_of_le M.hT.le] using ht) right_mem_uIcc
    rw [hpInt t ht, intervalIntegral.integral_add (hBpi.mono_set hsub) (hri.mono_set hsub)]
    abel
  obtain ⟨_, F, huc⟩ := hu
  have hpair : ContinuousOn (fun t => (x t, u t)) (Icc 0 M.T \ (F : Set ℝ)) :=
    (hx.mono sdiff_subset).prodMk huc
  have hkc : ContinuousOn k (Icc 0 M.T \ (F : Set ℝ)) :=
    ((hBcont.comp_continuousOn hpair).clm_apply (hp.mono sdiff_subset)).add
      (hrcont.comp_continuousOn hpair)
  refine ⟨p, F ∪ {0, M.T}, hp, ?_, ?_⟩
  · simpa using hpEq M.T ⟨M.hT.le, le_rfl⟩
  · intro t ht
    have htF : t ∉ F ∧ t ≠ 0 ∧ t ≠ M.T := by simpa [and_assoc, and_comm, and_left_comm] using ht.2
    have htI : t ∈ Ioo 0 M.T :=
      ⟨lt_of_le_of_ne ht.1.1 (Ne.symm htF.2.1), lt_of_le_of_ne ht.1.2 htF.2.2⟩
    have hnhds : Icc 0 M.T ∈ 𝓝 t := Icc_mem_nhds htI.1 htI.2
    have hreg : Icc 0 M.T \ (F : Set ℝ) ∈ 𝓝 t :=
      inter_mem hnhds (F.finite_toSet.isClosed.isOpen_compl.mem_nhds htF.1)
    have hkAt : ContinuousAt k t := hkc.continuousAt hreg
    have hkmeas : StronglyMeasurableAtFilter k (𝓝 t) volume :=
      ⟨Icc 0 M.T, hnhds,
        ((intervalIntegrable_iff_integrableOn_Icc_of_le M.hT.le).mp hki).aestronglyMeasurable⟩
    have hkt : IntervalIntegrable k volume t M.T :=
      hki.mono_set (uIcc_subset_uIcc
        (by simpa [uIcc_of_le M.hT.le] using ht.1) right_mem_uIcc)
    have hd := (intervalIntegral.integral_hasDerivAt_left hkt hkmeas hkAt).const_add q
    have hd' : HasDerivAt p (-k t) t := hd.congr_of_eventuallyEq
      (by filter_upwards [hnhds] with s hs using hpEq s hs)
    simpa only [hamiltonian_gradient M hf hg, k, B, r] using hd'
