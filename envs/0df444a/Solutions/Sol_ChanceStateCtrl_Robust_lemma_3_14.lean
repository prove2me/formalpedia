-- Prove2me | solution 1 for ChanceStateCtrl.Robust.lemma_3_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T13:29:31.180115+00:00
-- url     : https://prove2.me/submissions/b3dd330b-1959-4309-935a-40396cf14a21

import Mathlib
import Definitions.Def_ChanceStateCtrl_Robust_Setting

open MeasureTheory
open scoped CompactlySupported
open ChanceStateCtrl.Robust

/-- Gradient inequality for a convex function differentiable at `x`. -/
private lemma conv_grad_ineq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    (hc : ConvexOn ℝ Set.univ F) {x : E} (hd : DifferentiableAt ℝ F x) (y : E) :
    F x + fderiv ℝ F x (y - x) ≤ F y := by
  set v := y - x with hv
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hx : HasFDerivAt F (fderiv ℝ F x) (x + (0:ℝ) • v) := by simpa using hd.hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => F (x + t • v)) (fderiv ℝ F x v) 0 :=
    hx.comp_hasDerivAt (0:ℝ) h1
  have hT := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left
    (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => (ne_of_gt ht : t ≠ 0)))
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      slope (fun t : ℝ => F (x + t • v)) 0 t ≤ F y - F x := by
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0:ℝ) < 1)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    rw [slope_def_field]
    simp only [zero_smul, add_zero, sub_zero]
    have heq : x + t • v = (1 - t) • x + t • y := by
      rw [hv, smul_sub, sub_smul, one_smul]; abel
    have hcv := hc.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
      (by ring : (1 - t) + t = 1)
    rw [smul_eq_mul, smul_eq_mul] at hcv
    rw [heq, div_le_iff₀ ht0]
    nlinarith
  have := le_of_tendsto hT hev
  linarith

theorem solution {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {Ξ : Set (EuclideanSpace ℝ (Fin m))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)] [CompactSpace Ξ]
    (f0 : ChanceStateCtrl.PDE.L2 D) (phi : Fin m → ChanceStateCtrl.PDE.L2 D)
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : ChanceStateCtrl.AlmostSure.IsSolutionOperator D Ainv) (α : ℝ)
    (F : ChanceStateCtrl.PDE.L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hCQ : RobustCQ (Ξ := Ξ) Ainv f0 phi α) (us : ChanceStateCtrl.PDE.L2 D) :
    ChanceStateCtrl.General.IsSolution (robustFeasible (Ξ := Ξ) Ainv f0 phi α) F us ↔
      ∃ lamStar : StrongDual ℝ C(closure D × Ξ, ℝ),
        (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + lamStar (AhatBhat Ainv h) = 0) ∧
        Ghat Ainv f0 phi α us ∈ Khat D Ξ ∧ lamStar ∈ KhatPolar D Ξ ∧
        lamStar (Ghat Ainv f0 phi α us) = 0 := by
  classical
  have hSh : ∀ u q, Shat (Ξ := Ξ) Ainv f0 phi u q
      = Ainv u q.1 + Ainv (srcTerm f0 phi q.2.1) q.1 := fun u q => by
    show Ainv (u + srcTerm f0 phi q.2.1) q.1 = _
    rw [map_add]; rfl
  have hG : ∀ u q, Ghat (Ξ := Ξ) Ainv f0 phi α u q = Shat Ainv f0 phi u q - α := fun u q => rfl
  have hfeas : ∀ u, u ∈ robustFeasible (Ξ := Ξ) Ainv f0 phi α ↔
      ∀ q, Shat (Ξ := Ξ) Ainv f0 phi u q ≤ α := by
    intro u
    show (∀ q, Ghat (Ξ := Ξ) Ainv f0 phi α u q ≤ 0) ↔ _
    simp only [hG, sub_nonpos]
  have hdiff : DifferentiableAt ℝ F us := (hFdiff.differentiable one_ne_zero).differentiableAt
  constructor
  · -- necessity
    rintro ⟨hus, hmin⟩
    set ℓ := fderiv ℝ F us with hℓ
    set g0 := Ghat (Ξ := Ξ) Ainv f0 phi α us with hg0
    have hg0le : ∀ q, g0 q ≤ 0 := hus
    have hGadd : ∀ h q, Ghat (Ξ := Ξ) Ainv f0 phi α (us + h) q = g0 q + Ainv h q.1 := by
      intro h q
      rw [hg0, hG, hG, hSh, hSh, map_add, ContinuousMap.add_apply]; ring
    -- first-order condition
    have hfo : ∀ h, (∀ q, g0 q + Ainv h q.1 ≤ 0) → 0 ≤ ℓ h := by
      intro h hh
      have hseg : segment ℝ us (us + h) ⊆ robustFeasible (Ξ := Ξ) Ainv f0 phi α := by
        rw [segment_eq_image']
        rintro _ ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
        show ∀ q, Ghat (Ξ := Ξ) Ainv f0 phi α _ q ≤ 0
        intro q
        rw [add_sub_cancel_left, hGadd, map_smul, ContinuousMap.smul_apply, smul_eq_mul]
        have h1 := hg0le q
        have h2 := hh q
        nlinarith
      have hy := mem_posTangentConeAt_of_segment_subset hseg
      have hmin' : IsMinOn F (robustFeasible (Ξ := Ξ) Ainv f0 phi α) us :=
        isMinOn_iff.2 hmin
      exact hmin'.localize.hasFDerivWithinAt_nonneg hdiff.hasFDerivAt.hasFDerivWithinAt hy
    -- the open convex set to separate from the origin
    let A : Set (ℝ × C(closure D × Ξ, ℝ)) :=
      {p | ∃ h, ∃ δ > 0, ℓ h < p.1 ∧ ∀ q, g0 q + Ainv h q.1 + δ ≤ p.2 q}
    have hA0 : (0 : ℝ × C(closure D × Ξ, ℝ)) ∉ A := by
      rintro ⟨h, δ, hδ, h1, h2⟩
      have := hfo h (fun q => by have := h2 q; simp at this; linarith)
      simp at h1; linarith
    have hAopen : IsOpen A := by
      rw [isOpen_iff_mem_nhds]
      rintro ⟨t, y⟩ ⟨h, δ, hδ, h1, h2⟩
      have hev : ∀ᶠ p in nhds (t, y), ℓ h < p.1 ∧ p.2 ∈ Metric.ball y (δ / 2) :=
        ((continuous_fst.tendsto (t, y)).eventually (lt_mem_nhds h1)).and
          ((continuous_snd.tendsto (t, y)).eventually (Metric.ball_mem_nhds y (half_pos hδ)))
      filter_upwards [hev] with p hp
      obtain ⟨hp1, hp2⟩ := hp
      refine ⟨h, δ / 2, half_pos hδ, hp1, fun q => ?_⟩
      have h3 := ContinuousMap.dist_apply_le_dist (f := p.2) (g := y) q
      have h4 := Metric.mem_ball.1 hp2
      have h5 := h2 q
      rw [Real.dist_eq] at h3
      have h6 := (abs_lt.1 (lt_of_le_of_lt h3 h4)).1
      simp only at h5
      linarith
    have hAconv : Convex ℝ A := by
      rintro p ⟨h, δ, hδ, h1, h2⟩ p' ⟨h', δ', hδ', h1', h2'⟩ a b ha hb hab
      refine ⟨a • h + b • h', min δ δ', lt_min hδ hδ', ?_, fun q => ?_⟩
      · simp only [map_add, map_smul, smul_eq_mul, Prod.fst_add, Prod.smul_fst]
        rcases ha.eq_or_lt with rfl | ha'
        · simp at hab; subst hab; simp; linarith
        · nlinarith
      · simp only [map_add, map_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply,
          smul_eq_mul, Prod.snd_add, Prod.smul_snd]
        have e1 := mul_le_mul_of_nonneg_left (h2 q) ha
        have e2 := mul_le_mul_of_nonneg_left (h2' q) hb
        have e3 := mul_le_mul_of_nonneg_left (min_le_left δ δ') ha
        have e4 := mul_le_mul_of_nonneg_left (min_le_right δ δ') hb
        have e5 : g0 q = a * g0 q + b * g0 q := by rw [← add_mul, hab, one_mul]
        have e6 : min δ δ' = a * min δ δ' + b * min δ δ' := by rw [← add_mul, hab, one_mul]
        nlinarith
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hAconv hAopen hA0
    rw [map_zero] at hf
    set β := f ((1 : ℝ), (0 : C(closure D × Ξ, ℝ))) with hβ
    let lam : C(closure D × Ξ, ℝ) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inr ℝ ℝ _)
    have hsplit : ∀ t y, f (t, y) = t * β + lam y := by
      intro t y
      have : ((t, y) : ℝ × C(closure D × Ξ, ℝ)) = t • ((1 : ℝ), (0 : C(closure D × Ξ, ℝ)))
          + ((0 : ℝ), y) := by ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul]
      rfl
    have hmem : ∀ h δ t (y : C(closure D × Ξ, ℝ)), 0 < δ → ℓ h < t →
        (∀ q, g0 q + Ainv h q.1 + δ ≤ y q) → t * β + lam y < 0 := by
      intro h δ t y hδ ht hy
      rw [← hsplit]; exact hf _ ⟨h, δ, hδ, ht, hy⟩
    let one : C(closure D × Ξ, ℝ) := ContinuousMap.const _ 1
    have hbase : ∀ s : ℝ, 0 ≤ s → ∀ z : C(closure D × Ξ, ℝ), (∀ q, 0 ≤ z q) →
        (1 + s) * β + lam (g0 + one + z) < 0 := by
      intro s hs z hz
      refine hmem 0 1 (1 + s) _ one_pos (by simp; linarith) (fun q => ?_)
      simp [one]; linarith [hz q]
    -- positivity of `-lam`
    have hlampos : ∀ z : C(closure D × Ξ, ℝ), (∀ q, 0 ≤ z q) → lam z ≤ 0 := by
      intro z hz
      by_contra hc
      push Not at hc
      obtain ⟨N, hN⟩ := exists_nat_gt ((-(β + lam (g0 + one))) / lam z)
      have := hbase 0 le_rfl ((N : ℝ) • z) (fun q => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hz q))
      rw [map_add, map_smul, smul_eq_mul, add_zero, one_mul] at this
      rw [div_lt_iff₀ hc] at hN
      linarith
    have hβle : β ≤ 0 := by
      by_contra hc
      push Not at hc
      obtain ⟨N, hN⟩ := exists_nat_gt ((-(β + lam (g0 + one + 0))) / β)
      have := hbase N (by positivity) 0 (fun q => le_rfl)
      rw [div_lt_iff₀ hc] at hN
      nlinarith
    -- Slater point from the constraint qualification
    have hβne : β ≠ 0 := by
      intro hβ0
      have hCQ' := hCQ
      rw [RobustCQ, mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hCQ'
      obtain ⟨ε, hε, hball⟩ := hCQ'
      let w0 : C(closure D × Ξ, ℝ) := ContinuousMap.const _ (-(ε / 2))
      have hw0 : w0 ∈ Metric.ball (0 : C(closure D × Ξ, ℝ)) ε := by
        rw [mem_ball_zero_iff]
        refine lt_of_le_of_lt ((ContinuousMap.norm_le w0 (by linarith : (0:ℝ) ≤ ε / 2)).2
          (fun x => ?_)) (by linarith)
        simp [w0, abs_of_pos hε]
      obtain ⟨u0, k, hk, hw⟩ := hball hw0
      have hu0 : ∀ q, g0 q + Ainv (u0 - us) q.1 ≤ -(ε / 2) := by
        intro q
        rw [← hGadd, add_sub_cancel]
        have := congrArg (fun w : C(closure D × Ξ, ℝ) => w q) hw
        simp only [w0, ContinuousMap.const_apply, ContinuousMap.sub_apply] at this
        have := hk q
        linarith
      have := hmem (u0 - us) (ε / 4) (ℓ (u0 - us) + 1) (ContinuousMap.const _ (-(ε / 4)))
        (by linarith) (by linarith) (fun q => by have := hu0 q; simp only [ContinuousMap.const_apply]; linarith)
      rw [hβ0, mul_zero, zero_add] at this
      have hc : ContinuousMap.const (closure D × Ξ) (-(ε / 4)) =
          -(ContinuousMap.const (closure D × Ξ) (ε / 4)) := by ext; simp
      rw [hc, map_neg] at this
      have := hlampos (ContinuousMap.const _ (ε / 4)) (fun q => by simp; linarith)
      linarith
    have hβlt : β < 0 := lt_of_le_of_ne hβle hβne
    -- the key inequality
    have hkey : ∀ h, ℓ h * β + lam g0 + lam (AhatBhat Ainv h) ≤ 0 := by
      intro h
      by_contra hc
      push Not at hc
      set X0 := ℓ h * β + lam g0 + lam (AhatBhat Ainv h)
      set C := β + lam one
      set δ := X0 / (|C| + 1) with hδdef
      have hδ : 0 < δ := div_pos hc (by positivity)
      have hδm : δ * (|C| + 1) = X0 := div_mul_cancel₀ _ (by positivity)
      have := hmem h δ (ℓ h + δ) (g0 + AhatBhat Ainv h + δ • one) hδ (by linarith)
        (fun q => by simp [one, AhatBhat])
      rw [map_add, map_add, map_smul, smul_eq_mul] at this
      have e1 := mul_le_mul_of_nonneg_left (neg_abs_le C) hδ.le
      have e2 : (ℓ h + δ) * β + (lam g0 + lam (AhatBhat Ainv h) + δ * lam one) = X0 + δ * C := by
        simp only [X0, C]; ring
      nlinarith
    have hA0' : AhatBhat (Ξ := Ξ) Ainv 0 = 0 := by ext; simp [AhatBhat]
    have hAneg : ∀ h, AhatBhat (Ξ := Ξ) Ainv (-h) = -AhatBhat Ainv h := by
      intro h; ext; simp [AhatBhat]
    have hlg0 : lam g0 = 0 := by
      have h1 := hkey 0
      rw [map_zero, hA0', map_zero, zero_mul] at h1
      have h2 := hlampos (-g0) (fun q => by simp; linarith [hg0le q])
      rw [map_neg] at h2
      linarith
    have hlin : ∀ h, ℓ h * β + lam (AhatBhat Ainv h) = 0 := by
      intro h
      have h1 := hkey h
      have h2 := hkey (-h)
      rw [map_neg, hAneg, map_neg] at h2
      linarith
    refine ⟨β⁻¹ • lam, fun h => ?_, hus, fun y hy => ?_, ?_⟩
    · simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      have := hlin h
      field_simp
      linarith
    · simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      have h2 := hlampos (-y) (fun q => by simp; linarith [hy q])
      rw [map_neg] at h2
      exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 hβle) (by linarith)
    · simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hlg0, mul_zero]
  · -- sufficiency
    rintro ⟨lamStar, ha, hus, hpol, hcomp⟩
    refine ⟨hus, fun u hu => ?_⟩
    have hg := conv_grad_ineq hFconv hdiff u
    have e1 := ha (u - us)
    have hpt : AhatBhat (Ξ := Ξ) Ainv (u - us) = Ghat Ainv f0 phi α u - Ghat Ainv f0 phi α us := by
      ext q
      show Ainv (u - us) q.1 = Ghat (Ξ := Ξ) Ainv f0 phi α u q - Ghat (Ξ := Ξ) Ainv f0 phi α us q
      rw [hG, hG, hSh, hSh, map_sub, ContinuousMap.sub_apply]; ring
    rw [hpt, map_sub lamStar, hcomp] at e1
    have := hpol _ hu
    linarith
