-- Prove2me | solution 1 for ChanceStateCtrl.AlmostSure.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:38:44.168182+00:00
-- url     : https://prove2.me/submissions/d7b38b43-8c06-4dc5-9f00-05a810145322

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory Filter Topology

namespace ChanceStateCtrl.AlmostSure.L37Aux
open ChanceStateCtrl.AlmostSure

variable {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
  {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem Bconst_ae (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (h : ChanceStateCtrl.PDE.L2 D) :
    ∀ᵐ ω ∂P, (Ainv.compLp (Bconst P h) : Linf D P) ω = Ainv h := by
  filter_upwards [Ainv.coeFn_compLp (Bconst P h), Lp.coeFn_const (p := ⊤) (μ := P) h]
    with ω h1 h2
  rw [h1]
  simp only [Bconst] at *
  rw [h2]; rfl

theorem Ssol_ae (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (u : ChanceStateCtrl.PDE.L2 D) :
    ∀ᵐ ω ∂P, Ssol P Ainv ftil u ω = Ainv (u + ftil ω) := by
  filter_upwards [Ainv.coeFn_compLp (Bconst P u + ftil), Lp.coeFn_add (Bconst P u) ftil,
    Lp.coeFn_const (p := ⊤) (μ := P) u] with ω h1 h2 h3
  simp only [Ssol]
  rw [h1, h2]
  simp only [Pi.add_apply, Bconst]
  rw [h3]; rfl

theorem constLinf_ae (c : C(closure D, ℝ)) :
    ∀ᵐ ω ∂P, (constLinf P c : Linf D P) ω = c := by
  filter_upwards [Lp.coeFn_const (p := ⊤) (μ := P) c] with ω h
  simp only [constLinf]; rw [h]; rfl

theorem Gop_ae (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (u : ChanceStateCtrl.PDE.L2 D) :
    ∀ᵐ ω ∂P, Gop P Ainv ftil α u ω =
      Ainv (u + ftil ω) - ContinuousMap.const (closure D) α := by
  filter_upwards [Lp.coeFn_sub (Ssol P Ainv ftil u) (constLinf P (ContinuousMap.const (closure D) α)),
    Ssol_ae P Ainv ftil u, constLinf_ae P (ContinuousMap.const (closure D) α)] with ω h1 h2 h3
  simp only [Gop]
  rw [h1, Pi.sub_apply, h2, h3]

theorem convex_grad_ineq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ)
    (hFconv : ConvexOn ℝ Set.univ F) (hFd : Differentiable ℝ F) (x y : E) :
    F x + fderiv ℝ F x (y - x) ≤ F y := by
  set h := y - x
  let g : ℝ → ℝ := fun t => F (x + t • h)
  have hg : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
    have := hFconv.2 (Set.mem_univ (x + s • h)) (Set.mem_univ (x + t • h)) ha hb hab
    obtain rfl : b = 1 - a := by linarith
    simp only [g, smul_eq_mul]
    rw [smul_eq_mul, smul_eq_mul] at this
    convert this using 2
    module
  have hd : HasDerivAt g (fderiv ℝ F x h) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
    have h2 : HasFDerivAt F (fderiv ℝ F x) (x + (0 : ℝ) • h) := by
      simpa using (hFd x).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  simp only [slope_def_field, g] at this
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one, h] at this
  have hxy : x + (y - x) = y := by abel
  rw [hxy] at this
  simp only [h]
  linarith

theorem real_H1 {a c : ℝ} (H : ∀ t : ℝ, 0 < t → a + t * c ≤ 0) : a ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < |c| + 1 := by positivity
  set t := a / (|c| + 1) with ht
  have htpos : 0 < t := div_pos hcon hpos
  have hta : t * (|c| + 1) = a := by rw [ht]; field_simp
  have h1 := H t htpos
  have h2 : t * (-|c|) ≤ t * c := mul_le_mul_of_nonneg_left (neg_abs_le c) htpos.le
  nlinarith

theorem real_H2 {a c : ℝ} (H : ∀ t : ℝ, 0 < t → a + t * c ≤ 0) : c ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  have h1 := H ((|a| + 1) / c) (by positivity)
  have : (|a| + 1) / c * c = |a| + 1 := by field_simp
  rw [this] at h1
  linarith [neg_abs_le a]

theorem ae_norm_le_Linf {E : Type*} [NormedAddCommGroup E] (f : Lp E ⊤ P) :
    ∀ᵐ ω ∂P, ‖f ω‖ ≤ ‖f‖ := by
  have hfin : eLpNormEssSup f P ≠ ⊤ := by
    have := Lp.eLpNorm_lt_top f
    rw [eLpNorm_exponent_top] at this
    exact this.ne
  filter_upwards [ae_le_eLpNormEssSup (f := fun ω => f ω) (μ := P)] with ω hω
  rw [Lp.norm_def, eLpNorm_exponent_top]
  have := ENNReal.toReal_mono hfin hω
  simpa using this

theorem Kcone_int (k : Linf D P) (hk : k ∈ Kcone D P) {δ : ℝ} (hδ : 0 < δ) :
    k + constLinf P (ContinuousMap.const (closure D) (-δ)) ∈ interior (Kcone D P) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨δ / 2, by positivity, fun z hz => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hz
  show ∀ᵐ ω ∂P, ∀ x : closure D, z ω x ≤ 0
  have hk' : ∀ᵐ ω ∂P, ∀ x : closure D, k ω x ≤ 0 := hk
  filter_upwards [ae_norm_le_Linf P (z - (k + constLinf P (ContinuousMap.const (closure D) (-δ)))),
    Lp.coeFn_sub z (k + constLinf P (ContinuousMap.const (closure D) (-δ))),
    Lp.coeFn_add k (constLinf P (ContinuousMap.const (closure D) (-δ))),
    constLinf_ae P (ContinuousMap.const (closure D) (-δ)), hk'] with ω h1 h2 h3 h4 h5 x
  rw [h2, Pi.sub_apply, h3, Pi.add_apply, h4] at h1
  have h6 := (ContinuousMap.norm_coe_le_norm (z ω - (k ω + ContinuousMap.const (closure D) (-δ))) x)
  have h7 := le_abs_self ((z ω - (k ω + ContinuousMap.const (closure D) (-δ))) x)
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.const_apply,
    Real.norm_eq_abs] at h6 h7
  linarith [h5 x]

theorem Kcone_convex : Convex ℝ (Kcone D P) := by
  intro y1 h1 y2 h2 a b ha hb hab
  have h1' : ∀ᵐ ω ∂P, ∀ x : closure D, y1 ω x ≤ 0 := h1
  have h2' : ∀ᵐ ω ∂P, ∀ x : closure D, y2 ω x ≤ 0 := h2
  show ∀ᵐ ω ∂P, ∀ x : closure D, (a • y1 + b • y2) ω x ≤ 0
  filter_upwards [h1', h2', Lp.coeFn_add (a • y1) (b • y2), Lp.coeFn_smul a y1,
    Lp.coeFn_smul b y2] with ω e1 e2 e3 e4 e5 x
  rw [e3, Pi.add_apply, e4, e5]
  simp only [Pi.smul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
  nlinarith [e1 x, e2 x]

theorem Kcone_smul {k : Linf D P} (hk : k ∈ Kcone D P) {r : ℝ} (hr : 0 ≤ r) :
    r • k ∈ Kcone D P := by
  have hk' : ∀ᵐ ω ∂P, ∀ x : closure D, k ω x ≤ 0 := hk
  show ∀ᵐ ω ∂P, ∀ x : closure D, (r • k) ω x ≤ 0
  filter_upwards [hk', Lp.coeFn_smul r k] with ω e1 e2 x
  rw [e2]
  simp only [Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  nlinarith [e1 x]

theorem Kcone_zero : (0 : Linf D P) ∈ Kcone D P := by
  show ∀ᵐ ω ∂P, ∀ x : closure D, (0 : Linf D P) ω x ≤ 0
  filter_upwards [Lp.coeFn_zero C(closure D, ℝ) ⊤ P] with ω h x
  rw [h]; simp

theorem constLinf_smul (t : ℝ) :
    constLinf P (ContinuousMap.const (closure D) (-t)) =
      t • constLinf P (ContinuousMap.const (closure D) (-1)) := by
  apply Lp.ext
  filter_upwards [constLinf_ae P (ContinuousMap.const (closure D) (-t)),
    Lp.coeFn_smul t (constLinf P (ContinuousMap.const (closure D) (-1))),
    constLinf_ae P (ContinuousMap.const (closure D) (-1))] with ω h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3]
  ext x; simp

theorem Gop_affine (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (u h : ChanceStateCtrl.PDE.L2 D) (t : ℝ) :
    Gop P Ainv ftil α (u + t • h) = Gop P Ainv ftil α u + t • Ainv.compLp (Bconst P h) := by
  apply Lp.ext
  filter_upwards [Gop_ae P Ainv ftil α (u + t • h), Gop_ae P Ainv ftil α u,
    Lp.coeFn_add (Gop P Ainv ftil α u) (t • Ainv.compLp (Bconst P h)),
    Lp.coeFn_smul t (Ainv.compLp (Bconst P h) : Linf D P), Bconst_ae P Ainv h] with ω e1 e2 e3 e4 e5
  rw [e1, e3, Pi.add_apply, e2, e4, Pi.smul_apply, e5, map_add, map_add, map_add, map_smul]
  abel

theorem Gop_convex (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (u1 u2 : ChanceStateCtrl.PDE.L2 D)
    (a b : ℝ) (hab : a + b = 1) :
    Gop P Ainv ftil α (a • u1 + b • u2) = a • Gop P Ainv ftil α u1 + b • Gop P Ainv ftil α u2 := by
  apply Lp.ext
  filter_upwards [Gop_ae P Ainv ftil α (a • u1 + b • u2), Gop_ae P Ainv ftil α u1,
    Gop_ae P Ainv ftil α u2,
    Lp.coeFn_add (a • Gop P Ainv ftil α u1) (b • Gop P Ainv ftil α u2),
    Lp.coeFn_smul a (Gop P Ainv ftil α u1), Lp.coeFn_smul b (Gop P Ainv ftil α u2)]
    with ω e1 e2 e3 e4 e5 e6
  rw [e1, e4, Pi.add_apply, e5, e6, Pi.smul_apply, Pi.smul_apply, e2, e3]
  obtain rfl : b = 1 - a := by linarith
  simp only [map_add, map_smul]
  have hc : ContinuousMap.const (closure D) α =
      a • ContinuousMap.const (closure D) α + (1 - a) • ContinuousMap.const (closure D) α := by
    rw [← add_smul]; simp
  conv_lhs => rw [hc]
  module

end ChanceStateCtrl.AlmostSure.L37Aux

open ChanceStateCtrl.AlmostSure ChanceStateCtrl.AlmostSure.L37Aux

theorem solution {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))}
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hd : d = 1 ∨ d = 2 ∨ d = 3)
    (hS : ChanceStateCtrl.PDE.IsClassS D) [CompactSpace (closure D)]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ)) (hA : IsSolutionOperator D Ainv)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (F : ChanceStateCtrl.PDE.L2 D → ℝ)
    (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : ContDiff ℝ 1 F)
    (hCQ : CQ P Ainv ftil α) (us : ChanceStateCtrl.PDE.L2 D) :
    ChanceStateCtrl.General.IsSolution (feasible P Ainv ftil α) F us ↔
      ∃ lamStar : StrongDual ℝ (Linf D P),
        (∀ h : ChanceStateCtrl.PDE.L2 D, fderiv ℝ F us h + lamStar (Ainv.compLp (Bconst P h)) = 0) ∧
        Gop P Ainv ftil α us ∈ Kcone D P ∧ lamStar ∈ Kpolar D P ∧
        lamStar (Gop P Ainv ftil α us) = 0 := by
  have hFd : Differentiable ℝ F := hFdiff.differentiable (by norm_num)
  set e : Linf D P := constLinf P (ContinuousMap.const (closure D) (-1)) with he
  have hTdiff : ∀ u v : ChanceStateCtrl.PDE.L2 D,
      Ainv.compLp (Bconst P (v - u)) = (Gop P Ainv ftil α) v - (Gop P Ainv ftil α) u := by
    intro u v
    have := Gop_affine P Ainv ftil α u (v - u) 1
    rw [one_smul, one_smul, add_sub_cancel] at this
    rw [this]; abel
  have hint : ∀ k ∈ (Kcone D P), ∀ t : ℝ, 0 < t → k + t • e ∈ interior (Kcone D P) := by
    intro k hk t ht
    rw [he, ← constLinf_smul]
    exact Kcone_int P k hk ht
  constructor
  · intro hsol
    have hfeas : (Gop P Ainv ftil α) us ∈ (Kcone D P) := hsol.1
    -- Slater point from the CQ
    obtain ⟨u0, hu0⟩ : ∃ u0, (Gop P Ainv ftil α) u0 ∈ interior (Kcone D P) := by
      have h0 : (0 : Linf D P) ∈ interior {w | ∃ u : ChanceStateCtrl.PDE.L2 D,
          ∃ k ∈ Kcone D P, w = Gop P Ainv ftil α u - k} := hCQ
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h0
      obtain ⟨ε, hε, hball⟩ := h0
      have hw : (ε / 2) • e ∈ Metric.ball (0 : Linf D P) ε := by
        rw [Metric.mem_ball, dist_zero_right, norm_smul, he]
        have h1 : ‖constLinf P (ContinuousMap.const (closure D) (-1))‖ ≤ 1 := by
          have := Lp.norm_const_le (p := ⊤) (μ := P) (ContinuousMap.const (closure D) (-1 : ℝ) : C(closure D, ℝ))
          simp only [constLinf] at this ⊢
          refine this.trans ?_
          simp only [ENNReal.toReal_top, div_zero, Real.rpow_zero, mul_one]
          rw [ContinuousMap.norm_eq_iSup_norm]
          simp only [ContinuousMap.const_apply, norm_neg, norm_one]
          exact Real.iSup_le (fun _ => le_rfl) zero_le_one
        have : ‖ε / 2‖ = ε / 2 := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        rw [this]
        nlinarith [norm_nonneg (constLinf P (ContinuousMap.const (closure D) (-1)))]
      obtain ⟨u0, k0, hk0, hw'⟩ := hball hw
      refine ⟨u0, ?_⟩
      have : (Gop P Ainv ftil α) u0 = k0 + (ε / 2) • e := by rw [hw']; abel
      rw [this]
      exact hint k0 hk0 (ε / 2) (by positivity)
    -- separation
    set A : Set (ℝ × Linf D P) := {p | ∃ u, F u - F us < p.1 ∧ (Gop P Ainv ftil α) u - p.2 ∈ interior (Kcone D P)} with hA
    have hAopen : IsOpen A := by
      have : A = ⋃ u, ({p : ℝ × Linf D P | F u - F us < p.1} ∩
          {p | (Gop P Ainv ftil α) u - p.2 ∈ interior (Kcone D P)}) := by
        ext p; simp [hA]
      rw [this]
      refine isOpen_iUnion fun u => IsOpen.inter ?_ ?_
      · exact isOpen_lt continuous_const continuous_fst
      · exact isOpen_interior.preimage (continuous_const.sub continuous_snd)
    have hAconv : Convex ℝ A := by
      rintro p1 ⟨u1, h11, h12⟩ p2 ⟨u2, h21, h22⟩ a b ha hb hab
      refine ⟨a • u1 + b • u2, ?_, ?_⟩
      · have hc := hFconv.2 (Set.mem_univ u1) (Set.mem_univ u2) ha hb hab
        simp only [smul_eq_mul] at hc
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        rcases ha.lt_or_eq with ha' | ha'
        · have hus : F us = a * F us + b * F us := by rw [← add_mul, hab, one_mul]
          nlinarith [mul_pos ha' (sub_pos.2 h11), mul_nonneg hb (sub_pos.2 h21).le]
        · subst ha'
          have : b = 1 := by linarith
          subst this
          simp only [zero_mul, zero_add, one_mul] at hc ⊢
          linarith
      · have : (Gop P Ainv ftil α) (a • u1 + b • u2) - (a • p1 + b • p2).2 =
            a • ((Gop P Ainv ftil α) u1 - p1.2) + b • ((Gop P Ainv ftil α) u2 - p2.2) := by
          rw [Gop_convex P Ainv ftil α u1 u2 a b hab]
          simp only [Prod.snd_add, Prod.smul_snd, smul_sub]
          abel
        rw [this]
        exact (Kcone_convex P).interior h12 h22 ha hb hab
    have h0A : ((0 : ℝ), (0 : Linf D P)) ∉ A := by
      rintro ⟨u, h1, h2⟩
      have hu : u ∈ feasible P Ainv ftil α := by
        show (Gop P Ainv ftil α) u ∈ (Kcone D P)
        simpa using interior_subset h2
      have := hsol.2 u hu
      simp at h1
      linarith
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hAconv hAopen h0A
    simp only [Prod.mk_zero_zero, map_zero] at hf
    set μ := f (1, 0) with hμ
    set ℓ : StrongDual ℝ (Linf D P) := f.comp (ContinuousLinearMap.inr ℝ ℝ (Linf D P)) with hℓ
    have hfs : ∀ (t : ℝ) (y : Linf D P), f (t, y) = t * μ + ℓ y := by
      intro t y
      have : ((t, y) : ℝ × Linf D P) = t • ((1 : ℝ), (0 : Linf D P)) + ((0 : ℝ), y) := by
        ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul]
      rfl
    have hI : ∀ u (s : ℝ) (k : Linf D P), 0 < s → k ∈ interior (Kcone D P) →
        (F u - F us + s) * μ + ℓ ((Gop P Ainv ftil α) u - k) < 0 := by
      intro u s k hs hk
      rw [← hfs]
      apply hf
      refine ⟨u, by simp; linarith, ?_⟩
      simpa using hk
    have he0 : e ∈ interior (Kcone D P) := by simpa using hint 0 (Kcone_zero P) 1 one_pos
    -- consequences
    have C1 : μ ≤ 0 := by
      apply real_H2 (a := ℓ ((Gop P Ainv ftil α) us - e))
      intro t ht
      have := hI us t e ht he0
      simp at this; rw [map_sub]; linarith
    have C2 : ∀ k ∈ (Kcone D P), ℓ ((Gop P Ainv ftil α) us) ≤ ℓ k := by
      intro k hk
      have : ℓ ((Gop P Ainv ftil α) us) - ℓ k ≤ 0 := by
        apply real_H1 (c := μ - ℓ e)
        intro t ht
        have := hI us t (k + t • e) ht (hint k hk t ht)
        simp only [sub_self, zero_add, map_sub, map_add, map_smul, smul_eq_mul] at this
        nlinarith
      linarith
    have C3 : ∀ k ∈ (Kcone D P), 0 ≤ ℓ k := by
      intro k hk
      have : -ℓ k ≤ 0 := by
        apply real_H2 (a := ℓ ((Gop P Ainv ftil α) us))
        intro r hr
        have := C2 (r • k) (Kcone_smul P hk hr.le)
        rw [map_smul, smul_eq_mul] at this
        linarith
      linarith
    have C4 : ℓ ((Gop P Ainv ftil α) us) = 0 := by
      have h1 := C2 0 (Kcone_zero P)
      have h2 := C3 _ hfeas
      rw [map_zero] at h1
      linarith
    have C5 : μ ≠ 0 := by
      intro hμ0
      have := hI u0 1 ((Gop P Ainv ftil α) u0) one_pos hu0
      rw [hμ0, sub_self, map_zero] at this
      simp at this
    have C6 : ∀ u, (F u - F us) * μ + ℓ ((Gop P Ainv ftil α) u) ≤ 0 := by
      intro u
      apply real_H1 (c := μ - ℓ e)
      intro t ht
      have := hI u t (0 + t • e) ht (hint 0 (Kcone_zero P) t ht)
      simp only [zero_add, map_sub, map_smul, smul_eq_mul] at this
      nlinarith
    have hμneg : μ < 0 := lt_of_le_of_ne C1 C5
    refine ⟨μ⁻¹ • ℓ, ?_, hfeas, ?_, ?_⟩
    · intro h
      have hmin : ∀ u, F us ≤ F u + μ⁻¹ * ℓ ((Gop P Ainv ftil α) u) := by
        intro u
        have h1 := C6 u
        have h2 : μ⁻¹ * ((F u - F us) * μ + ℓ ((Gop P Ainv ftil α) u)) ≥ 0 :=
          mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 C1) h1
        rw [mul_add, ← mul_assoc, mul_comm μ⁻¹ (F u - F us), mul_assoc, inv_mul_cancel₀ C5,
          mul_one] at h2
        linarith
      let g : ℝ → ℝ := fun t => F (us + t • h) + t * (μ⁻¹ * ℓ (Ainv.compLp (Bconst P h)))
      have hgmin : IsLocalMin g 0 := by
        refine Filter.Eventually.of_forall fun t => ?_
        have := hmin (us + t • h)
        rw [Gop_affine P Ainv ftil α us h t, map_add, map_smul, C4, smul_eq_mul] at this
        simp only [g, zero_smul, add_zero, zero_mul]
        nlinarith
      have hgd : HasDerivAt g (fderiv ℝ F us h + μ⁻¹ * ℓ (Ainv.compLp (Bconst P h))) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => us + t • h) h 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add us
        have h2 : HasFDerivAt F (fderiv ℝ F us) (us + (0 : ℝ) • h) := by
          simpa using (hFd us).hasFDerivAt
        have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
        have h4 : HasDerivAt (fun t : ℝ => t * (μ⁻¹ * ℓ (Ainv.compLp (Bconst P h))))
            (μ⁻¹ * ℓ (Ainv.compLp (Bconst P h))) 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).mul_const (μ⁻¹ * ℓ (Ainv.compLp (Bconst P h)))
        exact h3.add h4
      have := hgmin.hasDerivAt_eq_zero hgd
      simpa using this
    · intro k hk
      show μ⁻¹ * ℓ k ≤ 0
      exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 C1) (C3 k hk)
    · show μ⁻¹ * ℓ ((Gop P Ainv ftil α) us) = 0
      rw [C4, mul_zero]
  · rintro ⟨lamStar, h53a, hfeas, hpol, hcompl⟩
    refine ⟨hfeas, fun u hu => ?_⟩
    have hu' : (Gop P Ainv ftil α) u ∈ (Kcone D P) := hu
    have hg := convex_grad_ineq F hFconv hFd us u
    have h1 := h53a (u - us)
    rw [hTdiff, map_sub lamStar, hcompl, sub_zero] at h1
    have h2 := hpol _ hu'
    linarith
