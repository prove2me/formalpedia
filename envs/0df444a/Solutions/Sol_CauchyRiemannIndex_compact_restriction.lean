-- Prove2me | solution 1 for CauchyRiemannIndex.compact_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T08:38:24.843224+00:00
-- url     : https://prove2.me/submissions/49ca94cd-87ee-43d1-9b07-b67216af2880

import Mathlib
import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_exists_subseq_cauchy_of_support_bounded

-- ===== Scratch/CRRelBase.lean =====
/-!
# Periodic strip bounds and a cut-off in `t` (copied from `Scratch/CRLocPer`, renamed `crrp`)
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Set Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### Periodic functions: `L^p` over five periods -/

/-- The horizontal strip `ℝ × [k, k + 1)`. -/
def crrpS (k : ℤ) : Set (ℝ × ℝ) := univ ×ˢ Ico (k : ℝ) (k + 1)

lemma crrpS_floor {k : ℤ} {x : ℝ × ℝ} (h : x ∈ crrpS k) : ⌊x.2⌋ = k :=
  Int.floor_eq_iff.2 ⟨h.2.1, h.2.2⟩

lemma crrp_shift (G : ℝ × ℝ → ℝ≥0∞) (hG : ∀ s t, G (s, t + 1) = G (s, t)) (k : ℤ) :
    ∫⁻ x in crrpS k, G x = ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x := by
  set e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.addRight (k : ℝ))
  have he : ∀ x : ℝ × ℝ, e x = (x.1, x.2 + k) := fun x => rfl
  have hGk : ∀ x : ℝ × ℝ, G (e x) = G x := by
    rintro ⟨s, t⟩
    have hp : Function.Periodic (fun t => G (s, t)) 1 := fun t => hG s t
    have := hp.int_mul k t
    rw [he]
    simpa using this
  have mp : MeasurePreserving e (volume : Measure (ℝ × ℝ)) volume :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (measurePreserving_add_right (volume : Measure ℝ) (k : ℝ))
  have hpre : e ⁻¹' crrpS k = univ ×ˢ Ico (0 : ℝ) 1 := by
    ext ⟨s, t⟩
    simp only [crrpS, mem_preimage, he, mem_prod, mem_univ, true_and, mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h := mp.setLIntegral_comp_preimage_emb e.measurableEmbedding G (crrpS k)
  rw [hpre] at h
  rw [← h]
  exact setLIntegral_congr_fun (MeasurableSet.univ.prod measurableSet_Ico)
    (fun x _ => hGk x)

lemma crrp_five (G : ℝ × ℝ → ℝ≥0∞) (hG : ∀ s t, G (s, t + 1) = G (s, t)) :
    ∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, G x ≤ 5 * ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x := by
  have hsub : univ ×ˢ Ico (-2 : ℝ) 3 ⊆ ⋃ k ∈ Finset.Icc (-2 : ℤ) 2, crrpS k := by
    rintro ⟨s, t⟩ ⟨-, h1, h2⟩
    simp only [mem_iUnion, Finset.mem_Icc, exists_prop]
    refine ⟨⌊t⌋, ⟨?_, ?_⟩, ?_⟩
    · exact Int.le_floor.2 (by push_cast; linarith)
    · have : ⌊t⌋ < 3 := Int.floor_lt.2 (by push_cast; linarith)
      omega
    · exact ⟨mem_univ _, Int.floor_le t, Int.lt_floor_add_one t⟩
  have hd : (↑(Finset.Icc (-2 : ℤ) 2) : Set ℤ).PairwiseDisjoint crrpS := by
    intro k _ j _ hkj
    exact Set.disjoint_left.2 fun x hk hj => hkj (by rw [← crrpS_floor hk, ← crrpS_floor hj])
  have hm : ∀ k ∈ Finset.Icc (-2 : ℤ) 2, MeasurableSet (crrpS k) :=
    fun k _ => MeasurableSet.univ.prod measurableSet_Ico
  calc ∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, G x
      ≤ ∫⁻ x in ⋃ k ∈ Finset.Icc (-2 : ℤ) 2, crrpS k, G x := lintegral_mono_set hsub
    _ = ∑ k ∈ Finset.Icc (-2 : ℤ) 2, ∫⁻ x in crrpS k, G x := lintegral_biUnion_finset hd hm G
    _ = ∑ k ∈ Finset.Icc (-2 : ℤ) 2, ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x :=
        Finset.sum_congr rfl fun k _ => crrp_shift G hG k
    _ = 5 * ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, G x := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1

lemma crrp_eLpNorm_le {E : Type*} [NormedAddCommGroup E] (f : ℝ × ℝ → E)
    (hf : ∀ s t, f (s, t + 1) = f (s, t)) (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm f p (volume.restrict (univ ×ˢ Ico (-2 : ℝ) 3)) ≤ 5 * eLpNorm f p cylMeasure := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hpr : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp
    simpa using this
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have h5 := crrp_five (fun x => ‖f x‖ₑ ^ p.toReal) (fun s t => by simp only [hf])
  have hpos : 0 ≤ 1 / p.toReal := by positivity
  have hle1 : 1 / p.toReal ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hpr
  calc (∫⁻ x in univ ×ˢ Ico (-2 : ℝ) 3, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
      ≤ (5 * ∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow h5 hpos
    _ = (5 : ℝ≥0∞) ^ (1 / p.toReal) *
          (∫⁻ x in univ ×ˢ Ico (0 : ℝ) 1, ‖f x‖ₑ ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.mul_rpow_of_nonneg _ _ hpos
    _ ≤ 5 * (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂cylMeasure) ^ (1 / p.toReal) := by
        gcongr
        · calc (5 : ℝ≥0∞) ^ (1 / p.toReal) ≤ 5 ^ (1 : ℝ) :=
                ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hle1
            _ = 5 := ENNReal.rpow_one _
        · exact le_of_eq rfl

/-! ### The cut-off in `t` -/

/-- A bump in `t`, equal to `1` on `[-1/2, 3/2]` and supported in `[-3/2, 5/2]`. -/
def crrpBump : ContDiffBump (1 / 2 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The cut-off function `χ`. -/
def crrpχ : ℝ → ℝ := fun t => crrpBump t

lemma crrpχ_contDiff : ContDiff ℝ ∞ crrpχ := crrpBump.contDiff

lemma crrpχ_one {t : ℝ} (h1 : -1 / 2 ≤ t) (h2 : t ≤ 3 / 2) : crrpχ t = 1 := by
  apply crrpBump.one_of_mem_closedBall
  have : crrpBump.rIn = 1 := rfl
  rw [this, Metric.mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> linarith

lemma crrpχ_abs_le (t : ℝ) : |crrpχ t| ≤ 1 := by
  show |crrpBump t| ≤ 1
  rw [abs_le]; exact ⟨by linarith [crrpBump.nonneg (x := t)], crrpBump.le_one⟩

lemma crrpχ_zero {t : ℝ} (h : t ∉ Ico (-2 : ℝ) 3) : crrpχ t = 0 := by
  by_contra hne
  have : t ∈ Function.support crrpχ := hne
  have h' : t ∈ Metric.ball (1 / 2 : ℝ) crrpBump.rOut := by
    rw [← crrpBump.support_eq]; exact this
  have : crrpBump.rOut = 2 := rfl
  rw [this, Metric.mem_ball, Real.dist_eq, abs_lt] at h'
  apply h; constructor <;> linarith

lemma crrpχ_deriv_zero {t : ℝ} (h : t ∉ Ico (-2 : ℝ) 3) : deriv crrpχ t = 0 := by
  by_contra hne
  have h1 : t ∈ tsupport crrpχ := support_deriv_subset hne
  have h2 : t ∈ Metric.closedBall (1 / 2 : ℝ) crrpBump.rOut := by
    rw [← crrpBump.tsupport_eq]; exact h1
  have : crrpBump.rOut = 2 := rfl
  rw [this, Metric.mem_closedBall, Real.dist_eq, abs_le] at h2
  apply h; constructor <;> linarith

lemma crrpχ_deriv_bound : ∃ M : ℝ≥0, ∀ t, |deriv crrpχ t| ≤ M := by
  have hc : Continuous (deriv crrpχ) := crrpχ_contDiff.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv crrpχ) := crrpBump.hasCompactSupport.deriv
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C.toNNReal, fun t => (hC t).trans (Real.le_coe_toNNReal C)⟩

/-! ### Periodicity of derivatives -/

lemma crrp_fderiv_per {u : ℝ × ℝ → Vec n} (hper : ∀ s t, u (s, t + 1) = u (s, t)) (s t : ℝ) :
    fderiv ℝ u (s, t + 1) = fderiv ℝ u (s, t) := by
  have hfun : (fun y : ℝ × ℝ => u (y + ((0 : ℝ), (1 : ℝ)))) = u := by
    funext ⟨a, b⟩
    simp only [Prod.mk_add_mk, add_zero, hper]
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := ((s, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ))
  rw [hfun, Prod.mk_add_mk, add_zero] at h
  exact h.symm

end

end CauchyRiemannIndex

-- ===== Scratch/CRRelP.lean =====
/-!
# `compact_restriction`: cut off, move to `ℝ²`, apply the simultaneous compactness lemma
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Set Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### The coordinate map `ℝ² → ℝ × ℝ` -/

/-- `y ↦ (y 0, y 1)`. -/
def crrpT : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2))

lemma crrpT_apply (y : EuclideanSpace ℝ (Fin 2)) : crrpT y = (y 0, y 1) := rfl

lemma crrpT_mp : MeasurePreserving crrpT volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

lemma crrpT_norm_le : ‖crrpT‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
  rw [crrpT_apply, Prod.norm_def, one_mul]
  exact max_le (PiLp.norm_apply_le y 0) (PiLp.norm_apply_le y 1)

lemma crrp_norm_le_add (y : EuclideanSpace ℝ (Fin 2)) : ‖y‖ ≤ |y 0| + |y 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have h0 : 0 ≤ |y 0| + |y 1| := by positivity
  calc √(‖y 0‖ ^ 2 + ‖y 1‖ ^ 2) ≤ √((|y 0| + |y 1|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        nlinarith [abs_nonneg (y 0), abs_nonneg (y 1)]
    _ = |y 0| + |y 1| := Real.sqrt_sq h0

lemma crrp_norm_le_sum {ι : Type*} [Fintype ι] (z : EuclideanSpace ℝ ι) :
    ‖z‖ ≤ ∑ i, ‖z i‖ := by
  rw [EuclideanSpace.norm_eq]
  have h0 : 0 ≤ ∑ i, ‖z i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc √(∑ i, ‖z i‖ ^ 2) ≤ √((∑ i, ‖z i‖) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)
    _ = ∑ i, ‖z i‖ := Real.sqrt_sq h0

/-! ### The derivative of a map on `ℝ × ℝ` -/

lemma crrp_fderiv_le {u : ℝ × ℝ → Vec n} (x : ℝ × ℝ) :
    ‖fderiv ℝ u x‖ ≤ ‖partialS u x‖ + ‖partialT u x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : fderiv ℝ u x v = v.1 • partialS u x + v.2 • partialT u x := by
    simp only [partialS, partialT, ← map_smul, ← map_add]
    congr 1; ext <;> simp
  rw [hv]
  calc ‖v.1 • partialS u x + v.2 • partialT u x‖
      ≤ ‖v.1‖ * ‖partialS u x‖ + ‖v.2‖ * ‖partialT u x‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖v‖ * ‖partialS u x‖ + ‖v‖ * ‖partialT u x‖ := by
        gcongr
        · exact norm_fst_le v
        · exact norm_snd_le v
    _ = (‖partialS u x‖ + ‖partialT u x‖) * ‖v‖ := by ring

/-! ### The cut-off `ψ(s, t) = χ(s) θ(t)` -/

/-- A bump in `s`, equal to `1` for `|s| ≤ |R| + 1`, vanishing for `|s| ≥ |R| + 2`. -/
def crrpBumpS (R : ℝ) : ContDiffBump (0 : ℝ) :=
  ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩

/-- The cut-off on `ℝ × ℝ`. -/
def crrpψ (R : ℝ) (x : ℝ × ℝ) : ℝ := crrpBumpS R x.1 * crrpχ x.2

lemma crrpψ_contDiff (R : ℝ) : ContDiff ℝ ∞ (crrpψ R) :=
  ((crrpBumpS R).contDiff.comp contDiff_fst).mul (crrpχ_contDiff.comp contDiff_snd)

lemma crrpψ_abs_le (R : ℝ) (x : ℝ × ℝ) : |crrpψ R x| ≤ 1 := by
  rw [crrpψ, abs_mul]
  have h1 : |crrpBumpS R x.1| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [(crrpBumpS R).nonneg (x := x.1)], (crrpBumpS R).le_one⟩
  have h2 := crrpχ_abs_le x.2
  calc |crrpBumpS R x.1| * |crrpχ x.2| ≤ 1 * 1 := by gcongr
    _ = 1 := one_mul 1

lemma crrpχ_zero' {t : ℝ} (h : t ∉ Icc (-3 / 2 : ℝ) (5 / 2)) : crrpχ t = 0 := by
  show crrpBump t = 0
  apply crrpBump.zero_of_le_dist
  have : crrpBump.rOut = 2 := rfl
  rw [this, Real.dist_eq]
  simp only [mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma crrpψ_one (R : ℝ) {x : ℝ × ℝ} (hs : x.1 ∈ Icc (-R) R) (ht : x.2 ∈ Ico (0 : ℝ) 1) :
    crrpψ R x = 1 := by
  rw [crrpψ, crrpχ_one (by linarith [ht.1]) (by linarith [ht.2]), mul_one]
  apply (crrpBumpS R).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  show |x.1| ≤ |R| + 1
  have : |x.1| ≤ |R| := abs_le.2 ⟨by linarith [le_abs_self R, hs.1], by linarith [le_abs_self R, hs.2]⟩
  linarith

lemma crrpψ_compact (R : ℝ) : HasCompactSupport (crrpψ R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × ℝ) (|R| + 3)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le, Prod.norm_def, lt_max_iff] at hx
  rw [crrpψ]
  rcases hx with h | h
  · rw [(crrpBumpS R).zero_of_le_dist, zero_mul]
    show |R| + 2 ≤ dist x.1 0
    rw [Real.dist_eq, sub_zero]; rw [Real.norm_eq_abs] at h; linarith
  · rw [crrpχ_zero', mul_zero]
    rw [Real.norm_eq_abs] at h
    intro hm
    have : |x.2| ≤ 5 / 2 := abs_le.2 ⟨by linarith [hm.1], hm.2⟩
    linarith [abs_nonneg R]

lemma crrpψ_fderiv_bound (R : ℝ) : ∃ C : ℝ≥0, ∀ x, ‖fderiv ℝ (crrpψ R) x‖ ≤ C := by
  have hc : Continuous fun x => ‖fderiv ℝ (crrpψ R) x‖ :=
    ((crrpψ_contDiff R).continuous_fderiv (by simp)).norm
  have hs : HasCompactSupport fun x => ‖fderiv ℝ (crrpψ R) x‖ := ((crrpψ_compact R).fderiv (𝕜 := ℝ)).norm
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  refine ⟨C.toNNReal, fun x => ?_⟩
  have := hC x
  rw [norm_norm] at this
  exact this.trans (Real.le_coe_toNNReal C)

/-- Outside the strip `t ∈ [-2, 3)`, `ψ` and its derivative vanish. -/
lemma crrpψ_off (R : ℝ) {x : ℝ × ℝ} (hx : x.2 ∉ Ico (-2 : ℝ) 3) :
    crrpψ R x = 0 ∧ fderiv ℝ (crrpψ R) x = 0 := by
  have hU : IsOpen {y : ℝ × ℝ | y.2 ∉ Icc (-3 / 2 : ℝ) (5 / 2)} :=
    (isClosed_Icc.preimage continuous_snd).isOpen_compl
  have hxU : x ∈ {y : ℝ × ℝ | y.2 ∉ Icc (-3 / 2 : ℝ) (5 / 2)} := by
    intro hm; apply hx; constructor <;> linarith [hm.1, hm.2]
  have hev : crrpψ R =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    rw [crrpψ, crrpχ_zero' hy, mul_zero]
  refine ⟨hev.eq_of_nhds, ?_⟩
  rw [hev.fderiv_eq]; simp

/-! ### The cut-off components -/

/-- `w(s, t) = ψ(s, t) u_i(s, t)`. -/
def crrpW (R : ℝ) (u : ℝ × ℝ → Vec n) (i : Fin n ⊕ Fin n) (x : ℝ × ℝ) : ℝ :=
  crrpψ R x * EuclideanSpace.proj i (u x)

/-- `|u| + |∂ₛu| + |∂ₜu|`. -/
def crrpG (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) : ℝ := ‖u x‖ + ‖partialS u x‖ + ‖partialT u x‖

lemma crrp_proj_le (i : Fin n ⊕ Fin n) (z : Vec n) : ‖EuclideanSpace.proj i z‖ ≤ ‖z‖ :=
  PiLp.norm_apply_le z i

lemma crrp_projCLM_le (i : Fin n ⊕ Fin n) : ‖(EuclideanSpace.proj i : Vec n →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [one_mul]; exact crrp_proj_le i z

lemma crrpW_contDiff (R : ℝ) {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ ∞ u) (i : Fin n ⊕ Fin n) :
    ContDiff ℝ ∞ (crrpW R u i) :=
  (crrpψ_contDiff R).mul ((EuclideanSpace.proj i : Vec n →L[ℝ] ℝ).contDiff.comp hu)

lemma crrpW_le (R : ℝ) (u : ℝ × ℝ → Vec n) (i : Fin n ⊕ Fin n) (x : ℝ × ℝ) :
    ‖crrpW R u i x‖ ≤ (univ ×ˢ Ico (-2 : ℝ) 3).indicator (crrpG u) x := by
  by_cases hx : x.2 ∈ Ico (-2 : ℝ) 3
  · rw [indicator_of_mem (by exact ⟨mem_univ _, hx⟩), crrpW, norm_mul, crrpG]
    have h1 : ‖crrpψ R x‖ ≤ 1 := crrpψ_abs_le R x
    have h2 := crrp_proj_le i (u x)
    calc ‖crrpψ R x‖ * ‖EuclideanSpace.proj i (u x)‖ ≤ 1 * ‖u x‖ := by gcongr
      _ ≤ ‖u x‖ + ‖partialS u x‖ + ‖partialT u x‖ := by
          rw [one_mul]; linarith [norm_nonneg (partialS u x), norm_nonneg (partialT u x)]
  · rw [indicator_of_notMem (fun h => hx h.2), crrpW, (crrpψ_off R hx).1, zero_mul, norm_zero]

lemma crrpW_fderiv_le (R : ℝ) (C : ℝ≥0) (hC : ∀ x, ‖fderiv ℝ (crrpψ R) x‖ ≤ C)
    {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ ∞ u) (i : Fin n ⊕ Fin n) (x : ℝ × ℝ) :
    ‖fderiv ℝ (crrpW R u i) x‖ ≤
      (1 + (C : ℝ)) * (univ ×ˢ Ico (-2 : ℝ) 3).indicator (crrpG u) x := by
  have hψd : HasFDerivAt (crrpψ R) (fderiv ℝ (crrpψ R) x) x :=
    ((crrpψ_contDiff R).differentiable (by simp) x).hasFDerivAt
  have hud : HasFDerivAt (fun y => EuclideanSpace.proj i (u y))
      ((EuclideanSpace.proj i).comp (fderiv ℝ u x)) x :=
    (EuclideanSpace.proj i : Vec n →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hu.differentiable (by simp) x).hasFDerivAt)
  have hd := hψd.mul hud
  have hfd : fderiv ℝ (crrpW R u i) x = crrpψ R x • (EuclideanSpace.proj i).comp (fderiv ℝ u x) +
      EuclideanSpace.proj i (u x) • fderiv ℝ (crrpψ R) x := hd.fderiv
  rw [hfd]
  by_cases hx : x.2 ∈ Ico (-2 : ℝ) 3
  · rw [indicator_of_mem (by exact ⟨mem_univ _, hx⟩), crrpG]
    have hDu := crrp_fderiv_le (u := u) x
    have h1 : ‖crrpψ R x‖ ≤ 1 := crrpψ_abs_le R x
    have h2 : ‖(EuclideanSpace.proj i).comp (fderiv ℝ u x)‖ ≤ ‖fderiv ℝ u x‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by have := crrp_projCLM_le (n := n) i; nlinarith [norm_nonneg (fderiv ℝ u x)])
    have h3 := crrp_proj_le i (u x)
    have h4 := hC x
    have hC0 : (0 : ℝ) ≤ C := C.2
    calc ‖crrpψ R x • (EuclideanSpace.proj i).comp (fderiv ℝ u x) +
          EuclideanSpace.proj i (u x) • fderiv ℝ (crrpψ R) x‖
        ≤ ‖crrpψ R x‖ * ‖(EuclideanSpace.proj i).comp (fderiv ℝ u x)‖ +
            ‖EuclideanSpace.proj i (u x)‖ * ‖fderiv ℝ (crrpψ R) x‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
      _ ≤ 1 * (‖partialS u x‖ + ‖partialT u x‖) + ‖u x‖ * C := by
          gcongr
          exact h2.trans hDu
      _ ≤ (1 + (C : ℝ)) * (‖u x‖ + ‖partialS u x‖ + ‖partialT u x‖) := by
          nlinarith [norm_nonneg (u x), norm_nonneg (partialS u x), norm_nonneg (partialT u x)]
  · rw [indicator_of_notMem (fun h => hx h.2), (crrpψ_off R hx).1, (crrpψ_off R hx).2]
    simp

/-! ### `Lᵖ` bounds on `ℝ × ℝ` -/

lemma crrpG_per {u : ℝ × ℝ → Vec n} (hper : ∀ s t, u (s, t + 1) = u (s, t)) (s t : ℝ) :
    crrpG u (s, t + 1) = crrpG u (s, t) := by
  simp only [crrpG, partialS, partialT, hper, crrp_fderiv_per hper]

lemma crrpG_eLpNorm (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) :
    eLpNorm ((univ ×ˢ Ico (-2 : ℝ) 3).indicator (crrpG u)) p volume ≤ 5 * w1pNorm p u := by
  have hc : Continuous u := hu.1.continuous
  have hcD : Continuous (fderiv ℝ u) := hu.1.continuous_fderiv (by simp)
  have hcS : Continuous (partialS u) := hcD.clm_apply continuous_const
  have hcT : Continuous (partialT u) := hcD.clm_apply continuous_const
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (MeasurableSet.univ.prod measurableSet_Ico)]
  refine (crrp_eLpNorm_le _ (crrpG_per hu.2.1) p hp hp').trans ?_
  gcongr
  rw [w1pNorm]
  have hf := fun (f : ℝ × ℝ → Vec n) (hf : Continuous f) =>
    (hf.norm.aestronglyMeasurable : AEStronglyMeasurable (fun x => ‖f x‖) cylMeasure)
  calc eLpNorm (crrpG u) p cylMeasure
      ≤ eLpNorm (fun x => ‖u x‖ + ‖partialS u x‖) p cylMeasure +
          eLpNorm (fun x => ‖partialT u x‖) p cylMeasure :=
        eLpNorm_add_le ((hf u hc).add (hf _ hcS)) (hf _ hcT) hp
    _ ≤ eLpNorm (fun x => ‖u x‖) p cylMeasure + eLpNorm (fun x => ‖partialS u x‖) p cylMeasure +
          eLpNorm (fun x => ‖partialT u x‖) p cylMeasure := by
        gcongr; exact eLpNorm_add_le (hf u hc) (hf _ hcS) hp
    _ = _ := by simp only [eLpNorm_norm]

/-! ### The functions on `ℝ²` -/

/-- `v = w ∘ T`. -/
def crrpV (R : ℝ) (u : ℝ × ℝ → Vec n) (i : Fin n ⊕ Fin n) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  crrpW R u i ∘ crrpT

lemma crrpV_contDiff (R : ℝ) {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ ∞ u) (i : Fin n ⊕ Fin n) :
    ContDiff ℝ 1 (crrpV R u i) :=
  ((crrpW_contDiff R hu i).comp crrpT.contDiff).of_le (by simp)

lemma crrpV_fderiv_le (R : ℝ) {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ ∞ u) (i : Fin n ⊕ Fin n)
    (y : EuclideanSpace ℝ (Fin 2)) :
    ‖fderiv ℝ (crrpV R u i) y‖ ≤ ‖fderiv ℝ (crrpW R u i) (crrpT y)‖ := by
  have hw := ((crrpW_contDiff R hu i).differentiable (by simp) (crrpT y))
  rw [crrpV, fderiv_comp y hw crrpT.differentiableAt, crrpT.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have := crrpT_norm_le
  nlinarith [norm_nonneg (fderiv ℝ (crrpW R u i) (crrpT y))]

lemma crrpV_eLpNorm (R : ℝ) (u : ℝ × ℝ → Vec n) (hc : Continuous u) (i : Fin n ⊕ Fin n)
    (p : ℝ≥0∞) : eLpNorm (crrpV R u i) p volume = eLpNorm (crrpW R u i) p volume := by
  have hcw : Continuous (crrpW R u i) :=
    ((crrpψ_contDiff R).continuous).mul ((EuclideanSpace.proj i).continuous.comp hc)
  exact eLpNorm_comp_measurePreserving hcw.aestronglyMeasurable crrpT_mp

/-! ### The main argument -/

theorem crrp_main (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) (R : ℝ)
    (u : ℕ → ℝ × ℝ → Vec n) (hu : ∀ k, IsTestSection (u k)) (hb : ∀ k, w1pNorm p (u k) ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N,
      eLpNorm (u (φ i) - u (φ j)) p (cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)) < ε := by
  have hp1 : 1 ≤ p := hp.le
  obtain ⟨C, hC⟩ := crrpψ_fderiv_bound R
  set M : ℝ≥0 := 5 * (1 + C) with hM
  -- the hypotheses of the compactness lemma
  have hbd : ∀ k i, eLpNorm (crrpV R (u k) i) p volume ≤ M := by
    intro k i
    rw [crrpV_eLpNorm R (u k) (hu k).1.continuous i p]
    calc eLpNorm (crrpW R (u k) i) p volume
        ≤ eLpNorm ((univ ×ˢ Ico (-2 : ℝ) 3).indicator (crrpG (u k))) p volume :=
          eLpNorm_mono_real (crrpW_le R (u k) i)
      _ ≤ 5 * w1pNorm p (u k) := crrpG_eLpNorm p hp1 hp' (hu k)
      _ ≤ 5 * 1 := by gcongr; exact hb k
      _ ≤ M := by
          rw [hM, ENNReal.coe_mul]
          gcongr
          · norm_num
          · exact_mod_cast le_add_of_nonneg_right C.2
  have hdbd : ∀ k i, eLpNorm (fun y => ‖fderiv ℝ (crrpV R (u k) i) y‖) p volume ≤ M := by
    intro k i
    have hcD : Continuous fun x => ‖fderiv ℝ (crrpW R (u k) i) x‖ :=
      ((crrpW_contDiff R (hu k).1 i).continuous_fderiv (by simp)).norm
    calc eLpNorm (fun y => ‖fderiv ℝ (crrpV R (u k) i) y‖) p volume
        ≤ eLpNorm ((fun x => ‖fderiv ℝ (crrpW R (u k) i) x‖) ∘ crrpT) p volume :=
          eLpNorm_mono_real fun y => by
            rw [norm_norm]; exact crrpV_fderiv_le R (hu k).1 i y
      _ = eLpNorm (fun x => ‖fderiv ℝ (crrpW R (u k) i) x‖) p volume :=
          eLpNorm_comp_measurePreserving hcD.aestronglyMeasurable crrpT_mp
      _ ≤ eLpNorm (fun x => (1 + (C : ℝ)) *
            (univ ×ˢ Ico (-2 : ℝ) 3).indicator (crrpG (u k)) x) p volume :=
          eLpNorm_mono_real fun x => by
            rw [norm_norm]; exact crrpW_fderiv_le R C hC (hu k).1 i x
      _ = ‖(1 + (C : ℝ))‖ₑ *
            eLpNorm ((univ ×ˢ Ico (-2 : ℝ) 3).indicator (crrpG (u k))) p volume := by
          have hfun : (fun x => (1 + (C : ℝ)) *
              (univ ×ˢ Ico (-2 : ℝ) 3).indicator (crrpG (u k)) x) =
              (1 + (C : ℝ)) • (univ ×ˢ Ico (-2 : ℝ) 3).indicator (crrpG (u k)) := rfl
          rw [hfun, eLpNorm_const_smul]
      _ ≤ ‖(1 + (C : ℝ))‖ₑ * (5 * 1) := by
          gcongr
          exact (crrpG_eLpNorm p hp1 hp' (hu k)).trans (by gcongr; exact hb k)
      _ = M := by
          have hE : ‖(1 + (C : ℝ))‖ₑ = ((1 + C : ℝ≥0) : ℝ≥0∞) := by
            rw [Real.enorm_eq_ofReal (by positivity),
              show (1 + (C : ℝ)) = ((1 + C : ℝ≥0) : ℝ) by push_cast; ring,
              ENNReal.ofReal_coe_nnreal]
          rw [hE, hM, mul_one, ENNReal.coe_mul, mul_comm]
          norm_num
  have hsupp : ∀ k i y, |R| + 5 < ‖y‖ → crrpV R (u k) i y = 0 := by
    intro k i y hy
    have h := crrp_norm_le_add y
    show crrpψ R (crrpT y) * _ = 0
    rw [crrpT_apply, crrpψ]
    by_cases h0 : |R| + 2 ≤ |y 0|
    · rw [(crrpBumpS R).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact h0)]; simp
    · rw [crrpχ_zero', mul_zero, zero_mul]
      intro hm
      have : |y 1| ≤ 5 / 2 := abs_le.2 ⟨by linarith [hm.1], hm.2⟩
      linarith
  obtain ⟨φ, hφ, hcau⟩ := exists_subseq_cauchy_of_support_bounded p hp1 hp' (|R| + 5) M
    (fun k i => crrpV R (u k) i) (fun k i => crrpV_contDiff R (hu k).1 i) hsupp hbd hdbd
  refine ⟨φ, hφ, fun ε hε => ?_⟩
  -- split `ε` among the `2n` coordinates
  obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr0
  set K : ℕ := Fintype.card (Fin n ⊕ Fin n)
  set ε' : ℝ≥0∞ := ENNReal.ofReal (r / (K + 1))
  have hε' : 0 < ε' := ENNReal.ofReal_pos.2 (by positivity)
  choose N hN using fun i => hcau i ε' hε'
  refine ⟨Finset.univ.sup N, fun a ha b hb => ?_⟩
  have hNi : ∀ i, N i ≤ Finset.univ.sup N := fun i => Finset.le_sup (Finset.mem_univ i)
  set S : Set (ℝ × ℝ) := Icc (-R) R ×ˢ univ
  have hSm : MeasurableSet S := measurableSet_Icc.prod MeasurableSet.univ
  -- pointwise comparison on the region
  have hae : ∀ᵐ x ∂(cylMeasure.restrict S), ‖(u (φ a) - u (φ b)) x‖ ≤
      ∑ i, ‖(crrpW R (u (φ a)) i - crrpW R (u (φ b)) i) x‖ := by
    have h1 : ∀ᵐ x ∂(cylMeasure.restrict S), x ∈ S := ae_restrict_mem hSm
    have h2 : ∀ᵐ x ∂(cylMeasure.restrict S), x ∈ univ ×ˢ Ico (0 : ℝ) 1 :=
      ae_restrict_of_ae (ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico))
    filter_upwards [h1, h2] with x hx1 hx2
    have hψ := crrpψ_one R hx1.1 hx2.2
    refine (crrp_norm_le_sum _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    simp only [Pi.sub_apply, crrpW, hψ, one_mul, PiLp.sub_apply]
    rfl
  have hcw : ∀ k i, Continuous (crrpW R (u k) i) := fun k i =>
    (crrpW_contDiff R (hu k).1 i).continuous
  calc eLpNorm (u (φ a) - u (φ b)) p (cylMeasure.restrict S)
      ≤ eLpNorm (fun x => ∑ i, ‖(crrpW R (u (φ a)) i - crrpW R (u (φ b)) i) x‖) p
          (cylMeasure.restrict S) := eLpNorm_mono_ae_real hae
    _ ≤ eLpNorm (fun x => ∑ i, ‖(crrpW R (u (φ a)) i - crrpW R (u (φ b)) i) x‖) p volume := by
        apply eLpNorm_mono_measure
        refine Measure.restrict_le_self.trans ?_
        exact Measure.restrict_le_self
    _ ≤ ∑ i, eLpNorm (fun x => ‖(crrpW R (u (φ a)) i - crrpW R (u (φ b)) i) x‖) p volume := by
        have hfun : (fun x => ∑ i, ‖(crrpW R (u (φ a)) i - crrpW R (u (φ b)) i) x‖) =
            ∑ i ∈ Finset.univ, fun x => ‖(crrpW R (u (φ a)) i - crrpW R (u (φ b)) i) x‖ := by
          funext x; rw [Finset.sum_apply]
        rw [hfun]
        exact eLpNorm_sum_le
          (fun i _ => (((hcw _ i).sub (hcw _ i)).norm).aestronglyMeasurable) hp1
    _ ≤ ∑ _i : Fin n ⊕ Fin n, ε' := by
        gcongr with i
        rw [eLpNorm_norm]
        have hcomp : eLpNorm (crrpV R (u (φ a)) i - crrpV R (u (φ b)) i) p volume =
            eLpNorm (crrpW R (u (φ a)) i - crrpW R (u (φ b)) i) p volume :=
          eLpNorm_comp_measurePreserving ((hcw _ i).sub (hcw _ i)).aestronglyMeasurable crrpT_mp
        rw [← hcomp]
        exact (hN i a ((hNi i).trans ha) b ((hNi i).trans hb)).le
    _ = K * ε' := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
    _ < ε := hrε

end

end CauchyRiemannIndex

-- ===== Scratch/CRRelPSol.lean =====
open MeasureTheory CauchyRiemannIndex
open scoped ENNReal NNReal

theorem solution (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) (R : ℝ)
    (u : ℕ → ℝ × ℝ → Vec n) (hu : ∀ k, IsTestSection (u k)) (hb : ∀ k, w1pNorm p (u k) ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ i ≥ N, ∀ j ≥ N,
      eLpNorm (u (φ i) - u (φ j)) p (cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)) < ε :=
  crrp_main n p hp hp' R u hu hb
