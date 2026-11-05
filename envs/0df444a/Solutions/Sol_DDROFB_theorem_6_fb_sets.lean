-- Prove2me | solution 1 for DDROFB.theorem_6_fb_sets
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T10:21:13.175133+00:00
-- url     : https://prove2.me/submissions/ffa27244-d2f8-435e-89fc-c89a03551161

import Mathlib
import Definitions.Def_DDROFB_HasIndepComponents
import Definitions.Def_DDROFB_SimultaneouslyImplies
import Definitions.Def_DDROFB_PFB
import Definitions.Def_DDROFB_UFB
import Definitions.Def_DDROFB_fbBound

set_option autoImplicit false

open MeasureTheory InnerProductSpace ProbabilityTheory

namespace DDROFBaux16d

lemma inner_eq_sum {d : ℕ} (v u : EuclideanSpace ℝ (Fin d)) : ⟪v, u⟫_ℝ = ∑ i, v i * u i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma cont_coord {d : ℕ} (i : Fin d) : Continuous (fun u : EuclideanSpace ℝ (Fin d) => u i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

/-- The weight `σ_i²` selected by the sign of `v_i`. -/
noncomputable def wt {d : ℕ} (σf σb : Fin d → ℝ) (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) : ℝ :=
  if 0 ≤ v i then σf i ^ 2 else σb i ^ 2

/-- The linear part of the support function. -/
noncomputable def lin {d : ℕ} (mb mf : Fin d → ℝ) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, (if 0 ≤ v i then mf i * v i else mb i * v i)

noncomputable def W {d : ℕ} (σf σb : Fin d → ℝ) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, wt σf σb v i * v i ^ 2

lemma wt_pos {d : ℕ} (σf σb : Fin d → ℝ) (hσf : ∀ i, 0 < σf i) (hσb : ∀ i, 0 < σb i)
    (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) : 0 < wt σf σb v i := by
  unfold wt; split_ifs
  · exact pow_pos (hσf i) 2
  · exact pow_pos (hσb i) 2

lemma W_nonneg {d : ℕ} (σf σb : Fin d → ℝ) (hσf : ∀ i, 0 < σf i) (hσb : ∀ i, 0 < σb i)
    (v : EuclideanSpace ℝ (Fin d)) : 0 ≤ W σf σb v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (wt_pos σf σb hσf hσb v i).le (sq_nonneg _)

lemma fbBound_eq {d : ℕ} (mb mf σf σb : Fin d → ℝ) (ε : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    DDROFB.fbBound mb mf σf σb ε v =
      lin mb mf v + Real.sqrt (2 * Real.log (1 / ε) * W σf σb v) := rfl

lemma sq_conv (a b x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
  have h : a * x ^ 2 + b * y ^ 2 - (a * x + b * y) ^ 2 = a * b * (x - y) ^ 2 := by
    rw [show b = 1 - a by linarith]; ring
  nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]

lemma convex_UFB {d : ℕ} (mb mf σf σb : Fin d → ℝ) (ε : ℝ) :
    Convex ℝ (DDROFB.UFB mb mf σf σb ε) := by
  rintro _ ⟨y1, y2, y3, hc, hs, rfl⟩ _ ⟨z1, z2, z3, hc', hs', rfl⟩ a b ha hb hab
  refine ⟨a • y1 + b • z1, a • y2 + b • z2, a • y3 + b • z3, fun i => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hc i
    obtain ⟨h1', h2', h3', h4'⟩ := hc' i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    refine ⟨by positivity, by positivity, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left h3 ha
      have := mul_le_mul_of_nonneg_left h3' hb
      have e : mb i = a * mb i + b * mb i := by rw [← add_mul, hab, one_mul]
      linarith
    · have := mul_le_mul_of_nonneg_left h4 ha
      have := mul_le_mul_of_nonneg_left h4' hb
      have e : mf i = a * mf i + b * mf i := by rw [← add_mul, hab, one_mul]
      linarith
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    calc ∑ i, ((a * y2 i + b * z2 i) ^ 2 / (2 * σf i ^ 2) +
          (a * y3 i + b * z3 i) ^ 2 / (2 * σb i ^ 2))
        ≤ ∑ i, (a * (y2 i ^ 2 / (2 * σf i ^ 2) + y3 i ^ 2 / (2 * σb i ^ 2)) +
            b * (z2 i ^ 2 / (2 * σf i ^ 2) + z3 i ^ 2 / (2 * σb i ^ 2))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have e1 := div_le_div_of_nonneg_right (sq_conv a b (y2 i) (z2 i) ha hb hab)
            (by positivity : (0:ℝ) ≤ 2 * σf i ^ 2)
          have e2 := div_le_div_of_nonneg_right (sq_conv a b (y3 i) (z3 i) ha hb hab)
            (by positivity : (0:ℝ) ≤ 2 * σb i ^ 2)
          have r1 : (a * y2 i ^ 2 + b * z2 i ^ 2) / (2 * σf i ^ 2) =
              a * (y2 i ^ 2 / (2 * σf i ^ 2)) + b * (z2 i ^ 2 / (2 * σf i ^ 2)) := by ring
          have r2 : (a * y3 i ^ 2 + b * z3 i ^ 2) / (2 * σb i ^ 2) =
              a * (y3 i ^ 2 / (2 * σb i ^ 2)) + b * (z3 i ^ 2 / (2 * σb i ^ 2)) := by ring
          linarith
      _ = a * ∑ i, (y2 i ^ 2 / (2 * σf i ^ 2) + y3 i ^ 2 / (2 * σb i ^ 2)) +
            b * ∑ i, (z2 i ^ 2 / (2 * σf i ^ 2) + z3 i ^ 2 / (2 * σb i ^ 2)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      _ ≤ a * Real.log (1 / ε) + b * Real.log (1 / ε) := by gcongr
      _ = Real.log (1 / ε) := by rw [← add_mul, hab, one_mul]
  · obtain rfl : b = 1 - a := by linarith
    module

/-- Support function of `U^FB_ε`: upper bound. -/
lemma UFB_le {d : ℕ} (mb mf σf σb : Fin d → ℝ) (hσf : ∀ i, 0 < σf i) (hσb : ∀ i, 0 < σb i)
    (ε : ℝ) (v u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ DDROFB.UFB mb mf σf σb ε) :
    ⟪v, u⟫_ℝ ≤ DDROFB.fbBound mb mf σf σb ε v := by
  obtain ⟨y1, y2, y3, hc, hs, rfl⟩ := hu
  rw [fbBound_eq, inner_eq_sum]
  simp only [PiLp.add_apply, PiLp.sub_apply]
  set L := Real.log (1 / ε)
  let p : Fin d ⊕ Fin d → ℝ := Sum.elim (fun i => if 0 ≤ v i then σf i * v i else 0)
    (fun i => if 0 ≤ v i then 0 else -(σb i * v i))
  let q : Fin d ⊕ Fin d → ℝ := Sum.elim (fun i => y2 i / σf i) (fun i => y3 i / σb i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d ⊕ Fin d)) p q
  simp only [Fintype.sum_sum_type, p, q, Sum.elim_inl, Sum.elim_inr] at hcs
  have hp2 : (∑ i, (if 0 ≤ v i then σf i * v i else 0) ^ 2) +
      (∑ i, (if 0 ≤ v i then 0 else -(σb i * v i)) ^ 2) = W σf σb v := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold wt; split_ifs <;> ring
  have hq2 : (∑ i, (y2 i / σf i) ^ 2) + (∑ i, (y3 i / σb i) ^ 2) ≤ 2 * L := by
    rw [← Finset.sum_add_distrib]
    have : ∑ i, ((y2 i / σf i) ^ 2 + (y3 i / σb i) ^ 2) =
        2 * ∑ i, (y2 i ^ 2 / (2 * σf i ^ 2) + y3 i ^ 2 / (2 * σb i ^ 2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := (hσf i).ne'; have := (hσb i).ne'
      field_simp
    rw [this]; linarith
  rw [hp2] at hcs
  set S := (∑ i, (if 0 ≤ v i then σf i * v i else 0) * (y2 i / σf i)) +
      ∑ i, (if 0 ≤ v i then 0 else -(σb i * v i)) * (y3 i / σb i) with hS
  have hW0 := W_nonneg σf σb hσf hσb v
  have hSle : S ≤ Real.sqrt (2 * L * W σf σb v) := by
    have h1 := Real.abs_le_sqrt hcs
    have h2 : Real.sqrt (W σf σb v * ((∑ i, (y2 i / σf i) ^ 2) + ∑ i, (y3 i / σb i) ^ 2)) ≤
        Real.sqrt (2 * L * W σf σb v) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    exact (le_abs_self S).trans (h1.trans h2)
  have hterm : ∀ i, v i * (y1 i + y2 i - y3 i) ≤
      (if 0 ≤ v i then mf i * v i else mb i * v i) +
      ((if 0 ≤ v i then σf i * v i else 0) * (y2 i / σf i) +
        (if 0 ≤ v i then 0 else -(σb i * v i)) * (y3 i / σb i)) := by
    intro i
    obtain ⟨h2, h3, h1l, h1u⟩ := hc i
    have hf := (hσf i).ne'; have hb' := (hσb i).ne'
    split_ifs with hv
    · have e : σf i * v i * (y2 i / σf i) = v i * y2 i := by field_simp
      rw [e]; nlinarith [mul_nonneg hv h3, mul_le_mul_of_nonneg_left h1u hv]
    · push Not at hv
      have e : -(σb i * v i) * (y3 i / σb i) = -(v i * y3 i) := by field_simp
      rw [e]
      nlinarith [mul_le_mul_of_nonpos_left h1l hv.le, mul_nonpos_iff.mpr (Or.inr ⟨hv.le, h2⟩)]
  calc ∑ i, v i * (y1 i + y2 i - y3 i)
      ≤ ∑ i, ((if 0 ≤ v i then mf i * v i else mb i * v i) +
        ((if 0 ≤ v i then σf i * v i else 0) * (y2 i / σf i) +
          (if 0 ≤ v i then 0 else -(σb i * v i)) * (y3 i / σb i))) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = lin mb mf v + S := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]; rfl
    _ ≤ _ := by linarith

/-- Support function of `U^FB_ε`: attained. -/
lemma UFB_attained {d : ℕ} (mb mf σf σb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hσf : ∀ i, 0 < σf i) (hσb : ∀ i, 0 < σb i)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : EuclideanSpace ℝ (Fin d)) :
    DDROFB.fbBound mb mf σf σb ε v ∈ (fun u => ⟪v, u⟫_ℝ) '' DDROFB.UFB mb mf σf σb ε := by
  set L := Real.log (1 / ε) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hε0]; linarith)
  set w := W σf σb v with hw
  have hw0 : 0 ≤ w := W_nonneg σf σb hσf hσb v
  set c := Real.sqrt (2 * L * w) / w with hc
  have hc0 : 0 ≤ c := div_nonneg (Real.sqrt_nonneg _) hw0
  have hcw : c * w = Real.sqrt (2 * L * w) := by
    rcases hw0.lt_or_eq with h | h
    · rw [hc, div_mul_cancel₀ _ h.ne']
    · rw [← h]; simp
  have hc2 : c ^ 2 * w / 2 ≤ L := by
    rcases hw0.lt_or_eq with h | h
    · have : c ^ 2 * w = (c * w) ^ 2 / w := by field_simp
      rw [this, hcw, Real.sq_sqrt (by positivity)]
      field_simp
      rfl
    · rw [← h]; simp [hL0]
  refine ⟨WithLp.toLp 2 (fun i => if 0 ≤ v i then mf i else mb i) +
      WithLp.toLp 2 (fun i => if 0 ≤ v i then c * σf i ^ 2 * v i else 0) -
      WithLp.toLp 2 (fun i => if 0 ≤ v i then 0 else -(c * σb i ^ 2 * v i)),
    ⟨WithLp.toLp 2 (fun i => if 0 ≤ v i then mf i else mb i),
      WithLp.toLp 2 (fun i => if 0 ≤ v i then c * σf i ^ 2 * v i else 0),
      WithLp.toLp 2 (fun i => if 0 ≤ v i then 0 else -(c * σb i ^ 2 * v i)), fun i => ?_, ?_, rfl⟩, ?_⟩
  · simp only [PiLp.toLp_apply]
    split_ifs with hv
    · exact ⟨by positivity, le_refl _, hm i, le_refl _⟩
    · push Not at hv
      refine ⟨le_refl _, ?_, le_refl _, hm i⟩
      have : 0 ≤ c * σb i ^ 2 * (-v i) :=
        mul_nonneg (mul_nonneg hc0 (sq_nonneg _)) (by linarith)
      linarith
  · simp only [PiLp.toLp_apply]
    calc ∑ i, ((if 0 ≤ v i then c * σf i ^ 2 * v i else 0) ^ 2 / (2 * σf i ^ 2) +
          (if 0 ≤ v i then 0 else -(c * σb i ^ 2 * v i)) ^ 2 / (2 * σb i ^ 2))
        = ∑ i, c ^ 2 / 2 * (wt σf σb v i * v i ^ 2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have := (hσf i).ne'; have := (hσb i).ne'
          unfold wt
          split_ifs
          · field_simp; ring
          · field_simp; ring
      _ = c ^ 2 * w / 2 := by rw [← Finset.mul_sum, hw, W]; ring
      _ ≤ L := hc2
  · simp only
    rw [fbBound_eq, inner_eq_sum, ← hL, ← hw, ← hcw]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.toLp_apply]
    rw [lin, hw, W, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold wt
    split_ifs <;> ring

section prob

open Classical in
lemma fwd_bound (Q : Measure ℝ) [IsProbabilityMeasure Q] (σ : ℝ) (hσ : 0 < σ)
    (h : DDROFB.fwdDev Q ≤ ENNReal.ofReal σ) (x : ℝ) (hx : 0 < x) :
    ∫ z, Real.exp (x * z) ∂Q ≤ Real.exp (x * ∫ z, z ∂Q + x ^ 2 * σ ^ 2 / 2) := by
  unfold DDROFB.fwdDev at h
  split_ifs at h with h1
  · have h2 := (le_iSup₂ (f := fun (x : ℝ) (_ : 0 < x) =>
        if Integrable (fun z : ℝ => Real.exp (x * z)) Q then
          ENNReal.ofReal (Real.sqrt (-2 * (∫ z, z ∂Q) / x +
            2 / x ^ 2 * Real.log (∫ z, Real.exp (x * z) ∂Q)))
        else ⊤) x hx).trans h
    split_ifs at h2 with h3
    · have h4 := (ENNReal.ofReal_le_ofReal_iff hσ.le).mp h2
      have h5 := (Real.sqrt_le_left hσ.le).mp h4
      have hMpos : 0 < ∫ z, Real.exp (x * z) ∂Q := integral_exp_pos h3
      set M := ∫ z, Real.exp (x * z) ∂Q
      set m := ∫ z, z ∂Q
      have e : x ^ 2 / 2 * (-2 * m / x + 2 / x ^ 2 * Real.log M) = -(x * m) + Real.log M := by
        field_simp
      have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ x ^ 2 / 2)
      rw [e] at h6
      rw [← Real.exp_log hMpos]
      exact Real.exp_le_exp.mpr (by linarith)
    · exact absurd h2 (by simp)
  · exact absurd h (by simp)

open Classical in
lemma bwd_bound (Q : Measure ℝ) [IsProbabilityMeasure Q] (σ : ℝ) (hσ : 0 < σ)
    (h : DDROFB.bwdDev Q ≤ ENNReal.ofReal σ) (x : ℝ) (hx : 0 < x) :
    ∫ z, Real.exp (-(x * z)) ∂Q ≤ Real.exp (-(x * ∫ z, z ∂Q) + x ^ 2 * σ ^ 2 / 2) := by
  unfold DDROFB.bwdDev at h
  split_ifs at h with h1
  · have h2 := (le_iSup₂ (f := fun (x : ℝ) (_ : 0 < x) =>
        if Integrable (fun z : ℝ => Real.exp (-(x * z))) Q then
          ENNReal.ofReal (Real.sqrt (2 * (∫ z, z ∂Q) / x +
            2 / x ^ 2 * Real.log (∫ z, Real.exp (-(x * z)) ∂Q)))
        else ⊤) x hx).trans h
    split_ifs at h2 with h3
    · have h4 := (ENNReal.ofReal_le_ofReal_iff hσ.le).mp h2
      have h5 := (Real.sqrt_le_left hσ.le).mp h4
      have hMpos : 0 < ∫ z, Real.exp (-(x * z)) ∂Q := integral_exp_pos h3
      set M := ∫ z, Real.exp (-(x * z)) ∂Q
      set m := ∫ z, z ∂Q
      have e : x ^ 2 / 2 * (2 * m / x + 2 / x ^ 2 * Real.log M) = x * m + Real.log M := by
        field_simp
      have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ x ^ 2 / 2)
      rw [e] at h6
      rw [← Real.exp_log hMpos]
      exact Real.exp_le_exp.mpr (by linarith)
    · exact absurd h2 (by simp)
  · exact absurd h (by simp)

lemma coord_mgf {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (i : Fin d) (σf σb : ℝ) (hσf : 0 < σf) (hσb : 0 < σb)
    (hf : DDROFB.fwdDev (DDROFB.marginal P i) ≤ ENNReal.ofReal σf)
    (hbw : DDROFB.bwdDev (DDROFB.marginal P i) ≤ ENNReal.ofReal σb) (c : ℝ) :
    ∫ u, Real.exp (c * u i) ∂P ≤
      Real.exp (c * ∫ u, u i ∂P + c ^ 2 * (if 0 ≤ c then σf ^ 2 else σb ^ 2) / 2) := by
  have hmeas : Measurable (fun u : EuclideanSpace ℝ (Fin d) => u i) := (cont_coord i).measurable
  haveI : IsProbabilityMeasure (DDROFB.marginal P i) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hmap : ∀ f : ℝ → ℝ, Continuous f →
      ∫ z, f z ∂(DDROFB.marginal P i) = ∫ u, f (u i) ∂P := fun f hf =>
    integral_map hmeas.aemeasurable hf.aestronglyMeasurable
  have hmean := hmap (fun z => z) continuous_id
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have h := bwd_bound _ σb hσb hbw (-c) (by linarith)
    rw [hmap (fun z => Real.exp (-(-c * z))) (by fun_prop), hmean] at h
    have e : (fun u : EuclideanSpace ℝ (Fin d) => Real.exp (-(-c * u i))) =
        fun u => Real.exp (c * u i) := by
      funext u; ring_nf
    rw [e] at h
    rw [if_neg (not_le.mpr hc)]
    refine h.trans (Real.exp_le_exp.mpr (le_of_eq ?_))
    ring
  · subst hc; simp
  · have h := fwd_bound _ σf hσf hf c hc
    rw [hmap (fun z => Real.exp (c * z)) (by fun_prop), hmean] at h
    rw [if_pos hc.le]
    exact h

lemma tail_fb {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hind : DDROFB.HasIndepComponents P) (R : ℝ) (hb : ∀ᵐ u ∂P, ‖u‖ ≤ R)
    (mb mf σf σb : Fin d → ℝ) (hσf : ∀ i, 0 < σf i) (hσb : ∀ i, 0 < σb i)
    (hP : P ∈ DDROFB.PFB mb mf σf σb) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : EuclideanSpace ℝ (Fin d)) :
    P.real {u | DDROFB.fbBound mb mf σf σb ε v < ⟪v, u⟫_ℝ} ≤ ε := by
  obtain ⟨_, _, hcoord⟩ := hP
  have hL : 0 < Real.log (1 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε0]; linarith)
  rcases (W_nonneg σf σb hσf hσb v).lt_or_eq with hw | hw
  · set L := Real.log (1 / ε) with hLdef
    set w := W σf σb v with hwdef
    set lam := Real.sqrt (2 * L * w) / w with hlam
    have hsq : Real.sqrt (2 * L * w) ^ 2 = 2 * L * w := Real.sq_sqrt (by positivity)
    have hlampos : 0 < lam := div_pos (Real.sqrt_pos.mpr (by positivity)) hw
    have hlam0 : 0 ≤ lam := hlampos.le
    have hint : Integrable (fun u => Real.exp (lam * ⟪v, u⟫_ℝ)) P := by
      refine Integrable.of_bound
        (by fun_prop : Continuous fun u : EuclideanSpace ℝ (Fin d) =>
          Real.exp (lam * ⟪v, u⟫_ℝ)).aestronglyMeasurable (Real.exp (lam * (‖v‖ * R))) ?_
      filter_upwards [hb] with u hu
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((real_inner_le_norm v u).trans
        (mul_le_mul_of_nonneg_left hu (norm_nonneg _))) hlam0)
    have hch := measure_ge_le_exp_mul_mgf (X := fun u => ⟪v, u⟫_ℝ) (μ := P)
      (DDROFB.fbBound mb mf σf σb ε v) hlam0 hint
    have hX : (fun u : EuclideanSpace ℝ (Fin d) => ⟪v, u⟫_ℝ) =
        ∑ i, (fun u : EuclideanSpace ℝ (Fin d) => v i * u i) := by
      funext u; rw [inner_eq_sum, Finset.sum_apply]
    have hind' : iIndepFun (fun i (u : EuclideanSpace ℝ (Fin d)) => v i * u i) P :=
      hind.comp (fun i x => v i * x) (fun i => measurable_const.mul measurable_id)
    have hmgf : mgf (fun u => ⟪v, u⟫_ℝ) P lam =
        ∏ i, mgf (fun u : EuclideanSpace ℝ (Fin d) => v i * u i) P lam := by
      rw [hX]; exact hind'.mgf_sum (fun i => measurable_const.mul (cont_coord i).measurable) _
    have hfac : ∀ i, mgf (fun u : EuclideanSpace ℝ (Fin d) => v i * u i) P lam ≤
        Real.exp (lam * (v i * ∫ u, u i ∂P) + lam ^ 2 * (wt σf σb v i * v i ^ 2) / 2) := by
      intro i
      obtain ⟨_, _, hf, hbw⟩ := hcoord i
      have h := coord_mgf P i (σf i) (σb i) (hσf i) (hσb i) hf hbw (lam * v i)
      unfold mgf
      have e : (fun u : EuclideanSpace ℝ (Fin d) => Real.exp (lam * (v i * u i))) =
          fun u => Real.exp (lam * v i * u i) := by
        funext u; ring_nf
      rw [e]
      refine h.trans (Real.exp_le_exp.mpr (le_of_eq ?_))
      have hsign : (0 ≤ lam * v i) ↔ (0 ≤ v i) := by
        constructor
        · intro h'; by_contra h''; push Not at h''
          have := mul_neg_of_pos_of_neg hlampos h''; linarith
        · intro h'; exact mul_nonneg hlam0 h'
      unfold wt
      by_cases hv : 0 ≤ v i
      · rw [if_pos (hsign.mpr hv), if_pos hv]; ring
      · rw [if_neg (fun h' => hv (hsign.mp h')), if_neg hv]; ring
    have hprod : ∏ i, mgf (fun u : EuclideanSpace ℝ (Fin d) => v i * u i) P lam ≤
        ∏ i, Real.exp (lam * (v i * ∫ u, u i ∂P) + lam ^ 2 * (wt σf σb v i * v i ^ 2) / 2) :=
      Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => hfac i)
    rw [← Real.exp_sum] at hprod
    have hmean : ∑ i, v i * ∫ u, u i ∂P ≤ lin mb mf v := by
      unfold lin
      refine Finset.sum_le_sum fun i _ => ?_
      obtain ⟨h1, h2, _, _⟩ := hcoord i
      split_ifs with hv
      · nlinarith [mul_le_mul_of_nonneg_left h2 hv]
      · push Not at hv
        nlinarith [mul_le_mul_of_nonpos_left h1 hv.le]
    have hsumexp : ∑ i, (lam * (v i * ∫ u, u i ∂P) + lam ^ 2 * (wt σf σb v i * v i ^ 2) / 2) =
        lam * ∑ i, v i * ∫ u, u i ∂P + lam ^ 2 * w / 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum]
      rfl
    have h1 : lam * Real.sqrt (2 * L * w) = 2 * L := by
      rw [hlam, div_mul_eq_mul_div, ← sq, hsq]; field_simp
    have h2 : lam ^ 2 * w / 2 = L := by
      rw [hlam, div_pow, hsq]; field_simp
    have key : -lam * DDROFB.fbBound mb mf σf σb ε v +
        (lam * ∑ i, v i * ∫ u, u i ∂P + lam ^ 2 * w / 2) ≤ -L := by
      rw [fbBound_eq, ← hLdef, ← hwdef]
      have : -lam * (lin mb mf v + Real.sqrt (2 * L * w)) +
          (lam * ∑ i, v i * ∫ u, u i ∂P + lam ^ 2 * w / 2) =
          -(lam * lin mb mf v) - lam * Real.sqrt (2 * L * w) +
            lam * ∑ i, v i * ∫ u, u i ∂P + lam ^ 2 * w / 2 := by ring
      rw [this, h1, h2]
      linarith [mul_le_mul_of_nonneg_left hmean hlam0]
    have hfin : P.real {u | DDROFB.fbBound mb mf σf σb ε v < ⟪v, u⟫_ℝ} ≤
        P.real {u | DDROFB.fbBound mb mf σf σb ε v ≤ ⟪v, u⟫_ℝ} :=
      measureReal_mono (fun u hu => by simp only [Set.mem_ofPred_eq] at hu ⊢; exact hu.le)
        (measure_ne_top _ _)
    have hexpL : Real.exp (-L) = ε := by
      rw [Real.exp_neg, hLdef, Real.exp_log (one_div_pos.mpr hε0), one_div, inv_inv]
    calc P.real {u | DDROFB.fbBound mb mf σf σb ε v < ⟪v, u⟫_ℝ}
        ≤ P.real {u | DDROFB.fbBound mb mf σf σb ε v ≤ ⟪v, u⟫_ℝ} := hfin
      _ ≤ Real.exp (-lam * DDROFB.fbBound mb mf σf σb ε v) *
            mgf (fun u => ⟪v, u⟫_ℝ) P lam := hch
      _ ≤ Real.exp (-lam * DDROFB.fbBound mb mf σf σb ε v) *
            Real.exp (∑ i, (lam * (v i * ∫ u, u i ∂P) + lam ^ 2 * (wt σf σb v i * v i ^ 2) / 2)) := by
          rw [hmgf]; exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = Real.exp (-lam * DDROFB.fbBound mb mf σf σb ε v +
            (lam * ∑ i, v i * ∫ u, u i ∂P + lam ^ 2 * w / 2)) := by
          rw [← Real.exp_add, hsumexp]
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr key
      _ = ε := hexpL
  · have hv0 : ∀ i, v i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
        mul_nonneg (wt_pos σf σb hσf hσb v j).le (sq_nonneg (v j)))).mp hw.symm i
        (Finset.mem_univ _)
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (wt_pos σf σb hσf hσb v i).ne'
      · simpa using h
    have hempty : {u : EuclideanSpace ℝ (Fin d) | DDROFB.fbBound mb mf σf σb ε v < ⟪v, u⟫_ℝ} = ∅ := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      simp [DDROFB.fbBound, inner_eq_sum, hv0]
    rw [hempty]
    simp [hε0.le]

end prob

lemma guarantee_fb {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P]
    (hind : DDROFB.HasIndepComponents P) (R : ℝ) (hb : ∀ᵐ u ∂P, ‖u‖ ≤ R)
    (mb mf σf σb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i) (hσf : ∀ i, 0 < σf i)
    (hσb : ∀ i, 0 < σb i) (hP : P ∈ DDROFB.PFB mb mf σf σb) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) : DDROFB.ImpliesGuarantee (DDROFB.UFB mb mf σf σb ε) P ε := by
  intro g hg hle
  have hgc : Continuous g := continuousOn_univ.mp (hg.continuousOn isOpen_univ)
  have hAconv : Convex ℝ {x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) | 0 < g x} :=
    hg.convex_gt 0
  have hAopen : IsOpen {x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) | 0 < g x} := by
    simpa only [Set.mem_univ, true_and, Set.sep_univ] using isOpen_lt continuous_const hgc
  have hdisj : Disjoint {x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) | 0 < g x}
      (DDROFB.UFB mb mf σf σb ε) := by
    rw [Set.disjoint_left]
    rintro a ⟨_, ha⟩ hU
    exact absurd (hle a hU) (not_le.mpr ha)
  obtain ⟨φ, s, hA, hB⟩ := geometric_hahn_banach_open hAconv hAopen
    (convex_UFB mb mf σf σb ε) hdisj
  set z := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm φ with hz
  have hφ : ∀ x, φ x = ⟪z, x⟫_ℝ := fun x => (InnerProductSpace.toDual_symm_apply).symm
  set v := -z with hv
  set δ := DDROFB.fbBound mb mf σf σb ε v with hδ
  have hδs : δ ≤ -s := by
    obtain ⟨b, hbU, hbδ⟩ := UFB_attained mb mf σf σb hm hσf hσb ε hε0 hε1 v
    have := hB b hbU
    rw [hφ] at this
    simp only at hbδ
    rw [← hδ, hv, inner_neg_left] at hbδ
    rw [← hbδ]
    linarith
  have hsub : {u | ⟪v, u⟫_ℝ ≤ δ} ⊆ {u | g u ≤ 0} := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    by_contra hpos
    push Not at hpos
    have h1 := hA u ⟨Set.mem_univ _, hpos⟩
    rw [hφ] at h1
    rw [hv, inner_neg_left] at hu
    linarith
  have hmeas : MeasurableSet {u : EuclideanSpace ℝ (Fin d) | ⟪v, u⟫_ℝ ≤ δ} :=
    measurableSet_le (continuous_const.inner continuous_id).measurable measurable_const
  have hcompl := measureReal_add_measureReal_compl (μ := P) hmeas
  rw [probReal_univ] at hcompl
  have hc : {u : EuclideanSpace ℝ (Fin d) | ⟪v, u⟫_ℝ ≤ δ}ᶜ = {u | δ < ⟪v, u⟫_ℝ} := by
    ext u; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hc] at hcompl
  have ht : P.real {u | δ < ⟪v, u⟫_ℝ} ≤ ε :=
    tail_fb P hind R hb mb mf σf σb hσf hσb hP ε hε0 hε1 v
  have hmo := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
  show 1 - ε ≤ P.real {u | g u ≤ 0}
  linarith

end DDROFBaux16d

open MeasureTheory InnerProductSpace DDROFB in
theorem solution {d N : ℕ} (Pstar : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure Pstar] (hind : HasIndepComponents Pstar)
    (hbdd : ∃ R : ℝ, ∀ᵐ u ∂Pstar, ‖u‖ ≤ R)
    (α : ℝ) (mb mf σf σb : (Fin N → EuclideanSpace ℝ (Fin d)) → Fin d → ℝ)
    (hm : ∀ S i, mb S i ≤ mf S i) (hσf : ∀ S i, 0 < σf S i) (hσb : ∀ S i, 0 < σb S i)
    (hcov : 1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar)
        {S | Pstar ∈ PFB (mb S) (mf S) (σf S) (σb S)}).toReal) :
    1 - α ≤ (Measure.pi (fun _ : Fin N => Pstar)
        {S | SimultaneouslyImplies (fun ε => UFB (mb S) (mf S) (σf S) (σb S) ε) Pstar}).toReal ∧
    ∀ S : Fin N → EuclideanSpace ℝ (Fin d), ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ v : EuclideanSpace ℝ (Fin d),
        IsLUB ((fun u => ⟪v, u⟫_ℝ) '' UFB (mb S) (mf S) (σf S) (σb S) ε)
          (fbBound (mb S) (mf S) (σf S) (σb S) ε v) := by
  obtain ⟨R, hR⟩ := hbdd
  constructor
  · have hsub : {S : Fin N → EuclideanSpace ℝ (Fin d) |
        Pstar ∈ PFB (mb S) (mf S) (σf S) (σb S)} ⊆
        {S | SimultaneouslyImplies (fun ε => UFB (mb S) (mf S) (σf S) (σb S) ε) Pstar} := by
      intro S hS ε hε0 hε1
      exact DDROFBaux16d.guarantee_fb Pstar hind R hR (mb S) (mf S) (σf S) (σb S) (hm S)
        (hσf S) (hσb S) hS ε hε0 hε1
    exact hcov.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
  · intro S ε hε0 hε1 v
    refine ⟨?_, fun b hb => hb (DDROFBaux16d.UFB_attained (mb S) (mf S) (σf S) (σb S) (hm S)
      (hσf S) (hσb S) ε hε0 hε1 v)⟩
    rintro _ ⟨u, hu, rfl⟩
    exact DDROFBaux16d.UFB_le (mb S) (mf S) (σf S) (σb S) (hσf S) (hσb S) ε v u hu
