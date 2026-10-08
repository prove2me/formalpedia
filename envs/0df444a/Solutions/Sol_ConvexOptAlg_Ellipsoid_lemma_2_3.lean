-- Prove2me | solution 1 for ConvexOptAlg.Ellipsoid.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:09:43.85292+00:00
-- url     : https://prove2.me/submissions/513cf044-941d-43a4-a074-e71c8ff3185e

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs



namespace ConvexOptAlg.Ellipsoid

open Matrix MeasureTheory

lemma el_vmv_mulVec {n : ℕ} (u v x : Fin n → ℝ) : vecMulVec u v *ᵥ x = (v ⬝ᵥ x) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma el_symm {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.IsHermitian) : Hᵀ = H := by
  have := hH.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma el_dot_symm {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : Pᵀ = P) (a b : Fin n → ℝ) :
    b ⬝ᵥ (P *ᵥ a) = a ⬝ᵥ (P *ᵥ b) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hP, dotProduct_comm]

lemma el_expand {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (a b : Fin n → ℝ) (τ : ℝ) :
    (a + τ • b) ⬝ᵥ (P *ᵥ (a + τ • b)) =
      a ⬝ᵥ (P *ᵥ a) + 2 * τ * (a ⬝ᵥ (P *ᵥ b)) + τ ^ 2 * (b ⬝ᵥ (P *ᵥ b)) := by
  have h := el_dot_symm hP a b
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, h]
  ring

lemma el_cs {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (a b : Fin n → ℝ) :
    (a ⬝ᵥ (P *ᵥ b)) ^ 2 ≤ (a ⬝ᵥ (P *ᵥ a)) * (b ⬝ᵥ (P *ᵥ b)) := by
  have hs := el_symm hP.1
  have key : ∀ x : ℝ, 0 ≤ (b ⬝ᵥ (P *ᵥ b)) * (x * x) + 2 * (a ⬝ᵥ (P *ᵥ b)) * x
      + a ⬝ᵥ (P *ᵥ a) := by
    intro x
    have := hP.dotProduct_mulVec_nonneg (a + x • b)
    simp only [star_trivial] at this
    rw [el_expand P hs] at this
    nlinarith [this]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]

lemma el_quad_pos {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) {v : Fin n → ℝ}
    (hv : v ≠ 0) : 0 < v ⬝ᵥ (H *ᵥ v) := by
  simpa using hH.dotProduct_mulVec_pos hv

lemma el_inv_mul {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) : H⁻¹ * H = 1 :=
  nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hH.det_pos.ne')

lemma el_mul_inv {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) : H * H⁻¹ = 1 :=
  mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hH.det_pos.ne')

lemma el_HwwH_mulVec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (w x : Fin n → ℝ) :
    (H * vecMulVec w w * H) *ᵥ x = (w ⬝ᵥ (H *ᵥ x)) • (H *ᵥ w) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, el_vmv_mulVec, mulVec_smul]


noncomputable def elNewH {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (H - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H *ᵥ w))⁻¹ • (H * vecMulVec w w * H))

noncomputable def elNewc {n : ℕ} (c0 : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → ℝ) : Fin n → ℝ :=
  c0 - ((1 : ℝ) / ((n : ℝ) + 1)) • (Real.sqrt (w ⬝ᵥ (H *ᵥ w)))⁻¹ • (H *ᵥ w)

lemma elNewH_mulVec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (w z : Fin n → ℝ) :
    elNewH H w *ᵥ z = ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) • (H *ᵥ z -
      (((2 : ℝ) / ((n : ℝ) + 1)) * (w ⬝ᵥ (H *ᵥ w))⁻¹ * (w ⬝ᵥ (H *ᵥ z))) • (H *ᵥ w)) := by
  unfold elNewH
  rw [smul_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, el_HwwH_mulVec, smul_smul, smul_smul]

lemma elNewH_symm {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef) (w : Fin n → ℝ) :
    (elNewH H w)ᵀ = elNewH H w := by
  have hs := el_symm hH.1
  unfold elNewH
  simp only [transpose_smul, transpose_sub, transpose_mul, hs, transpose_vecMulVec]
  simp only [Matrix.mul_assoc]

lemma elNewH_posDef {n : ℕ} (hn : 2 ≤ n) {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    {w : Fin n → ℝ} (hw : w ≠ 0) : (elNewH H w).PosDef := by
  have hs := el_symm hH.1
  have hβ := el_quad_pos hH hw
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact elNewH_symm hH w
  intro v hv
  simp only [star_trivial]
  rw [elNewH_mulVec, dotProduct_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hv' := el_quad_pos hH hv
  have hcs := el_cs H hH.posSemidef w v
  rw [el_dot_symm hs w v]
  have hk : 0 < (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := by
    apply div_pos <;> nlinarith
  apply mul_pos hk
  set β := w ⬝ᵥ (H *ᵥ w)
  set q := v ⬝ᵥ (H *ᵥ v)
  set s := w ⬝ᵥ (H *ᵥ v)
  have : 2 / ((n : ℝ) + 1) * β⁻¹ * s * s ≤ 2 / ((n : ℝ) + 1) * q := by
    rw [mul_assoc, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [inv_mul_le_iff₀ hβ]; nlinarith
  have : 2 / ((n : ℝ) + 1) * q < q := by
    have : 2 / ((n : ℝ) + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  linarith


lemma elNewH_inv {n : ℕ} (hn : 2 ≤ n) {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    {w : Fin n → ℝ} (hw : w ≠ 0) :
    (elNewH H w)⁻¹ = (((n : ℝ) ^ 2 - 1) / (n : ℝ) ^ 2) •
      (H⁻¹ + ((2 : ℝ) / (((n : ℝ) - 1) * (w ⬝ᵥ (H *ᵥ w)))) • vecMulVec w w) := by
  have hβ := el_quad_pos hH hw
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply inv_eq_right_inv
  apply mulVec_injective
  funext v
  rw [← mulVec_mulVec, one_mulVec, smul_mulVec, add_mulVec, smul_mulVec, el_vmv_mulVec,
    elNewH_mulVec]
  have h1 : H *ᵥ (H⁻¹ *ᵥ v) = v := by rw [mulVec_mulVec, el_mul_inv hH, one_mulVec]
  simp only [mulVec_smul, mulVec_add, h1, dotProduct_smul, dotProduct_add, smul_eq_mul,
    dotProduct_comm w v]
  set β := w ⬝ᵥ (H *ᵥ w)
  set s := v ⬝ᵥ w
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  have h3 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h4 : (n : ℝ) + 1 ≠ 0 := by linarith
  have h5 : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h6 : (n : ℝ) ≠ 0 := by linarith
  field_simp
  ring

lemma elNewH_contain {n : ℕ} (hn : 2 ≤ n) (c0 : Fin n → ℝ) {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0) :
    LinearOptimization.ellipsoid c0 H ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
      LinearOptimization.ellipsoid (elNewc c0 H w) (elNewH H w) := by
  rintro x ⟨hx, hxs⟩
  simp only [LinearOptimization.ellipsoid, Set.mem_setOf_eq] at hx hxs ⊢
  have hβ := el_quad_pos hH hw
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := el_symm hH.1
  have hsi : (H⁻¹)ᵀ = H⁻¹ := by rw [transpose_nonsing_inv, hs]
  rw [elNewH_inv hn hH hw]
  set β := w ⬝ᵥ (H *ᵥ w) with hβdef
  set y := x - c0
  have hxc : x - elNewc c0 H w = y + ((1 : ℝ) / ((n : ℝ) + 1) * (Real.sqrt β)⁻¹) • (H *ᵥ w) := by
    unfold elNewc; rw [smul_smul]; simp only [y]; abel
  rw [hxc]
  set τ := (1 : ℝ) / ((n : ℝ) + 1) * (Real.sqrt β)⁻¹
  rw [smul_mulVec, add_mulVec, smul_mulVec, el_vmv_mulVec, dotProduct_smul, dotProduct_add,
    dotProduct_smul, el_expand _ hsi]
  have e1 : y ⬝ᵥ (H⁻¹ *ᵥ (H *ᵥ w)) = w ⬝ᵥ y := by
    rw [mulVec_mulVec, el_inv_mul hH, one_mulVec, dotProduct_comm]
  have e2 : (H *ᵥ w) ⬝ᵥ (H⁻¹ *ᵥ (H *ᵥ w)) = β := by
    rw [mulVec_mulVec, el_inv_mul hH, one_mulVec, dotProduct_comm]
  have e3 : w ⬝ᵥ (y + τ • (H *ᵥ w)) = w ⬝ᵥ y + τ * β := by
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm (y + τ • (H *ᵥ w)) w, e1, e2, e3]
  -- Cauchy-Schwarz
  have hcs : (w ⬝ᵥ y) ^ 2 ≤ (y ⬝ᵥ (H⁻¹ *ᵥ y)) * β := by
    have := el_cs H⁻¹ hH.posSemidef.inv y (H *ᵥ w)
    rwa [e1, e2] at this
  set q := y ⬝ᵥ (H⁻¹ *ᵥ y)
  set s := w ⬝ᵥ y
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hsq : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  set sb := Real.sqrt β
  obtain ⟨u, hu⟩ : ∃ u, s = u * sb := ⟨s / sb, by field_simp⟩
  rw [hu] at hcs hxs ⊢
  have hu2 : u ^ 2 ≤ q := by
    rw [← hsq] at hcs; nlinarith [sq_nonneg sb]
  have hu0 : u ≤ 0 := by
    by_contra h; push_neg at h; nlinarith
  rw [← hsq]
  simp only [smul_eq_mul, τ]
  have h3 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h4 : (n : ℝ) + 1 ≠ 0 := by linarith
  have h6 : (n : ℝ) ≠ 0 := by linarith
  have key : ((n : ℝ) ^ 2 - 1) * q + 2 * ((n : ℝ) + 1) * u * (1 + u) + 1 ≤ (n : ℝ) ^ 2 := by
    have hu1 : -1 ≤ u := by nlinarith
    have hm : u * (1 + u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu0 (by linarith)
    have : 2 * ((n : ℝ) + 1) * u * (1 + u) ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 2 * ((n : ℝ) + 1)) hm
      linarith [this]
    have := mul_le_mul_of_nonneg_left hx (by nlinarith : (0:ℝ) ≤ (n : ℝ) ^ 2 - 1)
    linarith
  calc _ = (((n : ℝ) ^ 2 - 1) * q + 2 * ((n : ℝ) + 1) * u * (1 + u) + 1) / (n : ℝ) ^ 2 := by
        field_simp
        ring
    _ ≤ 1 := by rw [div_le_one (by positivity)]; exact key


lemma el_updM_eq {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    LinearOptimization.ellipsoidUpdateMatrix D (-w) = elNewH D w := by
  unfold LinearOptimization.ellipsoidUpdateMatrix elNewH
  simp [mulVec_neg]

lemma el_updC_eq {n : ℕ} (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    LinearOptimization.ellipsoidUpdateCenter z D (-w) = elNewc z D w := by
  unfold LinearOptimization.ellipsoidUpdateCenter elNewc
  simp [mulVec_neg, sub_eq_add_neg]

lemma el_run_posDef {n : ℕ} (hn : 2 ≤ n) {X : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    {R : ℝ} (hR : 0 < R) {c0 : Fin n → ℝ} {c : ℕ → Fin n → ℝ}
    {H : ℕ → Matrix (Fin n) (Fin n) ℝ} {w : ℕ → Fin n → ℝ}
    (hrun : IsEllipsoidRun X f R c0 c H w) :
    ∀ t, (∀ s < t, w s ≠ 0) → (H t).PosDef := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [hrun.2.1]
    exact PosDef.one.smul (by positivity)
  | succ t ih =>
    intro hw
    have hw' : ∀ s < t, w s ≠ 0 := fun s hs => hw s (by omega)
    have hwt : w t ≠ 0 := hw t (by omega)
    rw [((hrun.2.2 t hw').2.2 hwt).2, el_updM_eq]
    exact elNewH_posDef hn (ih hw') hwt

theorem cut_keeps_X_core {n : ℕ} (hn : 2 ≤ n) (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (R : ℝ) (hR : 0 < R) (c0 : Fin n → ℝ) (c : ℕ → Fin n → ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (w : ℕ → Fin n → ℝ)
    (hrun : IsEllipsoidRun X f R c0 c H w) (t : ℕ) (hw : ∀ s ≤ t, w s ≠ 0)
    (x : Fin n → ℝ) (hxX : x ∈ X) (hxt : x ∈ LinearOptimization.ellipsoid (c t) (H t))
    (hxt1 : x ∉ LinearOptimization.ellipsoid (c (t + 1)) (H (t + 1))) :
    c t ∈ X ∧ f (c t) < f x := by
  have hw' : ∀ s < t, w s ≠ 0 := fun s hs => hw s hs.le
  have hwt : w t ≠ 0 := hw t le_rfl
  have hpd := el_run_posDef hn hR hrun t hw'
  obtain ⟨hout, hin, hupd⟩ := hrun.2.2 t hw'
  obtain ⟨hc1, hH1⟩ := hupd hwt
  rw [hc1, hH1, el_updC_eq, el_updM_eq] at hxt1
  have hpos : 0 < w t ⬝ᵥ (x - c t) := by
    by_contra hcon
    push_neg at hcon
    exact hxt1 (elNewH_contain hn (c t) hpd hwt ⟨hxt, hcon⟩)
  by_cases hct : c t ∈ X
  · refine ⟨hct, ?_⟩
    have := (hin hct).2 x hxX
    linarith
  · exfalso
    have := (hout hct).2 x hxX
    rw [dotProduct_comm] at this
    linarith

open Finset in
lemma el_scalar (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n * (((n : ℝ) - 1) / ((n : ℝ) + 1)) <
      Real.exp (-1 / (n : ℝ)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := (n : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hN2 : 0 < N + 1 := by linarith
  have hN3 : 0 < N ^ 2 - 1 := by nlinarith
  set a := Real.log N
  set b := Real.log (N - 1)
  set c := Real.log (N + 1)
  -- upper bound on -log(1-y), y = 1/N^2
  set y : ℝ := 1 / N ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by positivity)]; nlinarith
  have hU : -Real.log (1 - y) ≤ y + y ^ 2 / 2 + y ^ 3 / (1 - y) := by
    have h := Real.abs_log_sub_add_sum_range_le (show |y| < 1 by rw [abs_of_pos hy0]; exact hy1) 2
    rw [abs_of_pos hy0] at h
    have h2 := (abs_le.mp h).1
    simp [Finset.sum_range_succ] at h2
    norm_num at h2
    linarith
  have hlogy : Real.log (1 - y) = b + c - 2 * a := by
    have : 1 - y = (N - 1) * (N + 1) / N ^ 2 := by rw [hy]; field_simp; ring
    rw [this, Real.log_div (by positivity) (by positivity), Real.log_mul hN1.ne' hN2.ne',
      Real.log_pow]
    push_cast; ring
  -- lower bound on -log(1-z), z = 1/(N+1)
  set z : ℝ := 1 / (N + 1) with hz
  have hz0 : 0 < z := by positivity
  have hz1 : z < 1 := by rw [hz, div_lt_one hN2]; linarith
  have hL : z + z ^ 2 / 2 + z ^ 3 / 3 + z ^ 4 / 4 ≤ -Real.log (1 - z) := by
    have h := Real.hasSum_pow_div_log_of_abs_lt_one (show |z| < 1 by rw [abs_of_pos hz0]; exact hz1)
    have := sum_le_hasSum (Finset.range 4) (fun i _ => by positivity) h
    simp [Finset.sum_range_succ] at this
    norm_num at this
    linarith
  have hlogz : Real.log (1 - z) = a - c := by
    have : 1 - z = N / (N + 1) := by rw [hz]; field_simp; ring
    rw [this, Real.log_div hN0.ne' hN2.ne']
  have hpos : 0 < (N ^ 2 / (N ^ 2 - 1)) ^ n * ((N - 1) / (N + 1)) := by positivity
  rw [← Real.log_lt_iff_lt_exp hpos, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_div (by positivity) hN3.ne', Real.log_div hN1.ne' hN2.ne',
    Real.log_pow]
  have hlog2 : Real.log (N ^ 2 - 1) = b + c := by
    rw [show N ^ 2 - 1 = (N - 1) * (N + 1) by ring, Real.log_mul hN1.ne' hN2.ne']
  rw [hlog2]
  push_cast
  rw [← hN]
  -- numeric inequality
  have hnum : (N - 1) * (y + y ^ 2 / 2 + y ^ 3 / (1 - y)) -
      2 * (z + z ^ 2 / 2 + z ^ 3 / 3 + z ^ 4 / 4) < -1 / N := by
    rw [hy, hz]
    rw [← sub_neg]
    have h1 : (1 : ℝ) - 1 / N ^ 2 = (N ^ 2 - 1) / N ^ 2 := by field_simp
    rw [h1]
    field_simp
    ring_nf
    nlinarith [pow_pos hN0 3, pow_pos hN0 4, pow_pos hN0 5, pow_pos hN0 6, pow_pos hN0 7,
      pow_pos hN0 8, pow_pos hN0 9, pow_pos hN0 10]
  have e1 : (N - 1) * (-Real.log (1 - y)) ≤ (N - 1) * (y + y ^ 2 / 2 + y ^ 3 / (1 - y)) :=
    mul_le_mul_of_nonneg_left hU hN1.le
  rw [hlogy] at e1
  rw [hlogz] at hL
  nlinarith


def elShape {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {v | v ⬝ᵥ (H⁻¹ *ᵥ v) ≤ 1}

lemma el_vol_ellipsoid {n : ℕ} (c : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    volume (LinearOptimization.ellipsoid c H) = volume (elShape H) := by
  have : LinearOptimization.ellipsoid c H = (fun x => x + (-c)) ⁻¹' elShape H := by
    ext x; simp [LinearOptimization.ellipsoid, elShape, sub_eq_add_neg]
  rw [this, measure_preimage_add_right]

lemma el_dot_mulVec_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u z : Fin n → ℝ) :
    (A *ᵥ u) ⬝ᵥ z = u ⬝ᵥ (Aᵀ *ᵥ z) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

lemma el_shape_transform {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) :
    elShape (A * H * Aᵀ) = (Matrix.toLin' A) '' elShape H := by
  have hAt : IsUnit Aᵀ.det := by rw [det_transpose]; exact hA
  have key : ∀ u, (A *ᵥ u) ⬝ᵥ ((A * H * Aᵀ)⁻¹ *ᵥ (A *ᵥ u)) = u ⬝ᵥ (H⁻¹ *ᵥ u) := by
    intro u
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, el_dot_mulVec_left, mulVec_mulVec,
      mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hAt,
      Matrix.one_mul, Matrix.mul_assoc, nonsing_inv_mul _ hA, Matrix.mul_one]
  ext v
  simp only [elShape, Set.mem_image, Set.mem_setOf_eq, Matrix.toLin'_apply]
  constructor
  · intro hv
    refine ⟨A⁻¹ *ᵥ v, ?_, ?_⟩
    · have hv' : A *ᵥ (A⁻¹ *ᵥ v) = v := by rw [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
      rw [← key, hv']; exact hv
    · rw [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
  · rintro ⟨u, hu, rfl⟩
    rw [key]; exact hu

lemma el_vol_transform {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (c c' : Fin n → ℝ) :
    volume (LinearOptimization.ellipsoid c' (A * H * Aᵀ)) =
      ENNReal.ofReal |A.det| * volume (LinearOptimization.ellipsoid c H) := by
  rw [el_vol_ellipsoid, el_vol_ellipsoid, el_shape_transform A H hA,
    MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']

noncomputable def elRho (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n * Real.sqrt (((n : ℝ) - 1) / ((n : ℝ) + 1))

lemma elRho_lt {n : ℕ} (hn : 2 ≤ n) : elRho n < Real.exp (-(1 : ℝ) / (2 * (n : ℝ))) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply lt_of_pow_lt_pow_left₀ 2 (Real.exp_pos _).le
  rw [← Real.exp_nat_mul, elRho, mul_pow, ← pow_mul, mul_comm n 2, pow_mul,
    Real.sq_sqrt (by apply div_nonneg <;> nlinarith), Real.sq_sqrt (by apply div_nonneg <;> linarith)]
  have : (n : ℝ) ≠ 0 := by linarith
  have e : ((2 : ℕ) : ℝ) * (-(1 : ℝ) / (2 * (n : ℝ))) = -1 / (n : ℝ) := by
    push_cast; field_simp
  rw [e]
  exact el_scalar n hn

lemma elRho_nonneg (n : ℕ) : 0 ≤ elRho n := by unfold elRho; positivity


noncomputable def elA {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Real.sqrt ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
    (1 - ((1 - Real.sqrt (((n : ℝ) - 1) / ((n : ℝ) + 1))) / (w ⬝ᵥ (H *ᵥ w))) •
      (H * vecMulVec w w))

lemma elA_det {n : ℕ} (hn : 2 ≤ n) {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    {w : Fin n → ℝ} (hw : w ≠ 0) : (elA H w).det = elRho n := by
  have hβ := el_quad_pos hH hw
  unfold elA elRho
  rw [det_smul, Fintype.card_fin]
  congr 1
  set δ := (1 - Real.sqrt (((n : ℝ) - 1) / ((n : ℝ) + 1))) / (w ⬝ᵥ (H *ᵥ w))
  have : (1 : Matrix (Fin n) (Fin n) ℝ) - δ • (H * vecMulVec w w) =
      1 + replicateCol (Fin 1) (-δ • (H *ᵥ w)) * replicateRow (Fin 1) w := by
    ext i j
    simp [Matrix.mul_apply, vecMulVec, mulVec, dotProduct, sub_eq_add_neg, Matrix.add_apply]
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [this]
  have hd := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (-δ • (H *ᵥ w)) w
  refine hd.trans ?_
  rw [dotProduct_smul, smul_eq_mul]
  simp only [δ]
  field_simp
  ring

lemma elA_factor {n : ℕ} (hn : 2 ≤ n) {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosDef)
    {w : Fin n → ℝ} (hw : w ≠ 0) : elNewH H w = elA H w * H * (elA H w)ᵀ := by
  have hβ := el_quad_pos hH hw
  have hs := el_symm hH.1
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hAt : (elA H w)ᵀ = Real.sqrt ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
      (1 - ((1 - Real.sqrt (((n : ℝ) - 1) / ((n : ℝ) + 1))) / (w ⬝ᵥ (H *ᵥ w))) •
        (vecMulVec w w * H)) := by
    unfold elA
    simp [transpose_mul, hs, transpose_vecMulVec]
  apply mulVec_injective
  funext v
  rw [← mulVec_mulVec, ← mulVec_mulVec, hAt, elNewH_mulVec]
  unfold elA
  have e1 : ∀ z, (H * vecMulVec w w) *ᵥ z = (w ⬝ᵥ z) • (H *ᵥ w) := by
    intro z; rw [← mulVec_mulVec, el_vmv_mulVec, mulVec_smul]
  have e2 : ∀ z, (vecMulVec w w * H) *ᵥ z = (w ⬝ᵥ (H *ᵥ z)) • w := by
    intro z; rw [← mulVec_mulVec, el_vmv_mulVec]
  simp only [smul_mulVec, sub_mulVec, one_mulVec, e1, e2, mulVec_smul, mulVec_sub,
    dotProduct_sub, smul_eq_mul]
  have hk := Real.sq_sqrt (show 0 ≤ (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) by
    apply div_nonneg <;> nlinarith)
  have hq := Real.sq_sqrt (show 0 ≤ ((n : ℝ) - 1) / ((n : ℝ) + 1) by
    apply div_nonneg <;> linarith)
  set K := Real.sqrt ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1))
  set S := Real.sqrt (((n : ℝ) - 1) / ((n : ℝ) + 1))
  set β := w ⬝ᵥ (H *ᵥ w)
  set a := w ⬝ᵥ (H *ᵥ v)
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [← hk]
  have h4 : (n : ℝ) + 1 ≠ 0 := by linarith
  have hS : S ^ 2 * ((n : ℝ) + 1) = (n : ℝ) - 1 := by rw [hq]; field_simp
  field_simp
  linear_combination (-(K ^ 2 * a * (H *ᵥ w) i)) * hS
  

lemma elRho_pos {n : ℕ} (hn : 2 ≤ n) : 0 < elRho n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold elRho
  apply mul_pos
  · apply pow_pos; apply Real.sqrt_pos.mpr; apply div_pos <;> nlinarith
  · apply Real.sqrt_pos.mpr; apply div_pos <;> linarith

lemma elNew_vol {n : ℕ} (hn : 2 ≤ n) (c0 c' : Fin n → ℝ) {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosDef) {w : Fin n → ℝ} (hw : w ≠ 0) :
    volume (LinearOptimization.ellipsoid c' (elNewH H w)) =
      ENNReal.ofReal (elRho n) * volume (LinearOptimization.ellipsoid c0 H) := by
  rw [elA_factor hn hH hw, el_vol_transform _ _ _ c0 c', elA_det hn hH hw,
    abs_of_pos (elRho_pos hn)]
  rw [elA_det hn hH hw]; exact isUnit_iff_ne_zero.mpr (elRho_pos hn).ne'

lemma el_dim_one_case (c0 : Fin 1 → ℝ) (H0 : Matrix (Fin 1) (Fin 1) ℝ) (hH0 : H0.PosDef)
    (w : Fin 1 → ℝ) (hw : w ≠ 0) :
    ∃ (c : Fin 1 → ℝ) (H : Matrix (Fin 1) (Fin 1) ℝ), H.PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid c H ∧
      volume (LinearOptimization.ellipsoid c H) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((1 : ℕ) : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0) := by
  set A : Matrix (Fin 1) (Fin 1) ℝ := (1 / 2 : ℝ) • 1
  have hAdet : A.det = 1 / 2 := by simp [A]
  have hAu : IsUnit A.det := by rw [hAdet]; norm_num
  have hβ := el_quad_pos hH0 hw
  set β := w ⬝ᵥ (H0 *ᵥ w)
  refine ⟨c0 - ((1 : ℝ) / 2 * (Real.sqrt β)⁻¹) • (H0 *ᵥ w), A * H0 * Aᵀ, ?_, ?_, ?_⟩
  · have : A * H0 * Aᵀ = (1 / 4 : ℝ) • H0 := by
      simp only [A, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_smul]; norm_num
    rw [this]; exact hH0.smul (by norm_num)
  · rintro x ⟨hx, hxs⟩
    simp only [LinearOptimization.ellipsoid, Set.mem_setOf_eq] at hx hxs ⊢
    have hsh := el_shape_transform A H0 hAu
    have hmem : x - (c0 - ((1 : ℝ) / 2 * (Real.sqrt β)⁻¹) • (H0 *ᵥ w)) ∈ elShape (A * H0 * Aᵀ) := by
      rw [hsh]
      refine ⟨(2 : ℝ) • (x - c0) + (Real.sqrt β)⁻¹ • (H0 *ᵥ w), ?_, ?_⟩
      · simp only [elShape, Set.mem_setOf_eq]
        have hs := el_symm hH0.1
        have hsi : (H0⁻¹)ᵀ = H0⁻¹ := by rw [transpose_nonsing_inv, hs]
        set y := x - c0
        have e1 : y ⬝ᵥ (H0⁻¹ *ᵥ (H0 *ᵥ w)) = w ⬝ᵥ y := by
          rw [mulVec_mulVec, el_inv_mul hH0, one_mulVec, dotProduct_comm]
        have e2 : (H0 *ᵥ w) ⬝ᵥ (H0⁻¹ *ᵥ (H0 *ᵥ w)) = β := by
          rw [mulVec_mulVec, el_inv_mul hH0, one_mulVec, dotProduct_comm]
        -- one-dimensionality: y is a multiple of H0 w
        have hHw : (H0 *ᵥ w) 0 ≠ 0 := by
          intro h0
          have : H0 *ᵥ w = 0 := by funext i; rw [Fin.fin_one_eq_zero i, h0]; rfl
          rw [show β = w ⬝ᵥ (H0 *ᵥ w) from rfl, this, dotProduct_zero] at hβ
          exact lt_irrefl _ hβ
        set lam := y 0 / (H0 *ᵥ w) 0
        have hy : y = lam • (H0 *ᵥ w) := by
          funext i; rw [Fin.fin_one_eq_zero i]; simp [lam]; field_simp
        have hq : y ⬝ᵥ (H0⁻¹ *ᵥ y) = lam ^ 2 * β := by
          rw [hy, mulVec_smul, dotProduct_smul, smul_dotProduct, e2, smul_eq_mul, smul_eq_mul]
          ring
        have hsv : w ⬝ᵥ y = lam * β := by
          rw [hy, dotProduct_smul, smul_eq_mul]
        rw [hsv] at hxs
        rw [hq] at hx
        have h2 : (2 : ℝ) • y + (Real.sqrt β)⁻¹ • (H0 *ᵥ w) =
            y + ((Real.sqrt β)⁻¹ / 2) • (H0 *ᵥ w) + y + ((Real.sqrt β)⁻¹ / 2) • (H0 *ᵥ w) := by
          rw [two_smul]; module
        have h3 : (2 : ℝ) • y + (Real.sqrt β)⁻¹ • (H0 *ᵥ w) =
            (2 * lam + (Real.sqrt β)⁻¹) • (H0 *ᵥ w) := by
          rw [hy, add_smul, smul_smul]
        rw [h3, mulVec_smul, dotProduct_smul, smul_dotProduct, e2, smul_eq_mul, smul_eq_mul]
        have hsb : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
        have hsq : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
        set sb := Real.sqrt β
        have hl0 : lam ≤ 0 := by
          by_contra h; push_neg at h; nlinarith
        have hl1 : lam ^ 2 * sb ^ 2 ≤ 1 := by rw [hsq]; exact hx
        have hl2 : -1 ≤ lam * sb := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hl0 hsb.le]
        have hl3 : lam * sb ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hl0 hsb.le
        rw [← hsq]
        have : (2 * lam + sb⁻¹) * ((2 * lam + sb⁻¹) * sb ^ 2) = (2 * (lam * sb) + 1) ^ 2 := by
          field_simp
        rw [this]
        nlinarith
      · simp only [Matrix.toLin'_apply, A, smul_mulVec, one_mulVec, smul_add, smul_smul]
        norm_num
        module
    simpa [elShape] using hmem
  · rw [el_vol_transform _ _ hAu c0, hAdet]
    gcongr
    have := Real.add_one_le_exp (-(1 : ℝ) / (2 * ((1 : ℕ) : ℝ)))
    norm_num at this ⊢
    linarith


lemma lemma_2_3_part2 {n : ℕ} (hn : 2 ≤ n) (c0 : Fin n → ℝ) (H0 : Matrix (Fin n) (Fin n) ℝ)
    (hH0 : H0.PosDef) (w : Fin n → ℝ) (hw : w ≠ 0) :
    (elNewH H0 w).PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid (elNewc c0 H0 w) (elNewH H0 w) ∧
      volume (LinearOptimization.ellipsoid (elNewc c0 H0 w) (elNewH H0 w)) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * (n : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0) := by
  refine ⟨elNewH_posDef hn hH0 hw, elNewH_contain hn c0 hH0 hw, ?_⟩
  rw [elNew_vol hn c0 _ hH0 hw]
  gcongr
  exact (elRho_lt hn).le

theorem lemma_2_3_core {n : ℕ} (c0 : Fin n → ℝ) (H0 : Matrix (Fin n) (Fin n) ℝ) (hH0 : H0.PosDef)
    (w : Fin n → ℝ) (hw : w ≠ 0) :
    (∃ (c : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid c H ∧
      volume (LinearOptimization.ellipsoid c H) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * (n : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0)) ∧
    (2 ≤ n →
      (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
          (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
            (H0 * vecMulVec w w * H0))).PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid
          (c0 - ((1 : ℝ) / ((n : ℝ) + 1)) • (Real.sqrt (w ⬝ᵥ (H0 *ᵥ w)))⁻¹ • (H0 *ᵥ w))
          (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
            (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
              (H0 * vecMulVec w w * H0))) ∧
      volume (LinearOptimization.ellipsoid
          (c0 - ((1 : ℝ) / ((n : ℝ) + 1)) • (Real.sqrt (w ⬝ᵥ (H0 *ᵥ w)))⁻¹ • (H0 *ᵥ w))
          (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
            (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
              (H0 * vecMulVec w w * H0)))) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * (n : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0)) := by
  have p2 : 2 ≤ n → _ := fun hn => lemma_2_3_part2 hn c0 H0 hH0 w hw
  refine ⟨?_, p2⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · exact absurd (Subsingleton.elim w 0) hw
    · exact el_dim_one_case c0 H0 hH0 w hw
  · exact ⟨_, _, p2 h⟩

end ConvexOptAlg.Ellipsoid

open ConvexOptAlg.Ellipsoid
open Matrix MeasureTheory

theorem solution {n : ℕ} (c0 : Fin n → ℝ) (H0 : Matrix (Fin n) (Fin n) ℝ) (hH0 : H0.PosDef)
    (w : Fin n → ℝ) (hw : w ≠ 0) :
    (∃ (c : Fin n → ℝ) (H : Matrix (Fin n) (Fin n) ℝ), H.PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid c H ∧
      volume (LinearOptimization.ellipsoid c H) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * (n : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0)) ∧
    (2 ≤ n →
      (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
          (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
            (H0 * vecMulVec w w * H0))).PosDef ∧
      LinearOptimization.ellipsoid c0 H0 ∩ {x | w ⬝ᵥ (x - c0) ≤ 0} ⊆
        LinearOptimization.ellipsoid
          (c0 - ((1 : ℝ) / ((n : ℝ) + 1)) • (Real.sqrt (w ⬝ᵥ (H0 *ᵥ w)))⁻¹ • (H0 *ᵥ w))
          (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
            (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
              (H0 * vecMulVec w w * H0))) ∧
      volume (LinearOptimization.ellipsoid
          (c0 - ((1 : ℝ) / ((n : ℝ) + 1)) • (Real.sqrt (w ⬝ᵥ (H0 *ᵥ w)))⁻¹ • (H0 *ᵥ w))
          (((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) •
            (H0 - ((2 : ℝ) / ((n : ℝ) + 1)) • (w ⬝ᵥ (H0 *ᵥ w))⁻¹ •
              (H0 * vecMulVec w w * H0)))) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * (n : ℝ)))) *
          volume (LinearOptimization.ellipsoid c0 H0)) := by
  exact lemma_2_3_core c0 H0 hH0 w hw
