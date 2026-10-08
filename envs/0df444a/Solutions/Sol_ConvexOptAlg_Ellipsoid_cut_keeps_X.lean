-- Prove2me | solution 1 for ConvexOptAlg.Ellipsoid.cut_keeps_X
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:59:23.06798+00:00
-- url     : https://prove2.me/submissions/bdccdb9e-b8c8-47c9-b7a7-df4d7c66e42f

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

end ConvexOptAlg.Ellipsoid

open ConvexOptAlg.Ellipsoid


theorem solution {n : ℕ} (hn : 2 ≤ n) (X : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (R : ℝ) (hR : 0 < R) (c0 : Fin n → ℝ) (c : ℕ → Fin n → ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (w : ℕ → Fin n → ℝ)
    (hrun : IsEllipsoidRun X f R c0 c H w) (t : ℕ) (hw : ∀ s ≤ t, w s ≠ 0)
    (x : Fin n → ℝ) (hxX : x ∈ X) (hxt : x ∈ LinearOptimization.ellipsoid (c t) (H t))
    (hxt1 : x ∉ LinearOptimization.ellipsoid (c (t + 1)) (H (t + 1))) :
    c t ∈ X ∧ f (c t) < f x := by
  exact cut_keeps_X_core hn X f R hR c0 c H w hrun t hw x hxX hxt hxt1
