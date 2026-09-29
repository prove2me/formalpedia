-- Prove2me | solution 1 for ChatterjeeQFT.hermOfVec_det_bijection
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:23:22.037968+00:00
-- url     : https://prove2.me/submissions/2340c3fc-ad6a-4ef5-a452-134f4a6fa192

import Mathlib
import Definitions.Def_ChatterjeeQFT_ElectronSpace

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder
open ChatterjeeQFT

/-! ## hermOfVec basics (SL2C preamble) -/

theorem W3a_ChatterjeeQFT_det_herm (x : Fin 4 → ℝ) :
    (hermOfVec x).det = ((minkowskiSq x : ℝ) : ℂ) := by
  rw [hermOfVec, Matrix.det_fin_two_of]
  simp only [minkowskiSq, minkowskiInner]
  push_cast
  linear_combination ((x 2 : ℂ)) ^ 2 * Complex.I_sq

theorem W3a_ChatterjeeQFT_hdiv (z : ℂ) : (z / (2 * Complex.I)).re = z.im / 2 := by
  rw [div_mul_eq_div_div, Complex.div_I]
  simp

theorem W3a_ChatterjeeQFT_vec_herm (x : Fin 4 → ℝ) : vecOfHerm (hermOfVec x) = x := by
  ext i
  fin_cases i
  · show ((hermOfVec x 0 0 + hermOfVec x 1 1) / 2).re = x 0
    simp [hermOfVec]
    try ring
  · show ((hermOfVec x 0 1 + hermOfVec x 1 0) / 2).re = x 1
    simp [hermOfVec]
    try ring
  · show ((hermOfVec x 1 0 - hermOfVec x 0 1) / (2 * Complex.I)).re = x 2
    rw [W3a_ChatterjeeQFT_hdiv]
    simp [hermOfVec]
    try ring
  · show ((hermOfVec x 0 0 - hermOfVec x 1 1) / 2).re = x 3
    simp [hermOfVec]
    try ring

theorem W3a_ChatterjeeQFT_herm_round (H : Matrix (Fin 2) (Fin 2) ℂ) (hH : H.IsHermitian) :
    hermOfVec (vecOfHerm H) = H := by
  have e00 := hH.apply 0 0
  have e11 := hH.apply 1 1
  have e10 := hH.apply 1 0
  have i00 : (H 0 0).im = 0 := by
    have := congrArg Complex.im e00
    simp at this
    linarith
  have i11 : (H 1 1).im = 0 := by
    have := congrArg Complex.im e11
    simp at this
    linarith
  have r10 : (H 1 0).re = (H 0 1).re := by
    have := congrArg Complex.re e10
    simp at this
    linarith
  have m10 : (H 1 0).im = -(H 0 1).im := by
    have := congrArg Complex.im e10
    simp at this
    linarith
  have hv0 : vecOfHerm H 0 = ((H 0 0).re + (H 1 1).re) / 2 := by
    show ((H 0 0 + H 1 1) / 2).re = _
    simp
  have hv1 : vecOfHerm H 1 = ((H 0 1).re + (H 1 0).re) / 2 := by
    show ((H 0 1 + H 1 0) / 2).re = _
    simp
  have hv2 : vecOfHerm H 2 = ((H 1 0).im - (H 0 1).im) / 2 := by
    show ((H 1 0 - H 0 1) / (2 * Complex.I)).re = _
    rw [W3a_ChatterjeeQFT_hdiv]
    simp
  have hv3 : vecOfHerm H 3 = ((H 0 0).re - (H 1 1).re) / 2 := by
    show ((H 0 0 - H 1 1) / 2).re = _
    simp
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [hermOfVec, hv0, hv1, hv2, hv3] <;> linarith

theorem solution :
    (∀ x : Fin 4 → ℝ, (hermOfVec x).det = ((minkowskiSq x : ℝ) : ℂ)) ∧
      (∀ x : Fin 4 → ℝ, vecOfHerm (hermOfVec x) = x) ∧
      (∀ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian → hermOfVec (vecOfHerm H) = H) :=
  ⟨W3a_ChatterjeeQFT_det_herm, W3a_ChatterjeeQFT_vec_herm, W3a_ChatterjeeQFT_herm_round⟩

theorem W3a_ChatterjeeQFT_herm_isHerm (x : Fin 4 → ℝ) : (hermOfVec x).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfVec, Matrix.conjTranspose_apply] <;> ring

/-! ## Mass shell -/

theorem W3a_ChatterjeeQFT_massShell_eq_graph (m : ℝ) (p : Fin 4 → ℝ) :
    p ∈ massShell m ↔ ∃ q : Fin 3 → ℝ, p = massShellEmb m q := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨![p 1, p 2, p 3], ?_⟩
    have hq : omega m ![p 1, p 2, p 3] = p 0 := by
      unfold omega
      simp only [minkowskiSq, minkowskiInner] at h1
      have e : m ^ 2 + ((![p 1, p 2, p 3] : Fin 3 → ℝ) 0 ^ 2 + (![p 1, p 2, p 3] : Fin 3 → ℝ) 1 ^ 2
          + (![p 1, p 2, p 3] : Fin 3 → ℝ) 2 ^ 2) = p 0 ^ 2 := by
        simp
        nlinarith
      rw [e, Real.sqrt_sq h2]
    ext i
    fin_cases i <;> simp [massShellEmb, hq]
  · rintro ⟨q, rfl⟩
    have h0 : 0 ≤ m ^ 2 + (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) := by positivity
    have hs : omega m q * omega m q = m ^ 2 + (q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2) :=
      Real.mul_self_sqrt h0
    have hnn : 0 ≤ omega m q := Real.sqrt_nonneg _
    refine ⟨?_, ?_⟩
    · simp [minkowskiSq, minkowskiInner, massShellEmb]
      nlinarith [hs]
    · simpa [massShellEmb] using hnn

theorem W3a_ChatterjeeQFT_cone_aux (y0 y1 y2 y3 q0 q1 q2 q3 : ℝ)
    (hq : q0 * q0 - (q1 * q1 + q2 * q2 + q3 * q3) = 1) (hq0 : 0 < q0)
    (hy : 0 ≤ y0 * y0 - (y1 * y1 + y2 * y2 + y3 * y3))
    (hp : 0 ≤ y0 * q0 - (y1 * q1 + y2 * q2 + y3 * q3)) : 0 ≤ y0 := by
  by_contra h
  push_neg at h
  have hCS : (y1 * q1 + y2 * q2 + y3 * q3) * (y1 * q1 + y2 * q2 + y3 * q3)
      ≤ (y1 * y1 + y2 * y2 + y3 * y3) * (q1 * q1 + q2 * q2 + q3 * q3) := by
    nlinarith [sq_nonneg (y1 * q2 - y2 * q1), sq_nonneg (y1 * q3 - y3 * q1),
      sq_nonneg (y2 * q3 - y3 * q2)]
  have h1 : y1 * q1 + y2 * q2 + y3 * q3 ≤ y0 * q0 := by linarith
  have h2 : y0 * q0 < 0 := mul_neg_of_neg_of_pos h hq0
  have h3 : (y0 * q0) * (y0 * q0) ≤
      (y1 * q1 + y2 * q2 + y3 * q3) * (y1 * q1 + y2 * q2 + y3 * q3) := by nlinarith
  have h4 : (y1 * y1 + y2 * y2 + y3 * y3) * (q1 * q1 + q2 * q2 + q3 * q3)
      ≤ (y0 * y0) * (q0 * q0 - 1) :=
    mul_le_mul (by linarith) (by linarith)
      (by nlinarith [mul_self_nonneg q1, mul_self_nonneg q2, mul_self_nonneg q3])
      (mul_self_nonneg y0)
  have h5 : 0 < y0 * y0 := by nlinarith
  nlinarith

theorem W3a_ChatterjeeQFT_massShell_lorentz_invariant (m : ℝ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsRestrictedLorentz L) (p : Fin 4 → ℝ) (hp : p ∈ massShell m) :
    L *ᵥ p ∈ massShell m := by
  obtain ⟨hLor, -, h00⟩ := hL
  obtain ⟨hp1, hp2⟩ := hp
  refine ⟨?_, ?_⟩
  · unfold minkowskiSq at *
    rw [hLor]
    exact hp1
  · have hq : L *ᵥ (Pi.single 0 1 : Fin 4 → ℝ) = fun i => L i 0 := by
      ext i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    have h1 := hLor (Pi.single 0 1) (Pi.single 0 1)
    have h2 := hLor p (Pi.single 0 1)
    have h3 := hLor p p
    rw [hq] at h1 h2
    simp only [minkowskiSq] at hp1
    rw [hp1] at h3
    simp [minkowskiInner] at h1 h2 h3
    apply W3a_ChatterjeeQFT_cone_aux _ ((L *ᵥ p) 1) ((L *ᵥ p) 2) ((L *ᵥ p) 3)
      (L 0 0) (L 1 0) (L 2 0) (L 3 0) ?_ h00 ?_ ?_
    · linarith
    · nlinarith [sq_nonneg m]
    · linarith

theorem W3a_ChatterjeeQFT_massShellMeasure_integral (m : ℝ) (hm : 0 < m)
    (f : (Fin 4 → ℝ) → ℂ) (hf : AEStronglyMeasurable f (massShellMeasure m)) :
    ∫ p, f p ∂(massShellMeasure m)
      = ∫ q : Fin 3 → ℝ, (1 / ((2 * Real.pi) ^ 3 * (2 * omega m q))) • f (massShellEmb m q) := by
  have hcont : Continuous (massShellEmb m) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp [massShellEmb, omega] <;> fun_prop
  have hdens : Measurable fun q : Fin 3 → ℝ =>
      ENNReal.ofReal (1 / ((2 * Real.pi) ^ 3 * (2 * omega m q))) := by
    unfold omega
    fun_prop
  unfold massShellMeasure at hf ⊢
  rw [integral_map hcont.measurable.aemeasurable hf,
    integral_withDensity_eq_integral_toReal_smul hdens
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext q
  rw [ENNReal.toReal_ofReal (by unfold omega; positivity)]

theorem W3a_ChatterjeeQFT_bosonAction_comp (a b : Fin 4 → ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : IsRestrictedLorentz A) (hB : IsRestrictedLorentz B) (ψ : (Fin 4 → ℝ) → ℂ) :
    bosonAction (a + A *ᵥ b) (A * B) ψ = bosonAction a A (bosonAction b B ψ) := by
  have hAdet : IsUnit A.det := by rw [hA.2.1]; exact isUnit_one
  funext p
  simp only [bosonAction]
  rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
  have hinner : minkowskiInner (a + A *ᵥ b) p
      = minkowskiInner a p + minkowskiInner b (A⁻¹ *ᵥ p) := by
    have := hA.1 b (A⁻¹ *ᵥ p)
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hAdet, Matrix.one_mulVec] at this
    rw [← this]
    simp only [minkowskiInner, Pi.add_apply]
    ring
  rw [hinner]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/-! ## Electron space -/

theorem W3a_ChatterjeeQFT_boost_herm (m : ℝ) (p : Fin 4 → ℝ) :
    (pureBoost m p)ᴴ = pureBoost m p := by
  unfold pureBoost
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, (W3a_ChatterjeeQFT_herm_isHerm p).eq]
  simp

theorem W3a_ChatterjeeQFT_electronInner_eq_boosted (m : ℝ) (hm : 0 < m)
    (ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ)) :
    electronInner m ψ φ
      = ∫ p, ∑ i : Fin 2, (starRingEnd ℂ) (((pureBoost m p)⁻¹ *ᵥ ψ p) i) *
          (((pureBoost m p)⁻¹ *ᵥ φ p) i) ∂(massShellMeasure m) := by
  unfold electronInner
  congr 1
  funext p
  have hB : ((pureBoost m p)⁻¹)ᴴ = (pureBoost m p)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, W3a_ChatterjeeQFT_boost_herm]
  have hW : electronWeight m p = (pureBoost m p)⁻¹ * (pureBoost m p)⁻¹ := by
    unfold electronWeight
    rw [Matrix.mul_inv_rev]
  have key : ∀ x y : Fin 2 → ℂ,
      ∑ i : Fin 2, (starRingEnd ℂ) (((pureBoost m p)⁻¹ *ᵥ x) i) * (((pureBoost m p)⁻¹ *ᵥ y) i)
        = star x ⬝ᵥ ((((pureBoost m p)⁻¹)ᴴ * (pureBoost m p)⁻¹) *ᵥ y) := by
    intro x y
    change star ((pureBoost m p)⁻¹ *ᵥ x) ⬝ᵥ ((pureBoost m p)⁻¹ *ᵥ y) = _
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [key, hB]
  unfold electronPairing
  rw [hW]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc]
  rfl

theorem W3a_ChatterjeeQFT_boost_sq (m : ℝ) (hm : 0 < m) (q : Fin 4 → ℝ)
    (hq : minkowskiSq q = m ^ 2) (hq0 : 0 ≤ q 0) :
    pureBoost m q * pureBoost m q = (m : ℂ)⁻¹ • hermOfVec q := by
  have hX : 0 < 2 + 2 * q 0 / m := by positivity
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (2 + 2 * q 0 / m) := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.mpr hX
  have hss : s ^ 2 = 2 + 2 * q 0 / m := hs ▸ Real.sq_sqrt hX.le
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have ht : ((s : ℂ)⁻¹) ^ 2 * (2 + 2 * (q 0 : ℂ) * (m : ℂ)⁻¹) = 1 := by
    have h2 : ((s : ℂ)) ^ 2 = 2 + 2 * (q 0 : ℂ) * (m : ℂ)⁻¹ := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hss
      push_cast at this
      rw [this]
      ring
    rw [← h2]
    field_simp
  have hmu : (m : ℂ) * (m : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hmC
  have hE : ((q 0 : ℂ)) * q 0 - (q 1 * q 1 + q 2 * q 2 + q 3 * q 3) = (m : ℂ) ^ 2 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hq
    simp only [minkowskiSq, minkowskiInner] at this
    push_cast at this
    exact this
  unfold pureBoost
  rw [← hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-((s : ℂ)⁻¹ ^ 2 * (m : ℂ)⁻¹ ^ 2)) * hE
      + (-((s : ℂ)⁻¹ ^ 2 * (m : ℂ)⁻¹ ^ 2 * (q 2 : ℂ) ^ 2)) * Complex.I_sq
      + (-((s : ℂ)⁻¹ ^ 2 * ((m : ℂ) * (m : ℂ)⁻¹ + 1))) * hmu
      + ((m : ℂ)⁻¹ * ((q 0 : ℂ) + q 3)) * ht
  · linear_combination ((m : ℂ)⁻¹ * ((q 1 : ℂ) - Complex.I * q 2)) * ht
  · linear_combination ((m : ℂ)⁻¹ * ((q 1 : ℂ) + Complex.I * q 2)) * ht
  · linear_combination (-((s : ℂ)⁻¹ ^ 2 * (m : ℂ)⁻¹ ^ 2)) * hE
      + (-((s : ℂ)⁻¹ ^ 2 * (m : ℂ)⁻¹ ^ 2 * (q 2 : ℂ) ^ 2)) * Complex.I_sq
      + (-((s : ℂ)⁻¹ ^ 2 * ((m : ℂ) * (m : ℂ)⁻¹ + 1))) * hmu
      + ((m : ℂ)⁻¹ * ((q 0 : ℂ) - q 3)) * ht

theorem W3a_ChatterjeeQFT_hdiag (C : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 2) :
    (C * Cᴴ) i i = ((Complex.normSq (C i 0) + Complex.normSq (C i 1) : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  rw [Complex.star_def, Complex.mul_conj, Complex.mul_conj]
  push_cast
  ring

theorem W3a_ChatterjeeQFT_re_diag_nonneg (m : ℝ) (hm : 0 < m) (C : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ ((((m : ℂ) • (C * Cᴴ)) 0 0 + ((m : ℂ) • (C * Cᴴ)) 1 1) / 2).re := by
  rw [Matrix.smul_apply, Matrix.smul_apply, W3a_ChatterjeeQFT_hdiag C 0,
    W3a_ChatterjeeQFT_hdiag C 1]
  have a1 := mul_nonneg hm.le (Complex.normSq_nonneg (C 0 0))
  have a2 := mul_nonneg hm.le (Complex.normSq_nonneg (C 0 1))
  have a3 := mul_nonneg hm.le (Complex.normSq_nonneg (C 1 0))
  have a4 := mul_nonneg hm.le (Complex.normSq_nonneg (C 1 1))
  simp [Complex.div_ofNat_re]
  nlinarith

theorem W3a_ChatterjeeQFT_electronWeight_intertwine (m : ℝ) (hm : 0 < m)
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.det = 1) (p : Fin 4 → ℝ) (hp : p ∈ massShell m) :
    Aᴴ * electronWeight m (kappa A p) * A = electronWeight m p := by
  obtain ⟨hp1, hp2⟩ := hp
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hMH : (hermOfVec p).IsHermitian := W3a_ChatterjeeQFT_herm_isHerm p
  have hAMA : (A * hermOfVec p * Aᴴ).IsHermitian := by
    unfold Matrix.IsHermitian
    simp [Matrix.conjTranspose_mul, hMH.eq, Matrix.mul_assoc]
  have hHq : hermOfVec (kappa A p) = A * hermOfVec p * Aᴴ := by
    unfold kappa
    exact W3a_ChatterjeeQFT_herm_round _ hAMA
  have hqsq : minkowskiSq (kappa A p) = m ^ 2 := by
    have h1 := W3a_ChatterjeeQFT_det_herm (kappa A p)
    rw [hHq, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hA,
      W3a_ChatterjeeQFT_det_herm, hp1] at h1
    have : ((m ^ 2 : ℝ) : ℂ) = (minkowskiSq (kappa A p) : ℂ) := by
      rw [← h1]
      simp
    exact_mod_cast this.symm
  have hV2 := W3a_ChatterjeeQFT_boost_sq m hm p hp1 hp2
  have hVH := W3a_ChatterjeeQFT_boost_herm m p
  have hM : hermOfVec p = (m : ℂ) • (pureBoost m p * (pureBoost m p)ᴴ) := by
    rw [hVH, hV2, smul_smul, mul_inv_cancel₀ hmC, one_smul]
  have hq0 : 0 ≤ kappa A p 0 := by
    have e : kappa A p 0 = (((A * hermOfVec p * Aᴴ) 0 0 + (A * hermOfVec p * Aᴴ) 1 1) / 2).re :=
      rfl
    have hC : A * hermOfVec p * Aᴴ
        = (m : ℂ) • ((A * pureBoost m p) * (A * pureBoost m p)ᴴ) := by
      rw [hM, Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
      simp [Matrix.mul_assoc]
    rw [e, hC]
    exact W3a_ChatterjeeQFT_re_diag_nonneg m hm _
  have hqb := W3a_ChatterjeeQFT_boost_sq m hm (kappa A p) hqsq hq0
  unfold electronWeight
  rw [hqb, hV2, hHq]
  rw [show (m : ℂ)⁻¹ • (A * hermOfVec p * Aᴴ) = A * ((m : ℂ)⁻¹ • hermOfVec p) * Aᴴ by
    simp [Matrix.mul_smul, Matrix.smul_mul]]
  have hAu : IsUnit A.det := by rw [hA]; exact isUnit_one
  have hAHu : IsUnit Aᴴ.det := by rw [Matrix.det_conjTranspose, hA, star_one]; exact isUnit_one
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAHu,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]

open scoped MatrixOrder in
theorem W3a_ChatterjeeQFT_psd_unique (V W : Matrix (Fin 2) (Fin 2) ℂ) (hV : V.PosSemidef)
    (hW : W.PosSemidef) (h : V * V = W * W) : V = W :=
  (CFC.mul_self_eq_mul_self_iff V W hV.nonneg hW.nonneg).mp h

theorem W3a_ChatterjeeQFT_pureBoost_spec (m : ℝ) (hm : 0 < m) (p : Fin 4 → ℝ)
    (hp : p ∈ massShell m) :
    (pureBoost m p).det = 1 ∧ (pureBoost m p).PosDef ∧
      kappa (pureBoost m p) (restMomentum m) = p ∧
      ∀ V : Matrix (Fin 2) (Fin 2) ℂ, V.det = 1 → V.PosDef →
        kappa V (restMomentum m) = p → V = pureBoost m p := by
  obtain ⟨hp1, hp2⟩ := hp
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hV2 := W3a_ChatterjeeQFT_boost_sq m hm p hp1 hp2
  have hVH : (pureBoost m p).IsHermitian := W3a_ChatterjeeQFT_boost_herm m p
  have hX : 0 < 2 + 2 * p 0 / m := by positivity
  have hE : ((p 0 : ℂ)) * p 0 - (p 1 * p 1 + p 2 * p 2 + p 3 * p 3) = (m : ℂ) ^ 2 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hp1
    simp only [minkowskiSq, minkowskiInner] at this
    push_cast at this
    exact this
  have hrest : hermOfVec (restMomentum m) = (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermOfVec, restMomentum]
  have hkap : ∀ V : Matrix (Fin 2) (Fin 2) ℂ, V.IsHermitian →
      hermOfVec (kappa V (restMomentum m)) = (m : ℂ) • (V * V) := by
    intro V hV
    have e : V * ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Vᴴ = (m : ℂ) • (V * V) := by
      rw [hV.eq]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    unfold kappa
    rw [hrest, e, W3a_ChatterjeeQFT_herm_round]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hV.eq]
    simp
  -- determinant
  have hdet : (pureBoost m p).det = 1 := by
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (2 + 2 * p 0 / m) := ⟨_, rfl⟩
    have hs0 : 0 < s := hs ▸ Real.sqrt_pos.mpr hX
    have hss : s ^ 2 = 2 + 2 * p 0 / m := hs ▸ Real.sq_sqrt hX.le
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have ht : ((s : ℂ)⁻¹) ^ 2 * (2 + 2 * (p 0 : ℂ) * (m : ℂ)⁻¹) = 1 := by
      have h2 : ((s : ℂ)) ^ 2 = 2 + 2 * (p 0 : ℂ) * (m : ℂ)⁻¹ := by
        have := congrArg (fun r : ℝ => (r : ℂ)) hss
        push_cast at this
        rw [this]
        ring
      rw [← h2]
      field_simp
    have hmu : (m : ℂ) * (m : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hmC
    unfold pureBoost
    rw [← hs, Matrix.det_fin_two]
    simp [hermOfVec]
    linear_combination ((s : ℂ)⁻¹ ^ 2 * (m : ℂ)⁻¹ ^ 2) * hE
      + ((s : ℂ)⁻¹ ^ 2 * (m : ℂ)⁻¹ ^ 2 * (p 2 : ℂ) ^ 2) * Complex.I_sq
      + ((s : ℂ)⁻¹ ^ 2 * ((m : ℂ) * (m : ℂ)⁻¹ + 1)) * hmu + ht
  -- positivity of M
  have hMpsd : (hermOfVec p).PosSemidef := by
    obtain ⟨N, hNdef⟩ : ∃ N, N = hermOfVec p + (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
      ⟨_, rfl⟩
    have hNH : Nᴴ = N := by
      rw [hNdef, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        (W3a_ChatterjeeQFT_herm_isHerm p).eq]
      simp
    have hNN : N * N = ((2 * (p 0 + m) : ℝ) : ℂ) • hermOfVec p := by
      rw [hNdef]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hermOfVec, Matrix.mul_apply, Fin.sum_univ_two] <;>
        first
        | ring1
        | linear_combination (-1 : ℂ) * hE + (-((p 2 : ℂ)) ^ 2) * Complex.I_sq
    have hpos : 0 < 2 * (p 0 + m) := by linarith
    have e : hermOfVec p = (((2 * (p 0 + m))⁻¹ : ℝ) : ℂ) • (Nᴴ * N) := by
      rw [hNH, hNN, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one,
        one_smul]
    rw [e]
    exact (posSemidef_conjTranspose_mul_self N).smul
      (Complex.zero_le_real.mpr (inv_pos.mpr hpos).le)
  have hPD : (pureBoost m p).PosDef := by
    unfold pureBoost
    have h1 : ((m : ℂ)⁻¹ • hermOfVec p).PosSemidef := hMpsd.smul (by
      rw [← Complex.ofReal_inv]; exact Complex.zero_le_real.mpr (inv_pos.mpr hm).le)
    have h2 : ((m : ℂ)⁻¹ • hermOfVec p + 1).PosDef :=
      Matrix.PosDef.posSemidef_add h1 Matrix.PosDef.one
    exact h2.smul (by
      rw [← Complex.ofReal_inv]
      exact Complex.zero_lt_real.mpr (inv_pos.mpr (Real.sqrt_pos.mpr hX)))
  have hk : kappa (pureBoost m p) (restMomentum m) = p := by
    rw [← W3a_ChatterjeeQFT_vec_herm (kappa (pureBoost m p) (restMomentum m)), hkap _ hVH, hV2,
      smul_smul, mul_inv_cancel₀ hmC, one_smul, W3a_ChatterjeeQFT_vec_herm]
  refine ⟨hdet, hPD, hk, fun V _ hVpd hVk => ?_⟩
  have h1 := hkap V hVpd.isHermitian
  rw [hVk] at h1
  have hVV : V * V = pureBoost m p * pureBoost m p := by
    rw [hV2, h1, smul_smul, inv_mul_cancel₀ hmC, one_smul]
  exact W3a_ChatterjeeQFT_psd_unique V _ hVpd.posSemidef hPD.posSemidef hVV
