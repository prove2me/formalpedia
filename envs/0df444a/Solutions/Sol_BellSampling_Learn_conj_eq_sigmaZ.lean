-- Prove2me | solution 1 for BellSampling.Learn.conj_eq_sigmaZ
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:04:30.862022+00:00
-- url     : https://prove2.me/submissions/df447760-fb84-40c7-8965-343b6462d6a7

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank
open BellSampling.Learn
set_option autoImplicit false

private noncomputable def chiSign {n : ℕ} (d x : Bits n) : ℂ :=
  (-1 : ℂ) ^ (Finset.univ.filter (fun i : Fin n => d i && x i)).card

private noncomputable def Z {n : ℕ} (d : Bits n) : Matrix (Bits n) (Bits n) ℂ :=
  pauliMatrix (fun _ => false) d

private lemma chiSign_eq_prod {n : ℕ} (d x : Bits n) :
    chiSign d x = ∏ i : Fin n, if d i && x i then (-1 : ℂ) else 1 := by
  unfold chiSign
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

private lemma chiSign_sq {n : ℕ} (d x : Bits n) :
    chiSign d x * chiSign d x = 1 := by
  unfold chiSign
  rw [← mul_pow]
  norm_num

private lemma chiSign_star {n : ℕ} (d x : Bits n) :
    star (chiSign d x) = chiSign d x := by
  simp [chiSign]

private lemma chiSign_norm {n : ℕ} (d x : Bits n) :
    ‖chiSign d x‖ = 1 := by
  simp [chiSign]

private lemma chiSign_xor {n : ℕ} (d a x : Bits n) :
    chiSign d (fun i => xor (a i) (x i)) = chiSign d a * chiSign d x := by
  simp only [chiSign_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases d i <;> cases a i <;> cases x i <;> norm_num

private lemma Z_apply {n : ℕ} (d y x : Bits n) :
    Z d y x = if y = x then chiSign d x else 0 := by
  simp [Z, pauliMatrix, chiSign]

private lemma Z_mulVec {n : ℕ} (d : Bits n) (v : QState n) (x : Bits n) :
    (Z d).mulVec v x = chiSign d x * v x := by
  simp [Matrix.mulVec, dotProduct, Z_apply]

private lemma Z_mulVec_Z_mulVec {n : ℕ} (d : Bits n) (v : QState n) :
    (Z d).mulVec ((Z d).mulVec v) = v := by
  ext x
  simp [Z_mulVec, ← mul_assoc, chiSign_sq]

private lemma Z_mulVec_zeroState {n : ℕ} (b : Bits n) :
    (Z b).mulVec (zeroState n) = zeroState n := by
  ext x
  by_cases hx : x = (fun _ => false)
  · subst hx
    simp [Z_mulVec, zeroState, chiSign]
  · simp [Z_mulVec, zeroState, hx]

private lemma Z_conjTranspose {n : ℕ} (b : Bits n) :
    (Z b).conjTranspose = Z b := by
  ext y x
  simp only [Matrix.conjTranspose_apply, Z_apply]
  by_cases hxy : y = x
  · subst hxy
    simp [chiSign_star]
  · simp [hxy, Ne.symm hxy]

private lemma sum_chiSign_mul {n : ℕ} (x y : Bits n) :
    (∑ d : Bits n, chiSign d x * chiSign d y) = if x = y then (2 : ℂ) ^ n else 0 := by
  simp_rw [chiSign_eq_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (a : Bool) =>
    (if a && x i then (-1 : ℂ) else 1) * (if a && y i then (-1 : ℂ) else 1))]
  have h1 : ∀ i : Fin n,
      (∑ a : Bool, (if a && x i then (-1 : ℂ) else 1) * (if a && y i then (-1 : ℂ) else 1)) =
        if x i = y i then 2 else 0 := by
    intro i
    cases x i <;> cases y i <;> norm_num
  simp_rw [h1]
  by_cases hxy : x = y
  · subst hxy
    simp
  · have hne : ∃ i : Fin n, x i ≠ y i := by
      by_contra h
      exact hxy (funext fun i => not_ne_iff.mp (fun hi => h ⟨i, hi⟩))
    rcases hne with ⟨i, hi⟩
    rw [if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private lemma sum_chiSign {n : ℕ} (x : Bits n) :
    (∑ b : Bits n, chiSign b x) = if x = (fun _ => false) then (2 : ℂ) ^ n else 0 := by
  have h1 : (∑ b : Bits n, chiSign b x) =
      ∑ b : Bits n, chiSign b x * chiSign b (fun _ => false) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [chiSign]
  rw [h1]
  exact sum_chiSign_mul x (fun _ => false)

private lemma pauliGroupSet_comm_map_star {n : ℕ} {P : Matrix (Bits n) (Bits n) ℂ}
    (hP : P ∈ pauliGroupSet n) (d : Bits n) :
    Z d * P.map star = P * Z d ∨ Z d * P.map star = -(P * Z d) := by
  rcases hP with ⟨c, a, w, rfl⟩
  have h_mat : Z d * (pauliMatrix a w).map star = chiSign d a • (pauliMatrix a w * Z d) := by
    ext y x
    simp only [Matrix.mul_apply, Z_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    simp only [pauliMatrix, Matrix.of_apply]
    by_cases hy : y = (fun i => xor (a i) (x i))
    · subst hy
      simp [chiSign_xor]
      ring
    · simp [hy]
  have h_star_smul : (Complex.I ^ (c : ℕ) • pauliMatrix a w).map star =
      star (Complex.I ^ (c : ℕ)) • (pauliMatrix a w).map star := by
    ext y x
    simp [Matrix.map_apply]
  have h_lhs : Z d * (Complex.I ^ (c : ℕ) • pauliMatrix a w).map star =
      (star (Complex.I ^ (c : ℕ)) * chiSign d a) • (pauliMatrix a w * Z d) := by
    rw [h_star_smul, Matrix.mul_smul, h_mat, smul_smul]
  have h_rhs : (Complex.I ^ (c : ℕ) • pauliMatrix a w) * Z d =
      Complex.I ^ (c : ℕ) • (pauliMatrix a w * Z d) := by
    rw [Matrix.smul_mul]
  have hc_sign : ∃ s₁ : ℂ, (s₁ = 1 ∨ s₁ = -1) ∧
      star (Complex.I ^ (c : ℕ)) = s₁ * Complex.I ^ (c : ℕ) := by
    fin_cases c
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨-1, Or.inr rfl, by simp⟩
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨-1, Or.inr rfl, by simp [pow_succ]⟩
  obtain ⟨s₁, hs₁, hc_eq⟩ := hc_sign
  have hd_sign : chiSign d a = 1 ∨ chiSign d a = -1 := by
    unfold chiSign
    exact neg_one_pow_eq_or ℂ _
  rw [h_lhs, h_rhs, hc_eq]
  rcases hs₁ with rfl | rfl <;> rcases hd_sign with hd | hd <;> rw [hd]
  · left; simp
  · right; simp [neg_smul]
  · right; simp [neg_smul]
  · left; simp

private lemma stabilizer_norm_sq_sum {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∑ x : Bits n, ‖ψ x‖ ^ 2 = 1 := by
  rcases hψ with ⟨U, ⟨hU_unit, _⟩, rfl⟩
  have hU : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU_unit
  have hdot : star (U.mulVec (zeroState n)) ⬝ᵥ (U.mulVec (zeroState n)) = 1 := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
      Matrix.vecMul_one]
    simp [dotProduct, zeroState]
  have h_re : (star (U.mulVec (zeroState n)) ⬝ᵥ (U.mulVec (zeroState n))).re = 1 := by
    rw [hdot, Complex.one_re]
  have h_sum_re : (star (U.mulVec (zeroState n)) ⬝ᵥ (U.mulVec (zeroState n))).re =
      ∑ x : Bits n, ‖(U.mulVec (zeroState n)) x‖ ^ 2 := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hc : star ((U.mulVec (zeroState n)) x) * (U.mulVec (zeroState n)) x =
        ((‖(U.mulVec (zeroState n)) x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    rw [hc, Complex.ofReal_re]
  linarith

private lemma sigma_zStr_eq_Z {n : ℕ} (d : Bits n) :
    sigma (zStr (Finset.univ.filter (fun i : Fin n => d i = true))) = Z d := by
  set S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => d i = true)
  ext y x
  simp only [sigma, Matrix.of_apply, Z_apply, chiSign_eq_prod]
  have h1 : ∀ i : Fin n, sigma1 (zStr S i) (y i) (x i) =
      if y i = x i then (if d i && x i then (-1 : ℂ) else 1) else 0 := by
    intro i
    have h01 : (0 : ZMod 2) ≠ 1 := by decide
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    by_cases hd : d i = true
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hd⟩
      cases y i <;> cases x i <;>
        simp [zStr, hiS, hd, sigma1, sigma10, bitIdx, h01, h10]
    · have hiS : i ∉ S := fun h => hd (Finset.mem_filter.mp h).2
      have hdf : d i = false := Bool.eq_false_iff.mpr hd
      cases y i <;> cases x i <;>
        simp [zStr, hiS, hdf, sigma1, sigma00, bitIdx]
  simp_rw [h1]
  by_cases hxy : y = x
  · subst hxy
    simp
  · have hne : ∃ i : Fin n, y i ≠ x i := by
      by_contra h
      exact hxy (funext fun i => not_ne_iff.mp (fun hi => h ⟨i, hi⟩))
    rcases hne with ⟨i, hi⟩
    rw [if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem solution {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ) :
    ∃ S : Finset (Fin n), ∃ c : ℂ, ‖c‖ = 1 ∧
      (fun x => star (ψ x)) = c • (sigma (zStr S)).mulVec ψ := by
  have hnorm : ∑ x : Bits n, ‖ψ x‖ ^ 2 = 1 := stabilizer_norm_sq_sum ψ hψ
  rcases hψ with ⟨U, ⟨hU_unit, hU_cliff⟩, hψ_eq⟩
  have hU_left : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU_unit
  have hU_right : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hU_unit
  set ψ_conj : QState n := fun x => star (ψ x)
  have hex_x0 : ∃ x₀ : Bits n, ψ x₀ ≠ 0 := by
    by_contra h_all
    have h0 : ∀ x : Bits n, ψ x = 0 := fun x => not_ne_iff.mp (fun hx => h_all ⟨x, hx⟩)
    have hsum0 : ∑ x : Bits n, ‖ψ x‖ ^ 2 = 0 := by simp [h0]
    linarith
  obtain ⟨x₀, hx₀⟩ := hex_x0
  have hex_d : ∃ d : Bits n, star ψ ⬝ᵥ (Z d).mulVec ψ_conj ≠ 0 := by
    by_contra h_all
    have hd0 : ∀ d : Bits n, star ψ ⬝ᵥ (Z d).mulVec ψ_conj = 0 :=
      fun d => not_ne_iff.mp (fun hd => h_all ⟨d, hd⟩)
    have hsum_d : (∑ d : Bits n, chiSign d x₀ * (star ψ ⬝ᵥ (Z d).mulVec ψ_conj)) = 0 := by
      simp [hd0]
    have hsum_eval : (∑ d : Bits n, chiSign d x₀ * (star ψ ⬝ᵥ (Z d).mulVec ψ_conj)) =
        (2 : ℂ) ^ n * (star (ψ x₀) * star (ψ x₀)) := by
      simp only [dotProduct, Pi.star_apply, Z_mulVec, ψ_conj]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have h_inner : ∀ x : Bits n,
          (∑ d : Bits n, chiSign d x₀ * (star (ψ x) * (chiSign d x * star (ψ x)))) =
            (star (ψ x) * star (ψ x)) * if x₀ = x then (2 : ℂ) ^ n else 0 := by
        intro x
        have h_rearr : ∀ d : Bits n,
            chiSign d x₀ * (star (ψ x) * (chiSign d x * star (ψ x))) =
              (star (ψ x) * star (ψ x)) * (chiSign d x₀ * chiSign d x) := by
          intro d; ring
        simp_rw [h_rearr, ← Finset.mul_sum, sum_chiSign_mul]
      simp_rw [h_inner, mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      ring
    rw [hsum_eval] at hsum_d
    have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hstar : star (ψ x₀) ≠ 0 := star_ne_zero.mpr hx₀
    exact mul_ne_zero h2n (mul_ne_zero hstar hstar) hsum_d
  obtain ⟨d, hd_ne⟩ := hex_d
  set φ : QState n := (Z d).mulVec ψ_conj
  set P : Bits n → Matrix (Bits n) (Bits n) ℂ := fun b => U * Z b * U.conjTranspose
  have hP_mem : ∀ b : Bits n, P b ∈ pauliGroupSet n := by
    intro b
    have hZb : Z b ∈ pauliGroupSet n := ⟨0, fun _ => false, b, by simp [Z]⟩
    exact hU_cliff (Z b) hZb
  have hP_herm : ∀ b : Bits n, (P b).conjTranspose = P b := by
    intro b
    simp [P, Matrix.conjTranspose_mul, Z_conjTranspose, Matrix.mul_assoc]
  have hP_ψ : ∀ b : Bits n, (P b).mulVec ψ = ψ := by
    intro b
    rw [hψ_eq]
    simp only [P]
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (zeroState n) U.conjTranspose U,
      hU_left, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Z_mulVec_zeroState]
  have hP_star_ψ : ∀ b : Bits n, ((P b).map star).mulVec ψ_conj = ψ_conj := by
    intro b
    ext x
    have h1 := congr_fun (hP_ψ b) x
    have h2 : star ((P b).mulVec ψ x) = star (ψ x) := congr_arg star h1
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul', ψ_conj] using h2
  have hP_φ_or : ∀ b : Bits n, (P b).mulVec φ = φ ∨ (P b).mulVec φ = -φ := by
    intro b
    have h1 : φ = (Z d * (P b).map star).mulVec ψ_conj := by
      rw [← Matrix.mulVec_mulVec, hP_star_ψ]
    rcases pauliGroupSet_comm_map_star (hP_mem b) d with hcomm | hcomm
    · left
      rw [hcomm, ← Matrix.mulVec_mulVec] at h1
      exact h1.symm
    · right
      rw [hcomm, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec] at h1
      exact neg_eq_iff_eq_neg.mp h1.symm
  have hP_φ : ∀ b : Bits n, (P b).mulVec φ = φ := by
    intro b
    rcases hP_φ_or b with hpos | hneg
    · exact hpos
    · exfalso
      have h_dot1 : star ψ ⬝ᵥ (P b).mulVec φ = -(star ψ ⬝ᵥ φ) := by
        rw [hneg, dotProduct_neg]
      have h_dot2 : star ψ ⬝ᵥ (P b).mulVec φ = star ψ ⬝ᵥ φ := by
        rw [Matrix.dotProduct_mulVec, ← hP_herm b, ← Matrix.star_mulVec, hP_ψ b]
      have h_eq : star ψ ⬝ᵥ φ = -(star ψ ⬝ᵥ φ) := h_dot2.symm.trans h_dot1
      have h_add : (2 : ℂ) * (star ψ ⬝ᵥ φ) = 0 := by
        linear_combination h_eq
      exact mul_ne_zero (by norm_num) hd_ne h_add
  have h_Ustar_φ : (U.conjTranspose.mulVec φ) (fun _ => false) = star ψ ⬝ᵥ φ := by
    have hψ_pt : ∀ y : Bits n, ψ y = U y (fun _ => false) := by
      intro y
      rw [hψ_eq]
      simp [Matrix.mulVec, dotProduct, zeroState]
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hψ_pt y]
  have h_sum_P : ∀ x : Bits n,
      (∑ b : Bits n, (P b).mulVec φ x) = (2 : ℂ) ^ n * (star ψ ⬝ᵥ φ) * ψ x := by
    intro x
    set v : QState n := U.conjTranspose.mulVec φ
    have h_step1 : ∀ b : Bits n, (P b).mulVec φ x = (U.mulVec ((Z b).mulVec v)) x := by
      intro b
      simp only [P, v, ← Matrix.mulVec_mulVec]
    simp_rw [h_step1, Matrix.mulVec, dotProduct, Z_mulVec]
    rw [Finset.sum_comm]
    have h_inner : ∀ y : Bits n,
        (∑ b : Bits n, U x y * (chiSign b y * v y)) =
          U x y * v y * if y = (fun _ => false) then (2 : ℂ) ^ n else 0 := by
      intro y
      have h_rearr : ∀ b : Bits n, U x y * (chiSign b y * v y) = (U x y * v y) * chiSign b y := by
        intro b; ring
      simp_rw [h_rearr, ← Finset.mul_sum, sum_chiSign]
    simp_rw [h_inner, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hψ_x : ψ x = U x (fun _ => false) := by
      rw [hψ_eq]
      simp [Matrix.mulVec, dotProduct, zeroState]
    rw [← hψ_x, h_Ustar_φ]
    simp only [dotProduct]
    ring
  set c : ℂ := star ψ ⬝ᵥ φ
  have hφ_eq : φ = c • ψ := by
    ext x
    have h1 := h_sum_P x
    simp_rw [hP_φ, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h1
    have h2n : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have h2 : (2 : ℂ) ^ n * φ x = (2 : ℂ) ^ n * (c * ψ x) := by
      calc
        (2 : ℂ) ^ n * φ x = (2 : ℂ) ^ n * c * ψ x := h1
        _ = (2 : ℂ) ^ n * (c * ψ x) := by ring
    exact mul_left_cancel₀ h2n h2
  have h_star_eq : ψ_conj = c • (Z d).mulVec ψ := by
    have h1 : (Z d).mulVec φ = (Z d).mulVec (c • ψ) := congr_arg (Z d).mulVec hφ_eq
    rwa [Z_mulVec_Z_mulVec, Matrix.mulVec_smul] at h1
  have hc_norm : ‖c‖ = 1 := by
    have h_pt : ∀ x : Bits n, ‖ψ x‖ ^ 2 = ‖c‖ ^ 2 * ‖ψ x‖ ^ 2 := by
      intro x
      have h1 := congr_fun h_star_eq x
      simp only [ψ_conj, Pi.smul_apply, Z_mulVec, smul_eq_mul] at h1
      have h2 := congr_arg (fun z : ℂ => ‖z‖ ^ 2) h1
      simpa [norm_mul, chiSign_norm, mul_pow] using h2
    have h_sum := Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => h_pt x
    rw [← Finset.mul_sum, hnorm, mul_one] at h_sum
    have hc_sq : ‖c‖ ^ 2 = 1 ^ 2 := by linarith
    exact (sq_eq_sq₀ (norm_nonneg c) zero_le_one).mp hc_sq
  refine ⟨Finset.univ.filter (fun i : Fin n => d i = true), c, hc_norm, ?_⟩
  rw [sigma_zStr_eq_Z]
  exact h_star_eq
