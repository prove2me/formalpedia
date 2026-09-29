-- Prove2me | solution 1 for CerednikDrinfeld.exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/25bdeefa-1330-5f41-9b43-caa9a9615b41

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace R4VH

open Matrix

section GLpart

variable {K : Type*} [Field K] {A : Type*} [CommGroup A]

def dGL (d : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(d : K), 1]) (by simp)

@[scoped simp] theorem coe_dGL (d : Kˣ) : ((dGL d : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    Matrix.diagonal ![(d : K), 1] := rfl

theorem dGL_mul (d d' : Kˣ) : dGL (d * d') = dGL d * dGL d' := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [coe_dGL, Units.val_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext l
  fin_cases l <;> simp

theorem dGL_one : dGL (1 : Kˣ) = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [coe_dGL, Units.val_one, Matrix.GeneralLinearGroup.coe_one]
  have : (![(1 : K), 1]) = fun _ => 1 := by funext l; fin_cases l <;> rfl
  rw [this, Matrix.diagonal_one]

theorem det_dGL (d : Kˣ) : Matrix.GeneralLinearGroup.det (dGL d) = d := by
  ext; simp [Matrix.GeneralLinearGroup.val_det_apply, coe_dGL]

def wGL : Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

def sGL (d : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![((d⁻¹ : Kˣ) : K), (d : K)]) (by simp)

theorem sGL_mul_dGL_mul_wGL (d : Kˣ) : sGL d * dGL d * (wGL : Matrix.GeneralLinearGroup (Fin 2) K) = wGL * dGL d := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, sGL, wGL, coe_dGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

variable (ν : Matrix.GeneralLinearGroup (Fin 2) K →* A)

theorem apply_sGL (d : Kˣ) : ν (sGL d) = 1 := by
  have h := congrArg ν (sGL_mul_dGL_mul_wGL d)
  rw [map_mul, map_mul, map_mul] at h

  have : ν (sGL d) * (ν (dGL d) * ν wGL) = 1 * (ν (dGL d) * ν wGL) := by
    rw [one_mul, ← mul_assoc, h, mul_comm]
  exact mul_right_cancel this

theorem diagonalGL_eq (d₀ d₁ : Kˣ) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(d₀ : K), d₁]) (by simp) = dGL (d₀ * d₁) * sGL d₁ := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, sGL, coe_dGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.diagonal_mul_diagonal, Units.val_mul]
  congr 1
  funext l
  fin_cases l <;> simp

def tGL (t : Matrix.TransvectionStruct (Fin 2) K) : Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix (by simp [t.det])

theorem apply_tGL (a : K) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (t : Matrix.TransvectionStruct (Fin 2) K) : ν (tGL t) = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  have ha1' : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  set c' := c / (a - 1) with hc'
  have hcc : c + c' = a * c' := by rw [hc']; field_simp; ring
  have hcc' : c' + c = a * c' := by rw [add_comm]; exact hcc

  let Dm : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal (Function.update (fun _ => (1 : K)) i a)
  have hDdet : Dm.det ≠ 0 := by
    simp only [Dm, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun l _ => ?_
    by_cases hl : l = i
    · subst hl; simpa
    · rw [Function.update_of_ne hl]; exact one_ne_zero
  let D : Matrix.GeneralLinearGroup (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Dm hDdet
  let T : K → Matrix.GeneralLinearGroup (Fin 2) K := fun x => tGL ⟨i, j, hij, x⟩

  have key : T c * T c' * D = D * T c' := by
    apply Matrix.GeneralLinearGroup.ext
    intro k l
    simp only [T, D, Dm, tGL, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.TransvectionStruct.toMatrix_mk]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · fin_cases k <;> fin_cases l <;>
        simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply,
          Matrix.diagonal, Function.update, hcc, hcc']
    · fin_cases k <;> fin_cases l <;>
        simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply,
          Matrix.diagonal, Function.update, hcc, hcc']
    · exact absurd rfl hij
  have h := congrArg ν key
  rw [map_mul, map_mul, map_mul] at h
  have : ν (T c) * (ν (T c') * ν D) = 1 * (ν (T c') * ν D) := by
    rw [one_mul, ← mul_assoc, h, mul_comm]
  exact mul_right_cancel this

theorem apply_eq_apply_dGL_det (a : K) (ha0 : a ≠ 0) (ha1 : a ≠ 1) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ν g = ν (dGL (Matrix.GeneralLinearGroup.det g)) := by

  suffices H : ∀ (Mx : Matrix (Fin 2) (Fin 2) K), Mx.det ≠ 0 → ∀ (h : Mx.det ≠ 0),
      ν (Matrix.GeneralLinearGroup.mkOfDetNeZero Mx h) = ν (dGL (Units.mk0 Mx.det h)) by
    have hg : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
    have h1 : Matrix.GeneralLinearGroup.mkOfDetNeZero (g : Matrix (Fin 2) (Fin 2) K) hg = g :=
      Matrix.GeneralLinearGroup.ext fun _ _ => rfl
    have h2 : Units.mk0 (g : Matrix (Fin 2) (Fin 2) K).det hg = Matrix.GeneralLinearGroup.det g := Units.ext rfl
    rw [← h2, ← H _ hg hg, h1]
  intro Mx hMx
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun N => ∀ (h : N.det ≠ 0), ν (Matrix.GeneralLinearGroup.mkOfDetNeZero N h) = ν (dGL (Units.mk0 N.det h)))
    Mx hMx ?_ ?_ ?_
  · intro Dv hD h
    have h0 : Dv 0 ≠ 0 := by
      intro h0; apply hD; simp [Matrix.det_diagonal, Fin.prod_univ_two, h0]
    have h1 : Dv 1 ≠ 0 := by
      intro h1; apply hD; simp [Matrix.det_diagonal, Fin.prod_univ_two, h1]
    have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal Dv) h =
        Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![((Units.mk0 _ h0 : Kˣ) : K), ((Units.mk0 _ h1 : Kˣ) : K)])
          (by simp [h0, h1]) :=
      Matrix.GeneralLinearGroup.ext fun i j => by
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
    have hdet : Units.mk0 (Matrix.diagonal Dv).det h = Units.mk0 _ h0 * Units.mk0 _ h1 := by
      ext; simp [Matrix.det_diagonal, Fin.prod_univ_two]
    rw [hmk, diagonalGL_eq, map_mul, apply_sGL, mul_one, hdet]
  · intro t h
    have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero t.toMatrix h = tGL t := Matrix.GeneralLinearGroup.ext fun _ _ => rfl
    have hdet : Units.mk0 t.toMatrix.det h = 1 := by ext; simp [t.det]
    rw [hmk, apply_tGL ν a ha0 ha1, hdet, dGL_one, map_one]
  · intro P Q hP hQ HP HQ h
    have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero (P * Q) h =
        Matrix.GeneralLinearGroup.mkOfDetNeZero P hP * Matrix.GeneralLinearGroup.mkOfDetNeZero Q hQ :=
      Matrix.GeneralLinearGroup.ext fun _ _ => rfl
    have hdet : Units.mk0 (P * Q).det h = Units.mk0 P.det hP * Units.mk0 Q.det hQ := by ext; simp
    rw [hmk, map_mul, HP hP, HQ hQ, hdet, dGL_mul, map_mul]

end GLpart

section Padicpart

variable {r : ℕ} [Fact r.Prime]

theorem exists_pow_eq_of_norm_sub_one_lt (w : ℤ_[r]) (hw : ‖w - 1‖ < 1) (q : ℕ) (hq : q.Prime) (hqr : q ≠ r) :
    ∃ z : ℤ_[r], z ^ q = w := by
  let F : Polynomial ℤ_[r] := Polynomial.X ^ q - Polynomial.C w
  have hF1 : F.aeval (1 : ℤ_[r]) = 1 - w := by simp [F]
  have hF' : F.derivative.aeval (1 : ℤ_[r]) = (q : ℤ_[r]) := by
    simp [F, Polynomial.derivative_pow]
  have hqnorm : ‖(q : ℤ_[r])‖ = 1 := by
    rw [PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out hq).mpr (Ne.symm hqr)
  have hnorm : ‖F.aeval (1 : ℤ_[r])‖ < ‖F.derivative.aeval (1 : ℤ_[r])‖ ^ 2 := by
    rw [hF1, hF', hqnorm, one_pow, ← norm_neg, neg_sub]
    exact hw
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  refine ⟨z, ?_⟩
  have : z ^ q - w = 0 := by simpa [F] using hz
  exact sub_eq_zero.mp this

theorem norm_pow_sub_one_lt (u : ℤ_[r]ˣ) : ‖(u : ℤ_[r]) ^ (r - 1) - 1‖ < 1 := by
  have hu : PadicInt.toZMod (u : ℤ_[r]) ≠ 0 := (PadicInt.toZMod.isUnit_map u.isUnit).ne_zero
  have hker : (u : ℤ_[r]) ^ (r - 1) - 1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[r] →+* ZMod r) := by
    rw [RingHom.mem_ker, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one hu, sub_self]
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hker
  exact PadicInt.mem_nonunits.mp (fun h => hker h)

omit [Fact r.Prime] in

theorem int_eq_zero_of_forall_prime_dvd (n : ℤ) (h : ∀ q : ℕ, q.Prime → q ≠ r → (q : ℤ) ∣ n) : n = 0 := by
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (n.natAbs + r + 1)
  have hqr : q ≠ r := by omega
  have hd : (q : ℤ) ∣ n := h q hqp hqr
  have hd' : q ∣ n.natAbs := Int.natCast_dvd.mp hd
  by_contra hn
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have := Nat.le_of_dvd hpos hd'
  omega

theorem apply_unitsMap_eq_one (f : ℚ_[r]ˣ →* Multiplicative ℤ) (u : ℤ_[r]ˣ) :
    f (Units.map (algebraMap ℤ_[r] ℚ_[r] : ℤ_[r] →* ℚ_[r]) u) = 1 := by
  set x : ℤ := Multiplicative.toAdd (f (Units.map (algebraMap ℤ_[r] ℚ_[r] : ℤ_[r] →* ℚ_[r]) u)) with hx
  have hr1 : 1 ≤ r - 1 := by have := (Fact.out : r.Prime).two_le; omega

  have hdiv : ∀ q : ℕ, q.Prime → q ≠ r → (q : ℤ) ∣ ((r - 1 : ℕ) : ℤ) * x := by
    intro q hq hqr
    obtain ⟨z, hz⟩ := exists_pow_eq_of_norm_sub_one_lt _ (norm_pow_sub_one_lt u) q hq hqr
    have hzu : IsUnit z := (isUnit_pow_iff hq.ne_zero).mp (hz ▸ (u.isUnit.pow (r - 1)))
    obtain ⟨zu, rfl⟩ := hzu
    have hunits : (Units.map (algebraMap ℤ_[r] ℚ_[r] : ℤ_[r] →* ℚ_[r]) u) ^ (r - 1) =
        (Units.map (algebraMap ℤ_[r] ℚ_[r] : ℤ_[r] →* ℚ_[r]) zu) ^ q := by
      rw [← map_pow, ← map_pow]
      congr 1
      ext
      simp only [Units.val_pow_eq_pow_val]
      exact hz.symm
    have h2 := congrArg (fun y => Multiplicative.toAdd (f y)) hunits
    simp only [map_pow, toAdd_pow, nsmul_eq_mul] at h2
    rw [← hx] at h2
    exact ⟨Multiplicative.toAdd (f (Units.map (algebraMap ℤ_[r] ℚ_[r] : ℤ_[r] →* ℚ_[r]) zu)), h2⟩
  have h0 : ((r - 1 : ℕ) : ℤ) * x = 0 := int_eq_zero_of_forall_prime_dvd _ hdiv
  have hx0 : x = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exfalso; have : (1 : ℤ) ≤ ((r - 1 : ℕ) : ℤ) := by exact_mod_cast hr1
      omega
    · exact h
  rw [← ofAdd_toAdd (f (Units.map (algebraMap ℤ_[r] ℚ_[r] : ℤ_[r] →* ℚ_[r]) u)), ← hx, hx0]
  rfl

end Padicpart

end R4VH
p2m_reactivate "P2MW.S_CerednikDrinfeld_exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic.R4VH"

open R4VH in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)
    (ν : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ) :
    ∃ c : ℤ, ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r], ν g = (vdet g) ^ c := by

  let f : ℚ_[r]ˣ →* Multiplicative ℤ :=
    { toFun := fun d => ν (dGL d)
      map_one' := by simp [dGL_one]
      map_mul' := fun d d' => by simp [dGL_mul] }
  have hf : ∀ d, f d = ν (dGL d) := fun _ => rfl
  have hr0 : ((r : ℕ) : ℚ_[r]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero
  let rU : ℚ_[r]ˣ := Units.mk0 ((r : ℕ) : ℚ_[r]) hr0
  refine ⟨Multiplicative.toAdd (f rU), fun g => ?_⟩

  have h2 : (2 : ℚ_[r]) ≠ 0 := two_ne_zero
  have h21 : (2 : ℚ_[r]) ≠ 1 := by norm_num
  rw [apply_eq_apply_dGL_det ν 2 h2 h21 g, ← hf]

  set n : ℤ := Multiplicative.toAdd (vdet g) with hn
  obtain ⟨u, hu⟩ := (hvdet g n).mp (by rw [hn, ofAdd_toAdd])
  have hdet : Matrix.GeneralLinearGroup.det g = Units.map (algebraMap ℤ_[r] ℚ_[r] : ℤ_[r] →* ℚ_[r]) u * rU ^ n := by
    ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
    simpa [rU] using hu
  rw [hdet, map_mul, apply_unitsMap_eq_one, one_mul, map_zpow, ← ofAdd_toAdd (f rU), ← ofAdd_zsmul,
    ← ofAdd_toAdd (vdet g), ← ofAdd_zsmul, ← hn, smul_eq_mul, smul_eq_mul, mul_comm]
  simp

end S_CerednikDrinfeld_exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic
end P2MW
export P2MW.S_CerednikDrinfeld_exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic (solution)
