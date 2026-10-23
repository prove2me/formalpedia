-- Prove2me | solution 1 for CTB.covering_double
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T02:00:31.40439+00:00
-- url     : https://prove2.me/submissions/41818148-11ab-4045-9adf-997a65c66ae2

import Mathlib
import Definitions.Def_CTB_alg
import Definitions.Def_CTB_tor

open CTB


/-- A homomorphism out of `ZMod 3` given an element of order dividing 3. -/
def ctb84_pow3 {M : Type*} [Group M] (a : M) (ha : a ^ 3 = 1) : Multiplicative (ZMod 3) →* M where
  toFun g := a ^ (Multiplicative.toAdd g).val
  map_one' := by simp
  map_mul' x y := by
    show a ^ (Multiplicative.toAdd (x * y)).val = a ^ (Multiplicative.toAdd x).val * a ^ (Multiplicative.toAdd y).val
    rw [← pow_add, toAdd_mul, ZMod.val_add]
    exact (pow_eq_pow_mod _ ha).symm

/-- multiplication by `ω` on `ℤ[ω]^3 = ℤ^6`, blockwise `(x, y) ↦ (-y, x - y)` -/
def ctb84_rotF (v : Fin 6 → ℤ) : Fin 6 → ℤ := ![-v 1, v 0 - v 1, -v 3, v 2 - v 3, -v 5, v 4 - v 5]

theorem ctb84_rot3 (v : Fin 6 → ℤ) : ctb84_rotF (ctb84_rotF (ctb84_rotF v)) = v := by
  funext i; fin_cases i <;> simp [ctb84_rotF] <;> ring

theorem ctb84_rot_add (v w : Fin 6 → ℤ) : ctb84_rotF (v + w) = ctb84_rotF v + ctb84_rotF w := by
  funext i; fin_cases i <;> simp [ctb84_rotF] <;> ring

abbrev N6 := Multiplicative (Fin 6 → ℤ)

def ctb84_rho : MulAut N6 where
  toFun v := Multiplicative.ofAdd (ctb84_rotF (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd (ctb84_rotF (ctb84_rotF (Multiplicative.toAdd v)))
  left_inv v := by simp [ctb84_rot3]
  right_inv v := by simp [ctb84_rot3]
  map_mul' v w := by simp [ctb84_rot_add]

theorem ctb84_rho3 : ctb84_rho ^ 3 = 1 := by
  ext v; simp [pow_succ, ctb84_rho, ctb84_rot3]

abbrev C3 := Multiplicative (ZMod 3)

def ctb84_phi : C3 →* MulAut N6 := ctb84_pow3 ctb84_rho ctb84_rho3

abbrev QQ := N6 ⋊[ctb84_phi] C3

def ctb84_cyc : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem ctb84_cyc3 : ctb84_cyc ^ 3 = 1 := by decide

def ctb84_psi : C3 →* Equiv.Perm (Fin 4) := ctb84_pow3 ctb84_cyc ctb84_cyc3

theorem ctb84_psi_inj (g : C3) (h : ctb84_psi g = 1) : g = 1 := by
  have : ∀ x : ZMod 3, ctb84_cyc ^ x.val = 1 → x = 0 := by decide
  exact Multiplicative.toAdd.injective (this _ h)

def ctb84_hol : QQ →* Equiv.Perm (Fin 4) := ctb84_psi.comp SemidirectProduct.rightHom

theorem ctb84_ker (x : QQ) : x ∈ ctb84_hol.ker ↔ x.right = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h; exact ctb84_psi_inj _ h
  · intro h; simp [ctb84_hol, h]

theorem ctb84_eq_inl (x : QQ) (h : x.right = 1) : x = SemidirectProduct.inl x.left := by
  ext <;> simp [h]

def ctb84_kerEquiv : ↥ctb84_hol.ker ≃* N6 where
  toFun x := x.1.left
  invFun n := ⟨SemidirectProduct.inl n, (ctb84_ker _).2 rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact (ctb84_eq_inl x.1 ((ctb84_ker _).1 x.2)).symm
  right_inv n := rfl
  map_mul' x y := by
    have hx := (ctb84_ker _).1 x.2
    simp [SemidirectProduct.mul_left, hx]

theorem ctb84_N6_tf (n : N6) (j : ℕ) (h : n ^ 2 ^ j = 1) : n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  have := congrFun (congrArg Multiplicative.toAdd h) i
  simpa using this

def ctb84_wS : CrystallographicBraidWorld 4 QQ where
  lattice := ctb84_hol.ker
  latticeNormal := inferInstance
  latticeComm := by
    intro x hx y hy
    rw [ctb84_eq_inl x ((ctb84_ker _).1 hx), ctb84_eq_inl y ((ctb84_ker _).1 hy),
      ← map_mul, ← map_mul, mul_comm]
  latticeIso := ctb84_kerEquiv
  hol := ctb84_hol
  holKer := rfl
  noEvenTorsion := by
    rintro g ⟨j, hj⟩
    have hr : g.right ^ 2 ^ j = 1 := by
      have := congrArg SemidirectProduct.rightHom hj
      rw [map_pow, map_one] at this
      simpa using this
    have hr1 : g.right = 1 := by
      have h3 : ((2 : ZMod 3) ^ j) * Multiplicative.toAdd g.right = 0 := by
        have := congrArg Multiplicative.toAdd hr
        simpa [toAdd_pow, nsmul_eq_mul] using this
      have h2 : IsUnit ((2 : ZMod 3) ^ j) := (IsUnit.of_mul_eq_one (2 : ZMod 3) (by decide)).pow j
      exact Multiplicative.toAdd.injective (h2.mul_right_eq_zero.mp h3)
    rw [ctb84_eq_inl g hr1] at hj ⊢
    rw [← map_pow] at hj
    have := ctb84_N6_tf _ j (SemidirectProduct.inl_injective (hj.trans (map_one _).symm))
    rw [this, map_one]

/-- `x^2 = 1` in `ZMod 2`. -/
theorem ctb84_z2 : ∀ x : Multiplicative (ZMod 2), x * x = 1 := by decide

theorem ctb84_c3 : ∀ g : C3, g ^ 3 = 1 := by decide

theorem ctb84_chi_triv (chi : QQ →* Multiplicative (ZMod 2)) (x : QQ) : chi x = 1 := by
  -- on `C3`
  have hC : ∀ g : C3, chi (SemidirectProduct.inr g) = 1 := by
    intro g
    have h3 : g ^ 3 = 1 := ctb84_c3 g
    have : chi (SemidirectProduct.inr g) ^ 3 = 1 := by rw [← map_pow, ← map_pow, h3, map_one, map_one]
    rw [pow_succ, sq, ctb84_z2, one_mul] at this
    exact this
  -- invariance on `N6`
  have hinv : ∀ n : N6, chi (SemidirectProduct.inl (ctb84_rho n)) = chi (SemidirectProduct.inl n) := by
    intro n
    have : ctb84_rho n = ctb84_phi (Multiplicative.ofAdd 1) n := by
      show ctb84_rho n = (ctb84_rho ^ (1 : ZMod 3).val) n
      rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
    rw [this, SemidirectProduct.inl_aut, map_mul, map_mul, hC, hC, one_mul, mul_one]
  let e : Fin 6 → N6 := fun i => Multiplicative.ofAdd (Pi.single i 1)
  have hblock : ∀ b : Fin 3, chi (SemidirectProduct.inl (e ⟨2 * b, by omega⟩)) = 1 ∧
      chi (SemidirectProduct.inl (e ⟨2 * b + 1, by omega⟩)) = 1 := by
    intro b
    have h1 : ctb84_rho (e ⟨2 * b, by omega⟩) = e ⟨2 * b + 1, by omega⟩ := by
      apply Multiplicative.toAdd.injective
      fin_cases b <;> decide
    have h2 : ctb84_rho (e ⟨2 * b + 1, by omega⟩) = (e ⟨2 * b, by omega⟩)⁻¹ * (e ⟨2 * b + 1, by omega⟩)⁻¹ := by
      apply Multiplicative.toAdd.injective
      fin_cases b <;> decide
    have k1 := hinv (e ⟨2 * b, by omega⟩)
    have k2 := hinv (e ⟨2 * b + 1, by omega⟩)
    rw [h1] at k1
    rw [h2] at k2
    simp only [map_mul, map_inv] at k2
    rw [k1] at k2
    set a := chi (SemidirectProduct.inl (e ⟨2 * b, by omega⟩))
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (ctb84_z2 a)
    rw [hai, ctb84_z2] at k2
    exact ⟨k2.symm, k1.trans k2.symm⟩
  have hbasis : ∀ i : Fin 6, chi (SemidirectProduct.inl (e i)) = 1 := by
    intro i
    fin_cases i
    · exact (hblock 0).1
    · exact (hblock 0).2
    · exact (hblock 1).1
    · exact (hblock 1).2
    · exact (hblock 2).1
    · exact (hblock 2).2
  have hN : ∀ n : N6, chi (SemidirectProduct.inl n) = 1 := by
    intro n
    let f : (Fin 6 → ℤ) →+ Additive (Multiplicative (ZMod 2)) :=
      MonoidHom.toAdditive ((chi.comp SemidirectProduct.inl))
    have hf : ∀ v, f v = 0 := by
      intro v
      rw [pi_eq_sum_univ v, map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_zsmul]
      have : f (fun j => if i = j then 1 else 0) = 0 := by
        have : (fun j : Fin 6 => if i = j then (1 : ℤ) else 0) = Pi.single i 1 := by
          funext j; simp [Pi.single_apply, eq_comm]
        rw [this]
        exact hbasis i
      rw [this, smul_zero]
    exact hf (Multiplicative.toAdd n)
  rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, hN, hC, mul_one]

theorem solution : ¬ (∀ {n : ℕ} {Q : Type} [Group Q]
    (W : CrystallographicBraidWorld n Q) (hn : 4 ≤ n),
    (∃ (T1 T2 : Subgroup Q) (chi : Q →* Multiplicative (ZMod 2)),
        T1 ≤ T2 ∧
        (∀ g ∈ T2, ∀ k ∈ T1, g * k * g⁻¹ ∈ T1) ∧
        (∀ x ∈ T2, chi x = 1 ↔ x ∈ T1) ∧
        (∀ y : Multiplicative (ZMod 2), ∃ x ∈ T2, chi x = y)) ∧
    (∃ (T3 T4 : Subgroup Q) (chis : Fin 3 → (Q →* Multiplicative (ZMod 2))),
        T3 ≤ T4 ∧
        (∀ g ∈ T4, ∀ k ∈ T3, g * k * g⁻¹ ∈ T3) ∧
        (∀ x ∈ T4, (∀ j, chis j x = 1) ↔ x ∈ T3) ∧
        (∀ ys : Fin 3 → Multiplicative (ZMod 2), ∃ x ∈ T4, ∀ j, chis j x = ys j))) :=
  by
  intro h
  obtain ⟨⟨T1, T2, chi, -, -, -, hs⟩, -⟩ := h ctb84_wS le_rfl
  obtain ⟨x, -, hx⟩ := hs (Multiplicative.ofAdd 1)
  rw [ctb84_chi_triv] at hx
  revert hx; decide
