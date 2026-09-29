-- Prove2me | solution 1 for FrobeniusEndo.trace_det_frob_of_line_of_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e469c10b-1167-5e95-bdbe-b2af883f3f43

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Finiteness
import Theorems.Thm_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero
import Theorems.Thm_FrobeniusEndo_det_frobPencilEnd_eq_zero_iff_dvd_kerDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_trace_det_frob_of_line_of_isotropic

p2m_open "WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo P2MW.S_FrobeniusEndo_trace_det_frob_of_line_of_isotropic.FrobeniusEndo"

namespace FrobeniusEndo
p2m_export "FrobeniusEndo" "linePencil linePencil_apply kerDeg frobEnd frobEnd_apply frobPencilEnd dvd_kerDeg_of_det_frobPencilEnd_eq_zero det_frobPencilEnd_eq_zero_iff_dvd_kerDeg"
p2m_open "FrobeniusEndo"

section BivariateDet

variable {R : Type*} [CommRing R]

theorem matrix_det_smul_one_sub_smul_fin_two (a c : R) (M : Matrix (Fin 2) (Fin 2) R) :
    (a • (1 : Matrix (Fin 2) (Fin 2) R) - c • M).det
      = a ^ 2 - a * c * M.trace + c ^ 2 * M.det := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_zero, mul_one]
  ring

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem linearMap_det_smul_one_sub_smul_of_basis_fin_two (b : Module.Basis (Fin 2) R M)
    (φ : M →ₗ[R] M) (a c : R) :
    LinearMap.det (a • (1 : M →ₗ[R] M) - c • φ)
      = a ^ 2 - a * c * LinearMap.trace R M φ + c ^ 2 * LinearMap.det φ := by
  rw [LinearMap.trace_eq_matrix_trace R b φ, ← LinearMap.det_toMatrix b φ,
    ← LinearMap.det_toMatrix b (a • (1 : M →ₗ[R] M) - c • φ), map_sub, map_smul, map_smul,
    LinearMap.toMatrix_one]
  exact matrix_det_smul_one_sub_smul_fin_two a c _

end BivariateDet

section RankTwo

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem finrank_eq_two_of_natCard (hV : Nat.card V = p ^ 2) : Module.finrank (ZMod p) V = 2 := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
  rw [hV, Nat.card_zmod] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm

noncomputable def basisOfNatCard (hV : Nat.card V = p ^ 2) : Module.Basis (Fin 2) (ZMod p) V :=
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero)
  Module.finBasisOfFinrankEq (ZMod p) V (finrank_eq_two_of_natCard hV)

end RankTwo

section Pencil

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ)

lemma coe_galois_smul_torsionBy (x : Submodule.torsionBy ℤ (W⁄K).Point p) :
    ((σ • x : Submodule.torsionBy ℤ (W⁄K).Point p) : (W⁄K).Point) = σ • (x : (W⁄K).Point) :=
  rfl

lemma coe_frobPencilEnd_apply (m n : ℤ) (x : Submodule.torsionBy ℤ (W⁄K).Point p) :
    ((frobPencilEnd W σ p m n x : Submodule.torsionBy ℤ (W⁄K).Point p) : (W⁄K).Point)
      = linePencil (frobEnd W σ) m n x := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, linePencil_apply,
    frobEnd_apply, Int.cast_smul_eq_zsmul, Submodule.coe_sub, Submodule.coe_smul_of_tower]
  rfl

lemma frobPencilEnd_eq_zero_iff (m n : ℤ) (x : Submodule.torsionBy ℤ (W⁄K).Point p) :
    frobPencilEnd W σ p m n x = 0 ↔ (x : (W⁄K).Point) ∈ (linePencil (frobEnd W σ) m n).ker := by
  rw [AddMonoidHom.mem_ker, ← coe_frobPencilEnd_apply, ZeroMemClass.coe_eq_zero]

lemma frobPencilEnd_natCast_one (m : ℕ) :
    frobPencilEnd W σ p (m : ℤ) 1
      = (m : ZMod p) • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p))
          - galoisRepModuleEnd S W p σ := by
  simp only [frobPencilEnd, Int.cast_natCast, Int.cast_one, one_smul]

end Pencil

section Dictionary

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime]

variable {p} in

lemma exists_pos_natCast_lift (hpK : (p : K) ≠ 0) (c : ZMod p) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 2 * p ∧ (m : K) ≠ 0 ∧ (m : ZMod p) = c := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hvlt : c.val < p := ZMod.val_lt c
  have hvcast : ((c.val : ℕ) : ZMod p) = c := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  by_cases hc0 : c = 0
  ·
    exact ⟨p, hp1, by omega, hpK, by rw [ZMod.natCast_self, hc0]⟩
  ·
    have hv1 : 1 ≤ c.val := by
      rcases Nat.eq_zero_or_pos c.val with h | h
      · exact absurd (by rw [← hvcast, h, Nat.cast_zero]) hc0
      · exact h
    by_cases hvk : ((c.val : ℕ) : K) = 0
    · refine ⟨c.val + p, by omega, by omega, ?_, by
        rw [Nat.cast_add, ZMod.natCast_self, add_zero, hvcast]⟩
      intro h0
      apply hpK
      have hsub : ((c.val + p : ℕ) : K) - ((c.val : ℕ) : K) = (p : K) := by
        push_cast; ring
      rw [h0, hvk, sub_zero] at hsub
      exact hsub.symm
    · exact ⟨c.val, hv1, by omega, hvk, hvcast⟩

theorem quadratic_eq_zero_of_det_smul_one_sub_eq_zero (hpK : (p : K) ≠ 0) {a : ℤ} {q : ℕ}
    (hline : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 →
      ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q)
    {c : ZMod p}
    (hdet : LinearMap.det
        (c • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p))
          - galoisRepModuleEnd S W p σ) = 0) :
    c ^ 2 - (a : ZMod p) * c + (q : ZMod p) = 0 := by
  obtain ⟨m, hm1, hmle, hmk, hmc⟩ := exists_pos_natCast_lift (K := K) hpK c

  have hdet' : LinearMap.det (frobPencilEnd W σ p (m : ℤ) 1) = 0 := by
    rw [frobPencilEnd_natCast_one, hmc]
    exact hdet

  have hdvd : p ∣ kerDeg (frobEnd W σ) (m : ℤ) 1 := dvd_kerDeg_of_det_frobPencilEnd_eq_zero W σ p hdet'
  have hdvdZ : (p : ℤ) ∣ ((m : ℤ) ^ 2 - a * (m : ℤ) + (q : ℤ)) := by
    rw [← hline m hm1 hmle hmk]
    exact_mod_cast hdvd

  have hzero : (((m : ℤ) ^ 2 - a * (m : ℤ) + (q : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvdZ
  push_cast at hzero
  rwa [hmc] at hzero

theorem det_smul_one_sub_eq_zero_of_quadratic_eq_zero
    (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (hpK : (p : K) ≠ 0) {a : ℤ} {q : ℕ}
    (hline : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 →
      ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q)
    (hpos : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0)
    {c : ZMod p}
    (hroot : c ^ 2 - (a : ZMod p) * c + (q : ZMod p) = 0) :
    LinearMap.det
        (c • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p))
          - galoisRepModuleEnd S W p σ) = 0 := by
  obtain ⟨m, hm1, hmle, hmk, hmc⟩ := exists_pos_natCast_lift (K := K) hpK c

  have hzero : (((m : ℤ) ^ 2 - a * (m : ℤ) + (q : ℤ) : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hmc]
    exact hroot
  have hdvdZ : (p : ℤ) ∣ ((m : ℤ) ^ 2 - a * (m : ℤ) + (q : ℤ)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzero
  have hdvd : p ∣ kerDeg (frobEnd W σ) (m : ℤ) 1 := by
    have : (p : ℤ) ∣ (kerDeg (frobEnd W σ) (m : ℤ) 1 : ℤ) := by
      rw [hline m hm1 hmle hmk]
      exact hdvdZ
    exact_mod_cast this

  have hdet' : LinearMap.det (frobPencilEnd W σ p (m : ℤ) 1) = 0 :=
    (det_frobPencilEnd_eq_zero_iff_dvd_kerDeg W σ p
      (by rw [hfull]; exact pow_ne_zero 2 (Fact.out : p.Prime).ne_zero) (hpos m hm1 hmle hmk)).mpr hdvd
  rwa [frobPencilEnd_natCast_one, hmc] at hdet'

end Dictionary

section Endgame

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime]

theorem trace_det_of_line_of_isotropic
    (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (hpK : (p : K) ≠ 0) {a : ℤ} {q : ℕ}
    (hline : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 →
      ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q)
    (hpos : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0)
    (hiso : ∃ c : ZMod p, c ^ 2 - (a : ZMod p) * c + (q : ZMod p) = 0) :
    galoisTrace S W p σ = (a : ZMod p) ∧
      LinearMap.det (galoisRepModuleEnd S W p σ) = (q : ZMod p) := by
  classical
  let b : Module.Basis (Fin 2) (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p) :=
    basisOfNatCard hfull
  rw [galoisTrace_def]
  set M := galoisRepModuleEnd S W p σ with hM
  set t := LinearMap.trace (ZMod p) _ M with ht
  set d := LinearMap.det M with hd

  have hdf : ∀ c : ZMod p,
      LinearMap.det (c • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p)) - M)
        = c ^ 2 - c * t + d := by
    intro c
    have h := linearMap_det_smul_one_sub_smul_of_basis_fin_two b M c 1
    simpa using h

  obtain ⟨lam, hlam⟩ := hiso
  set mu : ZMod p := (a : ZMod p) - lam with hmu
  have hmuroot : mu ^ 2 - (a : ZMod p) * mu + (q : ZMod p) = 0 := by
    rw [hmu]; linear_combination hlam

  have hdl : LinearMap.det
      (lam • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p)) - M) = 0 :=
    det_smul_one_sub_eq_zero_of_quadratic_eq_zero W σ p hfull hpK hline hpos hlam
  have hdmu : LinearMap.det
      (mu • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p)) - M) = 0 :=
    det_smul_one_sub_eq_zero_of_quadratic_eq_zero W σ p hfull hpK hline hpos hmuroot
  have el : lam ^ 2 - lam * t + d = 0 := by rw [← hdf lam]; exact hdl
  have emu : mu ^ 2 - mu * t + d = 0 := by rw [← hdf mu]; exact hdmu

  have htr : t = (a : ZMod p) := by
    by_cases hlm : lam = mu
    ·
      have ha2 : (a : ZMod p) = 2 * lam := by
        have h := hlm
        rw [hmu] at h
        linear_combination -h
      have hq2 : (q : ZMod p) = lam ^ 2 := by
        linear_combination hlam + lam * ha2
      set nu : ZMod p := t - lam with hnu
      have hnuchar : nu ^ 2 - nu * t + d = 0 := by
        rw [hnu]; linear_combination el
      have hdnu : LinearMap.det
          (nu • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p)) - M) = 0 := by
        rw [hdf nu]; exact hnuchar
      have hnuq : nu ^ 2 - (a : ZMod p) * nu + (q : ZMod p) = 0 :=
        quadratic_eq_zero_of_det_smul_one_sub_eq_zero W σ p hpK hline hdnu
      have hsq : (nu - lam) ^ 2 = 0 := by
        linear_combination hnuq + nu * ha2 - hq2
      have hnulam : nu = lam := by
        have h0 : nu - lam = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq
        exact sub_eq_zero.mp h0
      have htval : t = nu + lam := by rw [hnu]; ring
      rw [htval, hnulam, ha2]; ring
    ·
      have hfac : (lam - mu) * (lam + mu - t) = 0 := by
        linear_combination el - emu
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (sub_eq_zero.mp h) hlm
      · have hsum : lam + mu = t := sub_eq_zero.mp h
        rw [← hsum, hmu]; ring

  have hdet : d = (q : ZMod p) := by
    linear_combination el - hlam + lam * htr
  exact ⟨htr, hdet⟩

end Endgame

end FrobeniusEndo

theorem solution {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (hpK : (p : K) ≠ 0) (a : ℤ) (q : ℕ) (hline : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 → ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q) (hpos : ∀ m : ℕ, 1 ≤ m → m ≤ 2 * p → (m : K) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0) (hiso : ∃ c : ZMod p, c ^ 2 - (a : ZMod p) * c + (q : ZMod p) = 0) : galoisTrace S W p σ = (a : ZMod p) ∧ LinearMap.det (galoisRepModuleEnd S W p σ) = (q : ZMod p) :=
  FrobeniusEndo.trace_det_of_line_of_isotropic W σ p hfull hpK hline hpos hiso

end S_FrobeniusEndo_trace_det_frob_of_line_of_isotropic
end P2MW
export P2MW.S_FrobeniusEndo_trace_det_frob_of_line_of_isotropic (solution)
