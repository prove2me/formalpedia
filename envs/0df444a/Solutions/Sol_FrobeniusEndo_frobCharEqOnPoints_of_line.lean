-- Prove2me | solution 1 for FrobeniusEndo.frobCharEqOnPoints_of_line
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/48336ca9-ef16-589b-9c75-53d99dcf49c0

import Theorems.Thm_FrobeniusEndo_exists_prime_gt_and_quadratic_root
import Theorems.Thm_FrobeniusEndo_charEq_on_torsionBy_of_line_of_isotropic
import Theorems.Thm_FrobeniusEndo_frobCharEqOnPoints_of_charEq_on_torsion_of_trace_ne_zero
import Theorems.Thm_FrobeniusEndo_frobCharEqOnPoints_of_charEq_on_torsion_of_trace_zero
import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Algebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_frobCharEqOnPoints_of_line
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo

theorem solution {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k]
    [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k)
    (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (a : ℤ)
    (hline : ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 →
      ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + Fintype.card F)
    (hpos : ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0)
    (hcount : ∀ r : ℕ, r.Prime → (r : k) ≠ 0 → Nat.card (Submodule.torsionBy ℤ (W⁄k).Point r) = r ^ 2) :
    FrobCharEqOnPoints W σ a (Fintype.card F) := by
  set q : ℕ := Fintype.card F with hq
  have hq1 : 1 ≤ q := Fintype.card_pos_iff.mpr ⟨1⟩

  have hinv : ∀ r : ℕ, r.Prime → q < r → (r : k) ≠ 0 := by
    intro r hr hqr h0
    have h0F : (r : F) = 0 := by
      apply (algebraMap F k).injective
      rw [map_natCast, _root_.map_zero]
      exact h0
    have hdvd_r : ringChar F ∣ r := (ringChar.spec F r).mp h0F
    have hdvd_q : ringChar F ∣ q := (ringChar.spec F q).mp (FiniteField.cast_card_eq_zero F)
    have hne1 : ringChar F ≠ 1 := CharP.ringChar_ne_one
    rcases (Nat.dvd_prime hr).mp hdvd_r with h1 | h2
    · exact hne1 h1
    · have hle : ringChar F ≤ q := Nat.le_of_dvd hq1 hdvd_q
      omega

  have hkill : ∀ N : ℕ, ∃ r : ℕ, N < r ∧ r.Prime ∧ Nat.card (Submodule.torsionBy ℤ (W⁄k).Point r) = r ^ 2 ∧
      ∀ P : (W⁄k).Point, (r : ℤ) • P = 0 → σ • (σ • P) - a • (σ • P) + (q : ℤ) • P = 0 := by
    intro N
    obtain ⟨r, hNr, hr, c, hc⟩ :=
      FrobeniusEndo.exists_prime_gt_and_quadratic_root a (q : ℤ) (by exact_mod_cast hq1) (max N q)
    have hN : N < r := lt_of_le_of_lt (le_max_left N q) hNr
    have hqr : q < r := lt_of_le_of_lt (le_max_right N q) hNr
    have hrk : (r : k) ≠ 0 := hinv r hr hqr
    have hfull : Nat.card (Submodule.torsionBy ℤ (W⁄k).Point r) = r ^ 2 := hcount r hr hrk
    haveI : Fact r.Prime := ⟨hr⟩
    have hiso : ∃ c : ZMod r, c ^ 2 - (a : ZMod r) * c + (q : ZMod r) = 0 := ⟨c, by exact_mod_cast hc⟩
    refine ⟨r, hN, hr, hfull, fun P hP => ?_⟩
    exact FrobeniusEndo.charEq_on_torsionBy_of_line_of_isotropic W σ r hfull hrk a q
      (fun m hm _ hmk => hline m hm hmk) (fun m hm _ hmk => hpos m hm hmk) hiso P hP

  rcases eq_or_ne a 0 with rfl | ha
  · apply FrobeniusEndo.frobCharEqOnPoints_of_charEq_on_torsion_of_trace_zero W σ hσ
    intro N
    obtain ⟨r, hN, hr, hfull, hk⟩ := hkill N
    refine ⟨r, hN, hr, hfull, fun P hP => ?_⟩
    have := hk P hP
    rwa [zero_smul, sub_zero] at this
  · exact FrobeniusEndo.frobCharEqOnPoints_of_charEq_on_torsion_of_trace_ne_zero W σ hσ ha hkill

end S_FrobeniusEndo_frobCharEqOnPoints_of_line
end P2MW
export P2MW.S_FrobeniusEndo_frobCharEqOnPoints_of_line (solution)
