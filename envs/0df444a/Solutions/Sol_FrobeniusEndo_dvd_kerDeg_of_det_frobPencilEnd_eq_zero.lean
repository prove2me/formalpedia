-- Prove2me | solution 1 for FrobeniusEndo.dvd_kerDeg_of_det_frobPencilEnd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/75562eaa-8abf-56d0-87ab-e4cc32a05fb0

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero

p2m_open "WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo P2MW.S_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero.FrobeniusEndo"

namespace FrobeniusEndo
p2m_export "FrobeniusEndo" "linePencil linePencil_apply kerDeg kerDeg_def frobEnd frobEnd_apply frobPencilEnd"
p2m_open "FrobeniusEndo"

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

theorem dvd_kerDeg_of_det_eq_zero {m n : ℤ}
    (hdet : LinearMap.det (frobPencilEnd W σ p m n) = 0) :
    p ∣ kerDeg (frobEnd W σ) m n := by

  have hker : LinearMap.ker (frobPencilEnd W σ p m n) ≠ ⊥ :=
    bot_lt_iff_ne_bot.mp (LinearMap.bot_lt_ker_of_det_eq_zero hdet)
  obtain ⟨x, hxker, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker, frobPencilEnd_eq_zero_iff] at hxker

  have hx0' : (x : (W⁄K).Point) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  have hxp : p • (x : (W⁄K).Point) = 0 := by
    have hx_tors : ((p : ℤ)) • (x : (W⁄K).Point) = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    rwa [Nat.cast_smul_eq_nsmul] at hx_tors

  set y : (linePencil (frobEnd W σ) m n).ker := ⟨_, hxker⟩ with hy
  have hyp : p • y = 0 := Subtype.ext hxp
  have hy0 : y ≠ 0 := fun h0 => hx0' (congrArg Subtype.val h0)
  have hyord : addOrderOf y = p := by
    have h1 : addOrderOf y ∣ p := addOrderOf_dvd_of_nsmul_eq_zero hyp
    rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ h1) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hy0
    · exact h

  rw [kerDeg_def, ← hyord]
  exact addOrderOf_dvd_natCard y

end Dictionary

end FrobeniusEndo

theorem solution {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] {m n : ℤ} (h : LinearMap.det (frobPencilEnd W σ p m n) = 0) : p ∣ kerDeg (frobEnd W σ) m n :=
  FrobeniusEndo.dvd_kerDeg_of_det_eq_zero W σ p h

end S_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero
end P2MW
export P2MW.S_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero (solution)
