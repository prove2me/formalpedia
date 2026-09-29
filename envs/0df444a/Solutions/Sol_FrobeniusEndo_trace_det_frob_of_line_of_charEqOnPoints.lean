-- Prove2me | solution 1 for FrobeniusEndo.trace_det_frob_of_line_of_charEqOnPoints
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/30a2ddc7-3955-5bbe-8f04-ca1ec8be9b32

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Mathlib.LinearAlgebra.Determinant
import Theorems.Thm_FrobeniusEndo_trace_det_frob_of_line_of_isotropic
import Theorems.Thm_FrobeniusEndo_trace_det_frob_of_charEq_of_anisotropic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_trace_det_frob_of_line_of_charEqOnPoints

p2m_open "WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo P2MW.S_FrobeniusEndo_trace_det_frob_of_line_of_charEqOnPoints.FrobeniusEndo"

namespace FrobeniusEndo
p2m_export "FrobeniusEndo" "kerDeg frobEnd FrobCharEqOnPoints trace_det_frob_of_line_of_isotropic trace_det_frob_of_charEq_of_anisotropic"
p2m_open "FrobeniusEndo"

section Pencil

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ)

lemma coe_galois_smul_torsionBy (x : Submodule.torsionBy ℤ (W⁄K).Point p) :
    ((σ • x : Submodule.torsionBy ℤ (W⁄K).Point p) : (W⁄K).Point) = σ • (x : (W⁄K).Point) :=
  rfl

end Pencil

section Endgame

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime]

theorem trace_det_of_line_of_charEq
    (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (hpK : (p : K) ≠ 0) {a : ℤ} {q : ℕ}
    (hline : ∀ m : ℕ, 1 ≤ m → (m : K) ≠ 0 →
      ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q)
    (hpos : ∀ m : ℕ, 1 ≤ m → (m : K) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0)
    (hCE : galoisRepModuleEnd S W p σ * galoisRepModuleEnd S W p σ
        - (a : ZMod p) • galoisRepModuleEnd S W p σ
        + (q : ZMod p) •
            (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p)) = 0) :
    galoisTrace S W p σ = (a : ZMod p) ∧
      LinearMap.det (galoisRepModuleEnd S W p σ) = (q : ZMod p) := by
  by_cases hiso : ∃ c : ZMod p, c ^ 2 - (a : ZMod p) * c + (q : ZMod p) = 0
  · exact trace_det_frob_of_line_of_isotropic W σ p hfull hpK a q
      (fun m hm1 _ hmk => hline m hm1 hmk) (fun m hm1 _ hmk => hpos m hm1 hmk) hiso
  · exact trace_det_frob_of_charEq_of_anisotropic W σ p hfull a q hCE hiso

theorem charEq_of_forall_torsion {a : ℤ} {q : ℕ}
    (hpt : ∀ x : Submodule.torsionBy ℤ (W⁄K).Point p,
      σ • (σ • (x : (W⁄K).Point)) - a • (σ • (x : (W⁄K).Point)) + (q : ℤ) • (x : (W⁄K).Point) = 0) :
    galoisRepModuleEnd S W p σ * galoisRepModuleEnd S W p σ
        - (a : ZMod p) • galoisRepModuleEnd S W p σ
        + (q : ZMod p) • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄K).Point p)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply, Module.End.one_apply, LinearMap.zero_apply]

  rw [show ((q : ZMod p)) = (((q : ℤ) : ZMod p)) by push_cast; ring]
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  simpa only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul_of_tower,
    galoisRepModuleEnd_apply, coe_galois_smul_torsionBy, ZeroMemClass.coe_zero] using hpt x

theorem trace_det_of_line_of_charEqOnPoints
    (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (hpK : (p : K) ≠ 0) {a : ℤ} {q : ℕ}
    (hline : ∀ m : ℕ, 1 ≤ m → (m : K) ≠ 0 →
      ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q)
    (hpos : ∀ m : ℕ, 1 ≤ m → (m : K) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0)
    (hpt : FrobCharEqOnPoints W σ a q) :
    galoisTrace S W p σ = (a : ZMod p) ∧
      LinearMap.det (galoisRepModuleEnd S W p σ) = (q : ZMod p) :=
  trace_det_of_line_of_charEq W σ p hfull hpK hline hpos
    (charEq_of_forall_torsion W σ p fun x => hpt x.1)

end Endgame

end FrobeniusEndo

theorem solution {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] (hfull : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point p) = p ^ 2) (hpK : (p : K) ≠ 0) (a : ℤ) (q : ℕ) (hline : ∀ m : ℕ, 1 ≤ m → (m : K) ≠ 0 → ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - a * m + q) (hpos : ∀ m : ℕ, 1 ≤ m → (m : K) ≠ 0 → kerDeg (frobEnd W σ) m 1 ≠ 0) (hpt : FrobCharEqOnPoints W σ a q) : galoisTrace S W p σ = (a : ZMod p) ∧ LinearMap.det (galoisRepModuleEnd S W p σ) = (q : ZMod p) :=
  FrobeniusEndo.trace_det_of_line_of_charEqOnPoints W σ p hfull hpK hline hpos hpt

end S_FrobeniusEndo_trace_det_frob_of_line_of_charEqOnPoints
end P2MW
export P2MW.S_FrobeniusEndo_trace_det_frob_of_line_of_charEqOnPoints (solution)
