-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/81fb9e1a-11f8-53d5-8584-d0a4a6344ecf

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia

set_option autoImplicit false

open Quaternion CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve

theorem solution
    {r : ℕ} [Fact r.Prime] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {k₀ : Type} [CommRing k₀]
    (A₀ : FakeEllipticCurve Λ N k₀) (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)
    (X₀ : FormalODModule r k₀) (θ₀ : RelativeGroupLaw.FormalCoordinates A₀.f 2) (hA₀ : A₀.IsFormalModuleVia coord X₀ θ₀)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (hn : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (B' : Type) [CommRing B'] [Algebra k₀ B'] (J : Ideal B') (m : ℕ) (hJ : J ^ (m + 1) = ⊥)
    (s : Fin 2 → B') (hs : ∀ i, s i ∈ J) :
    θ₀ B' (fun i => MvFormalGroup.nilEval m (((n : MvFormalGroup.End X₀.F)).toPowerSeries i) s) =
      mapPt (A₀.act ⟨((n : ℕ) : ℚ), hn⟩) (A₀.act_over _) (θ₀ B' s) := by
  classical

  have hmem : (⟨((n : ℕ) : ℚ), hn⟩ : ↥Λ) = n • (⟨1, h1⟩ : ↥Λ) := by
    apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, nsmul_eq_mul, mul_one]
    exact QuaternionAlgebra.coe_natCast n
  have hco : coord ⟨((n : ℕ) : ℚ), hn⟩ = ((n : Zp2 r), 0) := by
    let φ : ↥Λ →+ Zp2 r × Zp2 r := AddMonoidHom.mk' coord hcoord.map_add
    have : coord ⟨((n : ℕ) : ℚ), hn⟩ = φ (n • ⟨1, h1⟩) := by rw [← hmem]; rfl
    rw [this, map_nsmul, show φ ⟨1, h1⟩ = (1, 0) from hcoord.map_one h1, Prod.smul_mk, smul_zero, nsmul_eq_mul, mul_one]

  have key := hA₀.2 B' J m hJ ⟨((n : ℕ) : ℚ), hn⟩ s hs
  rw [hco] at key
  dsimp only at key

  have hser : Series.addVia X₀.F (X₀.act (n : Zp2 r)) ((X₀.act 0).comp X₀.varpi) =
      ((n : MvFormalGroup.End X₀.F)).toPowerSeries := by
    have h0 : X₀.act 0 = fun _ => 0 := by
      rw [← FormalODModule.actEnd_toPowerSeries, ← FormalODModule.actRingHom_apply, map_zero]
      rfl
    have hc : (X₀.act 0).comp X₀.varpi = fun _ => 0 := by
      funext i
      simp only [Series.comp, h0]
      rw [← MvPolynomial.coe_zero, MvPowerSeries.subst_coe, map_zero, MvPolynomial.coe_zero]
    rw [hc, show (fun _ => (0 : MvPowerSeries (Fin 2) k₀)) = (0 : MvFormalGroup.End X₀.F).toPowerSeries from rfl,
      ← FormalODModule.actEnd_toPowerSeries,
      show Series.addVia X₀.F (X₀.actEnd (n : Zp2 r)).toPowerSeries (0 : MvFormalGroup.End X₀.F).toPowerSeries =
        (X₀.actEnd (n : Zp2 r) + 0).toPowerSeries from rfl,
      add_zero, ← FormalODModule.actRingHom_apply, map_natCast]
  rw [hser] at key
  exact key

end S_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_apply_nilEval_natCast_eq_mapPt_act_of_isFormalModuleVia (solution)
