-- Prove2me | solution 1 for CerednikDrinfeld.Omega.theta_pmoebius_mul_theta_eq_theta
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/79256a7e-2272-56c6-8956-4f999288a34d

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_mul_theta_eq_theta

set_option autoImplicit false

open scoped MatrixGroups
p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_mul_theta_eq_theta.CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "moebius pmoebius pmoebius_mk upperHalfPlane moebius_denom_ne_zero_of_mem pmoebius_mem_upperHalfPlane pmoebius_one pmoebius_mul crossRatio thetaFactor theta ThetaMultipliable"
namespace ThetaDictProof
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K]

theorem moebius_sub_moebius (g : GL (Fin 2) K₀) {u v : K}
    (hu : algebraMap K₀ K (g 1 0) * u + algebraMap K₀ K (g 1 1) ≠ 0)
    (hv : algebraMap K₀ K (g 1 0) * v + algebraMap K₀ K (g 1 1) ≠ 0) :
    moebius K₀ K g u - moebius K₀ K g v =
      algebraMap K₀ K (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (u - v) /
        ((algebraMap K₀ K (g 1 0) * u + algebraMap K₀ K (g 1 1)) *
          (algebraMap K₀ K (g 1 0) * v + algebraMap K₀ K (g 1 1))) := by
  unfold moebius
  rw [div_sub_div _ _ hu hv, map_sub, map_mul, map_mul]
  congr 1
  ring

theorem algebraMap_det_ne_zero (g : GL (Fin 2) K₀) :
    algebraMap K₀ K (g 0 0 * g 1 1 - g 0 1 * g 1 0) ≠ 0 := by
  intro h
  apply g.det_ne_zero
  rw [Matrix.det_fin_two]
  exact (algebraMap K₀ K).injective (by rw [map_zero]; exact h)

theorem crossRatio_moebius (g : GL (Fin 2) K₀) {z w x y : K}
    (hz : z ∈ upperHalfPlane K₀ K) (hw : w ∈ upperHalfPlane K₀ K)
    (hx : x ∈ upperHalfPlane K₀ K) (hy : y ∈ upperHalfPlane K₀ K) :
    crossRatio (moebius K₀ K g z) (moebius K₀ K g w) (moebius K₀ K g x) (moebius K₀ K g y) =
      crossRatio z w x y := by
  have hDz := moebius_denom_ne_zero_of_mem K₀ hz g
  have hDw := moebius_denom_ne_zero_of_mem K₀ hw g
  have hDx := moebius_denom_ne_zero_of_mem K₀ hx g
  have hDy := moebius_denom_ne_zero_of_mem K₀ hy g
  have hδ := algebraMap_det_ne_zero (K := K) g
  unfold crossRatio
  rw [moebius_sub_moebius g hDz hDx, moebius_sub_moebius g hDw hDy, moebius_sub_moebius g hDz hDy,
    moebius_sub_moebius g hDw hDx, div_mul_div_comm, div_mul_div_comm, div_div_div_comm]
  have hden :
      (algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1)) *
            (algebraMap K₀ K (g 1 0) * x + algebraMap K₀ K (g 1 1)) *
          ((algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1)) *
            (algebraMap K₀ K (g 1 0) * y + algebraMap K₀ K (g 1 1))) /
        ((algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1)) *
            (algebraMap K₀ K (g 1 0) * y + algebraMap K₀ K (g 1 1)) *
          ((algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1)) *
            (algebraMap K₀ K (g 1 0) * x + algebraMap K₀ K (g 1 1)))) = 1 := by
    rw [div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero hDz hDy) (mul_ne_zero hDw hDx))]
    ring
  have hnum :
      algebraMap K₀ K (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (z - x) *
          (algebraMap K₀ K (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (w - y)) =
        algebraMap K₀ K (g 0 0 * g 1 1 - g 0 1 * g 1 0) ^ 2 * ((z - x) * (w - y)) := by
    ring
  have hnum' :
      algebraMap K₀ K (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (z - y) *
          (algebraMap K₀ K (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (w - x)) =
        algebraMap K₀ K (g 0 0 * g 1 1 - g 0 1 * g 1 0) ^ 2 * ((z - y) * (w - x)) := by
    ring
  rw [hden, div_one, hnum, hnum', mul_div_mul_left _ _ (pow_ne_zero 2 hδ)]

variable [DecidableEq K]

theorem crossRatio_pmoebius (g : PGL(2, K₀)) {z w x y : K}
    (hz : z ∈ upperHalfPlane K₀ K) (hw : w ∈ upperHalfPlane K₀ K)
    (hx : x ∈ upperHalfPlane K₀ K) (hy : y ∈ upperHalfPlane K₀ K) :
    crossRatio (pmoebius K₀ g z) (pmoebius K₀ g w) (pmoebius K₀ g x) (pmoebius K₀ g y) =
      crossRatio z w x y := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
    rw [pmoebius_mk K₀ g z (moebius_denom_ne_zero_of_mem K₀ hz g),
      pmoebius_mk K₀ g w (moebius_denom_ne_zero_of_mem K₀ hw g),
      pmoebius_mk K₀ g x (moebius_denom_ne_zero_of_mem K₀ hx g),
      pmoebius_mk K₀ g y (moebius_denom_ne_zero_of_mem K₀ hy g)]
    exact crossRatio_moebius g hz hw hx hy

theorem crossRatio_mul_crossRatio {p q a b w : K}
    (hpa : p ≠ a) (hpb : p ≠ b) (hqa : q ≠ a) (hqb : q ≠ b) (hwp : w ≠ p) (hwq : w ≠ q) :
    crossRatio p q a b * crossRatio a w q p = crossRatio b w q p := by
  unfold crossRatio
  have h1 : p - a ≠ 0 := sub_ne_zero.2 hpa
  have h2 : p - b ≠ 0 := sub_ne_zero.2 hpb
  have h3 : q - a ≠ 0 := sub_ne_zero.2 hqa
  have h4 : q - b ≠ 0 := sub_ne_zero.2 hqb
  have h5 : a - p ≠ 0 := sub_ne_zero.2 hpa.symm
  have h6 : b - p ≠ 0 := sub_ne_zero.2 hpb.symm
  have h7 : a - q ≠ 0 := sub_ne_zero.2 hqa.symm
  have h8 : b - q ≠ 0 := sub_ne_zero.2 hqb.symm
  have h9 : w - p ≠ 0 := sub_ne_zero.2 hwp
  have h10 : w - q ≠ 0 := sub_ne_zero.2 hwq
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero (mul_ne_zero h2 h3) (mul_ne_zero h5 h10)) (mul_ne_zero h6 h10)]
  ring

variable {G : Type*} [Group G]

theorem thetaFactor_mul (ρ : G →* PGL(2, K₀)) {a b z₀ w : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hwz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ w) (β γ : G) :
    thetaFactor ρ a b z₀ (pmoebius K₀ (ρ β) z₀) γ * thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w a γ⁻¹ =
      thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w b γ⁻¹ := by

  have hβz₀ : pmoebius K₀ (ρ β) z₀ ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hz₀ (ρ β)
  have hγa : pmoebius K₀ (ρ γ) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha (ρ γ)
  have hγb : pmoebius K₀ (ρ γ) b ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ hb (ρ γ)

  have hinv : thetaFactor ρ a b z₀ (pmoebius K₀ (ρ β) z₀) γ =
      crossRatio (pmoebius K₀ (ρ (γ⁻¹ * β)) z₀) (pmoebius K₀ (ρ γ⁻¹) z₀) a b := by
    unfold thetaFactor
    rw [← crossRatio_pmoebius (ρ γ⁻¹) hβz₀ hz₀ hγa hγb]
    rw [← pmoebius_mul K₀ hz₀, ← map_mul, ← pmoebius_mul K₀ ha, ← map_mul, ← pmoebius_mul K₀ hb, ← map_mul,
      inv_mul_cancel, map_one, pmoebius_one, pmoebius_one]
  have hsnd : ∀ x : K, thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w x γ⁻¹ =
      crossRatio x w (pmoebius K₀ (ρ γ⁻¹) z₀) (pmoebius K₀ (ρ (γ⁻¹ * β)) z₀) := fun x => by
    unfold thetaFactor
    rw [map_mul, pmoebius_mul K₀ hz₀]
  rw [hinv, hsnd a, hsnd b]

  set p := pmoebius K₀ (ρ (γ⁻¹ * β)) z₀ with hp
  set q := pmoebius K₀ (ρ γ⁻¹) z₀ with hq
  have key : ∀ (δ : G) (x : K), (∀ γ : G, pmoebius K₀ (ρ γ) x ≠ z₀) → pmoebius K₀ (ρ δ) z₀ ≠ x := by
    intro δ x hx h
    apply hx δ⁻¹
    have hx' : x ∈ upperHalfPlane K₀ K := by rw [← h]; exact pmoebius_mem_upperHalfPlane K₀ hz₀ (ρ δ)
    rw [← h, ← pmoebius_mul K₀ hz₀, ← map_mul, inv_mul_cancel, map_one, pmoebius_one]
  have hpa : p ≠ a := key _ a hz₀a
  have hpb : p ≠ b := key _ b hz₀b
  have hqa : q ≠ a := key _ a hz₀a
  have hqb : q ≠ b := key _ b hz₀b
  have hwp : w ≠ p := fun h => hwz₀ _ h.symm
  have hwq : w ≠ q := fun h => hwz₀ _ h.symm
  exact crossRatio_mul_crossRatio hpa hpb hqa hqb hwp hwq

theorem theta_mul [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (ρ : G →* PGL(2, K₀)) {a b z₀ w : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hw : w ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hwz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ w) (β : G)
    (h₁ : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β) z₀))
    (h₂ : ThetaMultipliable ρ z₀ (pmoebius K₀ (ρ β) z₀) w a) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) * theta ρ z₀ (pmoebius K₀ (ρ β) z₀) w a =
      theta ρ z₀ (pmoebius K₀ (ρ β) z₀) w b := by

  have reindex : ∀ x : K, (∏' γ : G, thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w x γ⁻¹) =
      theta ρ z₀ (pmoebius K₀ (ρ β) z₀) w x := fun x => by
    unfold theta
    have h := Equiv.tprod_eq (Equiv.inv G) (thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w x)
    simpa only [Equiv.inv_apply] using h
  have h₁' : Multipliable (thetaFactor ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) := h₁
  have h₂m : Multipliable (thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w a) := h₂
  have h₂' : Multipliable fun γ : G => thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w a γ⁻¹ := by
    have h := (Equiv.multipliable_iff (Equiv.inv G) (f := thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w a)).2 h₂m
    simpa only [Function.comp_def, Equiv.inv_apply] using h
  have hprod : HasProd ((thetaFactor ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) *
      fun γ : G => thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w a γ⁻¹)
      ((∏' γ : G, thetaFactor ρ a b z₀ (pmoebius K₀ (ρ β) z₀) γ) *
        ∏' γ : G, thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w a γ⁻¹) :=
    HasProd.mul h₁'.hasProd h₂'.hasProd
  have hfun : ((thetaFactor ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) *
      fun γ : G => thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w a γ⁻¹) =
      fun γ : G => thetaFactor ρ z₀ (pmoebius K₀ (ρ β) z₀) w b γ⁻¹ :=
    funext fun γ => by
      rw [Pi.mul_apply]
      exact thetaFactor_mul ρ ha hb hz₀ hz₀a hz₀b hwz₀ β γ
  rw [hfun] at hprod
  rw [← reindex a, ← reindex b]
  unfold theta
  exact hprod.tprod_eq.symm

end CerednikDrinfeld.Omega.ThetaDictProof

theorem solution
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ w : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hw : w ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hwz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ w) (β : G)
    (h₁ : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β) z₀))
    (h₂ : ThetaMultipliable ρ z₀ (pmoebius K₀ (ρ β) z₀) w a) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) * theta ρ z₀ (pmoebius K₀ (ρ β) z₀) w a =
      theta ρ z₀ (pmoebius K₀ (ρ β) z₀) w b :=
  CerednikDrinfeld.Omega.ThetaDictProof.theta_mul ρ ha hb hz₀ hw hz₀a hz₀b hwz₀ β h₁ h₂

end S_CerednikDrinfeld_Omega_theta_pmoebius_mul_theta_eq_theta
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_theta_pmoebius_mul_theta_eq_theta (solution)
