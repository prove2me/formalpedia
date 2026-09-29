-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/20e54c89-fb38-5d5b-9f14-0da8aef2352e

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace P2mWs44UR

variable {p : ℕ} [Fact p.Prime] {B S : Type} [CommRing B] [CommRing S]

noncomputable abbrev A (X : FormalODModule p B) (f : B →+* S) (a : Zp2 p) : Series S := (X.act a).map f

theorem A_const (X : FormalODModule p B) (f : B →+* S) (a : Zp2 p) (i : Fin 2) :
    MvPowerSeries.constantCoeff (A X f a i) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.map f (X.act a i)) = 0
  rw [MvPowerSeries.constantCoeff_map, (X.isLawHom_act a).1 i, map_zero]

theorem A_mul (X : FormalODModule p B) (f : B →+* S) (a b : Zp2 p) :
    A X f (a * b) = (A X f a).comp (A X f b) := by
  show (X.act (a * b)).map f = ((X.act a).map f).comp ((X.act b).map f)
  rw [X.act_mul, Series.map_comp f _ _ (X.isLawHom_act b).1]

theorem A_one (X : FormalODModule p B) (f : B →+* S) : A X f 1 = Series.id S := by
  show (X.act 1).map f = Series.id S
  rw [X.act_one, Series.map_id]

theorem A_natCast (X : FormalODModule p B) (f : B →+* S) (n : ℕ) :
    Series.map f (X.F.nthSeries n) = A X f (n : Zp2 p) := by
  show Series.map f (X.F.nthSeries n) = (X.act (n : Zp2 p)).map f
  rw [X.act_natCast]

theorem A_inv_comp (X : FormalODModule p B) (f : B →+* S) (w : (Zp2 p)ˣ) (φ : Series S)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    (A X f ((w⁻¹ : (Zp2 p)ˣ) : Zp2 p)).comp ((A X f (w : Zp2 p)).comp φ) = φ := by
  rw [← Series.comp_assoc _ _ _ (A_const X f _) hφ, ← A_mul, Units.inv_mul, A_one,
    Series.id_comp _ hφ]

end P2mWs44UR

open P2mWs44UR in
theorem solution
    {p : ℕ} [Fact p.Prime] {B R₀ S : Type} [CommRing B] [CommRing R₀] [CommRing S]
    (X : FormalODModule p B) (X₀ : FormalODModule p R₀) (f : B →+* S) (g : R₀ →+* S)
    (σ σf ε : Series S)
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσf0 : ∀ i, MvPowerSeries.constantCoeff (σf i) = 0)
    (hε0 : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)
    (hlin : ∀ m : ℕ, (Series.map f (X.F.nthSeries m)).comp σf = σf.comp (Series.map g (X₀.F.nthSeries m)))
    (u v α β : ℕ) (hu : IsUnit ((u : ℕ) : Zp2 p)) (hv : IsUnit ((v : ℕ) : Zp2 p))
    (h : (Series.map f (X.F.nthSeries (u * p ^ α))).comp (σ.comp ε) =
      (Series.map f (X.F.nthSeries (u * v * p ^ β))).comp σf) :
    (Series.map f (X.F.nthSeries (p ^ α))).comp (σ.comp (ε.comp (Series.map g (X₀.act ((hv.unit⁻¹ : (Zp2 p)ˣ) : Zp2 p))))) =
      (Series.map f (X.F.nthSeries (p ^ β))).comp σf := by

  have hσε0 : ∀ i, MvPowerSeries.constantCoeff ((σ.comp ε) i) = 0 :=
    Series.constantCoeff_comp hσ0 hε0
  have hGc : ∀ (a : Zp2 p) (i : Fin 2), MvPowerSeries.constantCoeff (A X₀ g a i) = 0 :=
    fun a i => A_const X₀ g a i

  have hcast1 : ((u * p ^ α : ℕ) : Zp2 p) = (hu.unit : Zp2 p) * ((p ^ α : ℕ) : Zp2 p) := by
    rw [IsUnit.unit_spec]; push_cast; ring
  have hcast2 : ((u * v * p ^ β : ℕ) : Zp2 p) =
      (hu.unit : Zp2 p) * (((p ^ β : ℕ) : Zp2 p) * (hv.unit : Zp2 p)) := by
    rw [IsUnit.unit_spec, IsUnit.unit_spec]; push_cast; ring

  rw [A_natCast, A_natCast, hcast1, hcast2, A_mul, A_mul,
    Series.comp_assoc _ _ _ (A_const X f _) hσε0, Series.comp_assoc _ _ _ (A_const X f _) hσf0] at h
  have h1 := congrArg (fun ψ => (A X f ((hu.unit⁻¹ : (Zp2 p)ˣ) : Zp2 p)).comp ψ) h
  rw [A_inv_comp X f hu.unit _ (Series.constantCoeff_comp (A_const X f _) hσε0),
    A_inv_comp X f hu.unit _ (Series.constantCoeff_comp (A_const X f _) hσf0),
    A_mul, Series.comp_assoc _ _ _ (A_const X f _) hσf0] at h1

  have hv' : (A X f (hv.unit : Zp2 p)).comp σf = σf.comp (A X₀ g (hv.unit : Zp2 p)) := by
    rw [IsUnit.unit_spec, ← A_natCast, ← A_natCast]
    exact hlin v
  rw [hv'] at h1

  have h2 := congrArg (fun ψ => ψ.comp (A X₀ g ((hv.unit⁻¹ : (Zp2 p)ˣ) : Zp2 p))) h1
  rw [Series.comp_assoc _ _ _ hσε0 (hGc _), Series.comp_assoc _ _ _ hε0 (hGc _),
    Series.comp_assoc _ _ _ (Series.constantCoeff_comp hσf0 (hGc _)) (hGc _),
    Series.comp_assoc _ _ _ (hGc _) (hGc _), ← A_mul, Units.mul_inv, A_one, Series.comp_id] at h2
  rw [A_natCast, A_natCast]
  exact h2

end S_CerednikDrinfeld_FormalODModule_nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq (solution)
