-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/3bdf8572-d876-5500-990d-0d811edb7330

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open MvPowerSeries (constantCoeff)

namespace IsoThicken

variable {p : ℕ} [Fact p.Prime]

theorem reduceMap_comp_mk {B₁ B₂ : Type} [CommRing B₁] [CommRing B₂] (g : B₁ →+* B₂) :
    (reduceMap (p := p) g).comp (Ideal.Quotient.mk (pIdeal p B₁)) = (Ideal.Quotient.mk (pIdeal p B₂)).comp g :=
  RingHom.ext fun _ => rfl

theorem Xbar_map {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B₁ B₂ : Type} [CommRing B₁] [CommRing B₂] (t : Rigidified p Φ B₁) (g : B₁ →+* B₂) :
    (t.map g).Xbar = t.Xbar.map (reduceMap g) := by
  show (t.X.map g).map _ = (t.X.map _).map _
  rw [FormalODModule.map_map, FormalODModule.map_map, reduceMap_comp_mk]

theorem natCast_quot_eq_zero (R : Type) [CommRing R] : ((p : R ⧸ pIdeal p R)) ^ 1 = 0 := by
  rw [pow_one, ← map_natCast (Ideal.Quotient.mk (pIdeal p R)) p, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem ker_reduceMap_pow_eq_bot {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)
    (hπ : Function.Surjective π) (N : ℕ) (hN : RingHom.ker π ^ N = ⊥) :
    RingHom.ker (reduceMap (p := p) π) ^ N = ⊥ := by
  have hp0 : ((p : R ⧸ pIdeal p R)) = 0 := by simpa using natCast_quot_eq_zero (p := p) R
  have hker : RingHom.ker (reduceMap (p := p) π) ≤ (RingHom.ker π).map (Ideal.Quotient.mk (pIdeal p R)) := by
    intro x hx
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := pIdeal p R) x
    have hx' : Ideal.Quotient.mk (pIdeal p S) (π q) = 0 := hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx'
    obtain ⟨c, hc⟩ := hx'
    obtain ⟨r, hr⟩ := hπ c
    have hmem : q - (p : R) * r ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, hr, hc, sub_self]
    have hq : Ideal.Quotient.mk (pIdeal p R) q = Ideal.Quotient.mk (pIdeal p R) (q - (p : R) * r) := by
      rw [map_sub, map_mul, map_natCast, hp0, zero_mul, sub_zero]
    rw [hq]
    exact Ideal.mem_map_of_mem _ hmem
  apply le_bot_iff.mp
  calc RingHom.ker (reduceMap (p := p) π) ^ N
      ≤ ((RingHom.ker π).map (Ideal.Quotient.mk (pIdeal p R))) ^ N := Ideal.pow_right_mono hker _
    _ = ((RingHom.ker π) ^ N).map (Ideal.Quotient.mk (pIdeal p R)) := (Ideal.map_pow _ _ _).symm
    _ = ⊥ := by rw [hN, Ideal.map_bot]

end IsoThicken

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {R S : Type} [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) (hR : IsNilpotent (p : R))
    (ψ : O →+* R) (t₁ t₂ : Rigidified p Φ R) (h₁ : t₁.IsAdmissible ι ψ) (h₂ : t₂.IsAdmissible ι ψ)
    (u v : Series R) (hu : FormalODModule.IsODHom t₁.X t₂.X u) (hv : FormalODModule.IsODHom t₂.X t₁.X v)
    (hvu : v.comp u = Series.id R) (huv : u.comp v = Series.id R) (m : ℕ)
    (hc : ((t₂.map π).Xbar.act ((p : Zp2 p) ^ (m + t₂.n))).comp
        (((u.map π).map (Ideal.Quotient.mk (pIdeal p S))).comp (t₁.map π).ρ)
      = ((t₂.map π).Xbar.act ((p : Zp2 p) ^ (m + t₁.n))).comp (t₂.map π).ρ) :
    t₁.IsIsomorphic t₂ := by
  obtain ⟨N, hN⟩ := hker
  rw [Submodule.zero_eq_bot] at hN
  have hN1 : RingHom.ker π ^ (N + 1) = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ N)).trans hN.le)
  have hI := IsoThicken.ker_reduceMap_pow_eq_bot (p := p) π hπ (N + 1) hN1
  let ρπ := reduceMap (p := p) π
  let mkR := Ideal.Quotient.mk (pIdeal p R)
  have hρ₁ : ∀ i, constantCoeff (t₁.ρ i) = 0 := h₁.constantCoeff_ρ
  have hρ₂ : ∀ i, constantCoeff (t₂.ρ i) = 0 := h₂.constantCoeff_ρ
  have hub : FormalODModule.IsODHom t₁.Xbar t₂.Xbar (u.map mkR) := hu.map mkR
  have ccA : ∀ k i, constantCoeff (t₂.Xbar.act ((p : Zp2 p) ^ k) i) = 0 := fun k => (t₂.Xbar.isLawHom_act _).1
  have ccW : ∀ i, constantCoeff (((u.map mkR).comp t₁.ρ) i) = 0 := Series.constantCoeff_comp hub.constantCoeff hρ₁
  have hφ : FormalODModule.IsODHom (t₁.Φbar ψ) t₂.Xbar
      ((t₂.Xbar.act ((p : Zp2 p) ^ (m + t₂.n))).comp ((u.map mkR).comp t₁.ρ)) :=
    (FormalODModule.IsODHom.act_natCast_pow _ _).comp (hub.comp h₁.2.2.1)
  have hψ' : FormalODModule.IsODHom (t₁.Φbar ψ) t₂.Xbar
      ((t₂.Xbar.act ((p : Zp2 p) ^ (m + t₁.n))).comp t₂.ρ) :=
    (FormalODModule.IsODHom.act_natCast_pow _ _).comp h₂.2.2.1
  have e2 : (u.map mkR).map ρπ = (u.map π).map (Ideal.Quotient.mk (pIdeal p S)) := by
    rw [Series.map_map, IsoThicken.reduceMap_comp_mk, ← Series.map_map]
  have heq : ((t₂.Xbar.act ((p : Zp2 p) ^ (m + t₂.n))).comp ((u.map mkR).comp t₁.ρ)).map ρπ =
      ((t₂.Xbar.act ((p : Zp2 p) ^ (m + t₁.n))).comp t₂.ρ).map ρπ := by
    rw [Series.map_comp _ _ _ ccW, Series.map_comp _ _ _ hρ₁, Series.map_comp _ _ _ hρ₂, e2,
      ← FormalODModule.map_act ρπ t₂.Xbar, ← FormalODModule.map_act ρπ t₂.Xbar,
      ← IsoThicken.Xbar_map t₂ π]
    have := hc
    rw [Rigidified.map_ρ, Rigidified.map_ρ] at this
    exact this
  have R' := (CerednikDrinfeld.FormalODModule.act_pow_comp_eq_of_map_eq_and_isODHom_act_pow_comp_of_ker_pow_eq_bot p ρπ N hI 1 (IsoThicken.natCast_quot_eq_zero (p := p) _) (t₁.Φbar ψ) t₂.Xbar).1
    _ _ hφ hψ' heq
  refine ⟨u, v, 1 * N + m, hu, hv, hvu, huv, ?_⟩
  rw [add_assoc, add_assoc, FormalODModule.act_pow_add t₂.Xbar (1 * N) (m + t₂.n),
    FormalODModule.act_pow_add t₂.Xbar (1 * N) (m + t₁.n),
    Series.comp_assoc _ _ _ (ccA _) ccW, Series.comp_assoc _ _ _ (ccA _) hρ₂]
  exact R'

#print axioms solution

end S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent (solution)
