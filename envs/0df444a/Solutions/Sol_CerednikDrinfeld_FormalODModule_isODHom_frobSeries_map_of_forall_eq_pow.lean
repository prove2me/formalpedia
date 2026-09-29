-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isODHom_frobSeries_map_of_forall_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0f617ff2-42ee-5a60-a0c3-bb4baca74488

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isODHom_frobSeries_map_of_forall_eq_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace FrobODHom

variable {p : ℕ} [Fact p.Prime] {C D : Type} [CommRing C] [CommRing D]

theorem map_pow_eq_subst_X_pow {σ : Type} (f g : C →+* D) (j : ℕ) (hp : (p : D) = 0)
    (hg : ∀ x : C, g x = (f x) ^ (p ^ j)) (φ : MvPowerSeries σ C) :
    (MvPowerSeries.map f φ) ^ (p ^ j) =
      MvPowerSeries.subst (fun s => (MvPowerSeries.X s : MvPowerSeries σ D) ^ (p ^ j)) (MvPowerSeries.map g φ) := by
  classical
  have hpp : p.Prime := Fact.out
  rcases subsingleton_or_nontrivial D with hD | hD
  · ext m; exact Subsingleton.elim _ _
  haveI : CharP D p := (CharP.charP_iff_prime_eq_zero hpp).mpr hp
  have hgf : g = (iterateFrobenius D p j).comp f :=
    RingHom.ext fun x => by rw [RingHom.comp_apply, iterateFrobenius_def, hg]
  have hR : MvPowerSeries.subst (fun s => (MvPowerSeries.X s : MvPowerSeries σ D) ^ (p ^ j)) (MvPowerSeries.map g φ) =
      MvPowerSeries.expand (p ^ j) (pow_ne_zero j hpp.ne_zero) (MvPowerSeries.map g φ) := by
    rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
  rw [hR, hgf, ← MvPowerSeries.map_iterateFrobenius_expand p hpp.ne_zero (MvPowerSeries.map f φ) j,
    MvPowerSeries.map_expand]
  congr 1

theorem subst_X_pow {τ : Type} (a : Fin 2 → MvPowerSeries τ D)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin 2) (n : ℕ) :
    MvPowerSeries.subst a ((MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ n) = (a i) ^ n := by
  rw [← MvPowerSeries.substAlgHom_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero ha), map_pow,
    MvPowerSeries.substAlgHom_X]

theorem constantCoeff_map_eq_zero (f : C →+* D) {φ : Series C}
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (i : Fin 2) :
    MvPowerSeries.constantCoeff ((φ.map f) i) = 0 := by
  show MvPowerSeries.constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hφ0, map_zero]

end FrobODHom

open FrobODHom in
theorem solution
    {p : ℕ} [Fact p.Prime] {C : Type} [CommRing C] {D : Type} [CommRing D]
    (f g : C →+* D) (j : ℕ) (hp : (p : D) = 0) (hg : ∀ x : C, g x = (f x) ^ (p ^ j))
    (G : FormalODModule p C) :
    FormalODModule.IsODHom (G.map f) (G.map g) (Rigidified.frobSeries (p := p) D j) := by
  classical
  have hpp : p.Prime := Fact.out
  have hq : p ^ j ≠ 0 := pow_ne_zero j hpp.ne_zero
  have h0 : ∀ i, MvPowerSeries.constantCoeff (Rigidified.frobSeries (p := p) D j i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ (p ^ j)) = 0
    rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]
  refine ⟨⟨h0, fun i => ?_⟩, fun a => ?_, ?_⟩
  ·
    have hF0 : ∀ l, MvPowerSeries.constantCoeff ((G.map f).F.toPowerSeries l) = 0 :=
      (G.map f).F.constantCoeff_eq_zero
    show MvPowerSeries.subst (G.map f).F.toPowerSeries ((MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ (p ^ j)) = _
    rw [subst_X_pow _ hF0 i]
    show (MvPowerSeries.map f (G.F.toPowerSeries i)) ^ (p ^ j) = _
    rw [map_pow_eq_subst_X_pow f g j hp hg]
    show _ = MvPowerSeries.subst _ (MvPowerSeries.map g (G.F.toPowerSeries i))
    congr 1
    funext s
    rcases s with l | l
    · simp only [Sum.elim_inl]
      show _ = MvPowerSeries.subst _ ((MvPowerSeries.X l : MvPowerSeries (Fin 2) D) ^ (p ^ j))
      rw [subst_X_pow _ (fun l => MvPowerSeries.constantCoeff_X _) l]
    · simp only [Sum.elim_inr]
      show _ = MvPowerSeries.subst _ ((MvPowerSeries.X l : MvPowerSeries (Fin 2) D) ^ (p ^ j))
      rw [subst_X_pow _ (fun l => MvPowerSeries.constantCoeff_X _) l]
  ·
    funext i
    show MvPowerSeries.subst ((G.act a).map f) ((MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ (p ^ j)) =
      MvPowerSeries.subst (Rigidified.frobSeries (p := p) D j) (MvPowerSeries.map g (G.act a i))
    rw [subst_X_pow _ (constantCoeff_map_eq_zero f (G.isLawHom_act a).1) i]
    show (MvPowerSeries.map f (G.act a i)) ^ (p ^ j) = _
    rw [map_pow_eq_subst_X_pow f g j hp hg]
    rfl
  ·
    funext i
    show MvPowerSeries.subst (G.varpi.map f) ((MvPowerSeries.X i : MvPowerSeries (Fin 2) D) ^ (p ^ j)) =
      MvPowerSeries.subst (Rigidified.frobSeries (p := p) D j) (MvPowerSeries.map g (G.varpi i))
    rw [subst_X_pow _ (constantCoeff_map_eq_zero f G.isLawHom_varpi.1) i]
    show (MvPowerSeries.map f (G.varpi i)) ^ (p ^ j) = _
    rw [map_pow_eq_subst_X_pow f g j hp hg]
    rfl

end S_CerednikDrinfeld_FormalODModule_isODHom_frobSeries_map_of_forall_eq_pow
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isODHom_frobSeries_map_of_forall_eq_pow (solution)
