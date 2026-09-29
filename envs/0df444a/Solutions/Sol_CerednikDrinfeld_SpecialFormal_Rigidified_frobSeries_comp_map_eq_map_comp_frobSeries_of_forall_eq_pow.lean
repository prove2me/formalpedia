-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a76bb8d4-1d02-5304-bbfb-2e9f04e8a47e

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem solution
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {B : Type} [CommRing B]
    (ψ χ : O →+* B) (j : ℕ)
    (hχ : ∀ x : O ⧸ pIdeal p O, residueMap ψ x = (residueMap χ x) ^ (p ^ j))
    (e : Series (O ⧸ pIdeal p O)) (he : ∀ i, MvPowerSeries.constantCoeff (e i) = 0) :
    (Rigidified.frobSeries (p := p) (B ⧸ pIdeal p B) j).comp (Series.map (residueMap χ) e) =
      (Series.map (residueMap ψ) e).comp (Rigidified.frobSeries (p := p) (B ⧸ pIdeal p B) j) := by
  classical
  have hp : p.Prime := Fact.out
  funext i
  rcases subsingleton_or_nontrivial (B ⧸ pIdeal p B) with hB | hB
  · ext m; exact Subsingleton.elim _ _
  haveI : CharP (B ⧸ pIdeal p B) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal p B)) p, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl)
  have hs : MvPowerSeries.HasSubst (Series.map (residueMap χ) e) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun l => by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map (residueMap χ) (e l)) = 0
      rw [MvPowerSeries.constantCoeff_map, he, map_zero])

  have hL : (Rigidified.frobSeries (p := p) (B ⧸ pIdeal p B) j).comp (Series.map (residueMap χ) e) i =
      (MvPowerSeries.map (residueMap χ) (e i)) ^ (p ^ j) := by
    show MvPowerSeries.subst (Series.map (residueMap χ) e) ((MvPowerSeries.X i : MvPowerSeries (Fin 2) _) ^ (p ^ j)) = _
    rw [← MvPowerSeries.substAlgHom_apply hs, map_pow, MvPowerSeries.substAlgHom_X]
    rfl

  have hR : (Series.map (residueMap ψ) e).comp (Rigidified.frobSeries (p := p) (B ⧸ pIdeal p B) j) i =
      MvPowerSeries.expand (p ^ j) (pow_ne_zero j hp.ne_zero) (MvPowerSeries.map (residueMap ψ) (e i)) := by
    show MvPowerSeries.subst (fun l => (MvPowerSeries.X l : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ (p ^ j))
      (MvPowerSeries.map (residueMap ψ) (e i)) = _
    rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]
  have hψχ : residueMap ψ = (iterateFrobenius (B ⧸ pIdeal p B) p j).comp (residueMap χ) :=
    RingHom.ext fun x => by rw [RingHom.comp_apply, iterateFrobenius_def, hχ]
  rw [hL, hR, hψχ, ← MvPowerSeries.map_iterateFrobenius_expand p hp.ne_zero (MvPowerSeries.map (residueMap χ) (e i)) j,
    MvPowerSeries.map_expand]
  congr 1

end S_CerednikDrinfeld_SpecialFormal_Rigidified_frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_frobSeries_comp_map_eq_map_comp_frobSeries_of_forall_eq_pow (solution)
