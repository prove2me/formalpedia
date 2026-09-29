-- Prove2me | solution 1 for FormalGroup.exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b74a357e-b9a7-55bc-93a6-3183fe9cd532

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Theorems.Thm_MvFormalGroup_subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem solution
    {T k : Type u} [CommRing T] [CommRing k] (π : T →+* k) (hπ : RingHom.ker π ^ 2 = ⊥)
    (q : ℕ) (hq : (q : T) = 0)
    (F₀ : FormalGroup k) (G₀ G : FormalGroup T) [G.IsComm]
    (hG₀ : G₀.IsBaseChange π F₀) (hG : G.IsBaseChange π F₀) :
    ∃ θ : FormalGroup.LawHom G₀ G, θ.series = G.nthSeries q := by
  classical

  haveI : (MvFormalGroup.ofFormalGroup G).IsComm := MvFormalGroup.instIsCommOfFormalGroup G
  have hI : RingHom.ker π ^ (1 + 1) = ⊥ := by simpa using hπ
  have hp : (q : T) ^ 1 = 0 := by rw [pow_one]; exact hq
  obtain ⟨-, hrig⟩ := MvFormalGroup.subst_nthSeries_eq_of_map_eq_and_exists_hom_of_ker_pow_eq_bot
    π 1 hI q 1 hp (MvFormalGroup.ofFormalGroup G)

  have E₀ : MvFormalGroup.ofFormalGroup F₀ = (MvFormalGroup.ofFormalGroup G₀).map π :=
    MvFormalGroup.ofFormalGroup_eq_map_of_isBaseChange G₀ π F₀ hG₀
  have E : MvFormalGroup.ofFormalGroup F₀ = (MvFormalGroup.ofFormalGroup G).map π :=
    MvFormalGroup.ofFormalGroup_eq_map_of_isBaseChange G π F₀ hG

  have hφ0 : ∀ i : Fin 1, MvPowerSeries.constantCoeff
      ((fun _ : Fin 1 => (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) T)) i) = 0 :=
    fun _ => MvPowerSeries.constantCoeff_X 0
  have hex : ∃ f₀ : ((MvFormalGroup.ofFormalGroup G₀).map π).Hom ((MvFormalGroup.ofFormalGroup G).map π),
      ∀ i, f₀.toPowerSeries i =
        MvPowerSeries.map π ((fun _ : Fin 1 => (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) T)) i) := by
    rw [← E₀, ← E]
    refine ⟨MvFormalGroup.Hom.id _, fun i => ?_⟩
    rw [MvPowerSeries.map_X, Subsingleton.elim i 0]
    rfl
  obtain ⟨f, hf⟩ := hrig 1 (MvFormalGroup.ofFormalGroup G₀) (fun _ => MvPowerSeries.X 0) hφ0 hex
  refine ⟨FormalGroup.LawHom.ofMvHom f, ?_⟩
  rw [FormalGroup.LawHom.ofMvHom_series, hf 0, show q ^ (1 * 1) = q by rw [mul_one, pow_one],
    MvFormalGroup.nthSeries_ofFormalGroup]
  have hX : (fun _ : Fin 1 => (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) T)) = MvPowerSeries.X :=
    funext fun i => by rw [Subsingleton.elim i 0]
  rw [hX]
  show MvFormalGroup.ofMv (MvPowerSeries.subst MvPowerSeries.X (MvFormalGroup.toMv (G.nthSeries q))) = G.nthSeries q
  rw [MvPowerSeries.subst_self]
  exact MvFormalGroup.ofMv_toMv _

end S_FormalGroup_exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot
end P2MW
export P2MW.S_FormalGroup_exists_lawHom_series_eq_nthSeries_of_isBaseChange_of_ker_sq_eq_bot (solution)
