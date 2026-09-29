-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.IsSpecial.of_isODHom_of_comp_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/66ebf343-ac11-5948-b833-76a41f2f20ea

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_IsSpecial_of_isODHom_of_comp_eq_id

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace IsoInvAux

open MvFormalGroup

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]

theorem linearPart_comp (ψ φ : Series B) (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    linearPart (ψ.comp φ) = linearPart ψ * linearPart φ := by
  show linearPart (fun i => MvPowerSeries.subst φ (ψ i)) = _
  exact linearPart_subst hφ ψ

theorem linearPart_id : linearPart (Series.id B) = (1 : Matrix (Fin 2) (Fin 2) B) := by
  show linearPart (fun i : Fin 2 => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B)) = 1
  exact linearPart_X

end IsoInvAux

theorem solution
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (Y Y' : FormalODModule p B) (u v : Series B)
    (hu : FormalODModule.IsODHom Y Y' u) (hv : FormalODModule.IsODHom Y' Y v)
    (hvu : v.comp u = Series.id B) (huv : u.comp v = Series.id B)
    (hY : Y.IsSpecial j) : Y'.IsSpecial j := by
  classical
  have hu0 : ∀ i, MvPowerSeries.constantCoeff (u i) = 0 := hu.constantCoeff
  have hv0 : ∀ i, MvPowerSeries.constantCoeff (v i) = 0 := hv.constantCoeff

  have hLvu : MvFormalGroup.linearPart v * MvFormalGroup.linearPart u = 1 := by
    rw [← IsoInvAux.linearPart_comp v u hu0, hvu, IsoInvAux.linearPart_id]
  have hLuv : MvFormalGroup.linearPart u * MvFormalGroup.linearPart v = 1 := by
    rw [← IsoInvAux.linearPart_comp u v hv0, huv, IsoInvAux.linearPart_id]

  have hint : ∀ a : Zp2 p, MvFormalGroup.linearPart u * MvFormalGroup.linearPart (Y.act a) =
      MvFormalGroup.linearPart (Y'.act a) * MvFormalGroup.linearPart u := by
    intro a
    rw [← IsoInvAux.linearPart_comp u (Y.act a) (Y.isLawHom_act a).1, hu.2.1 a, IsoInvAux.linearPart_comp _ u hu0]

  let T : Y.Lie →ₗ[B] Y'.Lie := Matrix.mulVecLin (MvFormalGroup.linearPart u)
  let T' : Y'.Lie →ₗ[B] Y.Lie := Matrix.mulVecLin (MvFormalGroup.linearPart v)
  have hTT' : T ∘ₗ T' = LinearMap.id := by
    show Matrix.mulVecLin _ ∘ₗ Matrix.mulVecLin _ = LinearMap.id
    rw [← Matrix.mulVecLin_mul, hLuv, Matrix.mulVecLin_one]
  have hT'T : T' ∘ₗ T = LinearMap.id := by
    show Matrix.mulVecLin _ ∘ₗ Matrix.mulVecLin _ = LinearMap.id
    rw [← Matrix.mulVecLin_mul, hLvu, Matrix.mulVecLin_one]
  let e : Y.Lie ≃ₗ[B] Y'.Lie := LinearEquiv.ofLinear T T' hTT' hT'T
  have he : (e : Y.Lie →ₗ[B] Y'.Lie) = T := rfl

  have hact : ∀ (a : Zp2 p) (m : Y.Lie), Y'.lieAct a (T m) = T (Y.lieAct a m) := by
    intro a m
    show Matrix.mulVecLin _ (Matrix.mulVecLin _ m) = Matrix.mulVecLin _ (Matrix.mulVecLin _ m)
    rw [← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, hint]

  have hker : ∀ (c : Zp2 p → B) (m : Y.Lie),
      (∀ a, m ∈ LinearMap.ker (Y.lieAct a - c a • LinearMap.id)) ↔
        (∀ a, T m ∈ LinearMap.ker (Y'.lieAct a - c a • LinearMap.id)) := by
    intro c m
    refine forall_congr' fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_apply, hact, ← map_smul, ← map_sub]
    exact (map_eq_zero_iff T (show Function.Injective T from e.injective)).symm
  have hmap : ∀ (c : Zp2 p → B),
      (⨅ a, LinearMap.ker (Y'.lieAct a - c a • LinearMap.id)) =
        (⨅ a, LinearMap.ker (Y.lieAct a - c a • LinearMap.id)).map (e : Y.Lie →ₗ[B] Y'.Lie) := by
    intro c
    ext m'
    rw [Submodule.mem_iInf, Submodule.mem_map]
    constructor
    · intro h
      refine ⟨e.symm m', ?_, e.apply_symm_apply m'⟩
      rw [Submodule.mem_iInf, hker]
      intro a
      have : T (e.symm m') = m' := e.apply_symm_apply m'
      rw [this]; exact h a
    · rintro ⟨m, hm, rfl⟩
      rw [Submodule.mem_iInf, hker] at hm
      exact hm
  have hZ : Y'.lieZero j = (Y.lieZero j).map (e : Y.Lie →ₗ[B] Y'.Lie) := hmap (fun a => j a)
  have hO : Y'.lieOne j = (Y.lieOne j).map (e : Y.Lie →ₗ[B] Y'.Lie) := hmap (fun a => j (WittVector.frobenius a))
  obtain ⟨hc, hi0, hi1⟩ := hY
  refine ⟨?_, ?_, ?_⟩
  · rw [hZ, hO]
    exact (Submodule.orderIsoMapComap e).isCompl hc
  · rw [hZ]
    haveI := hi0
    exact Module.Invertible.congr (Submodule.equivMapOfInjective (e : Y.Lie →ₗ[B] Y'.Lie) e.injective (Y.lieZero j))
  · rw [hO]
    haveI := hi1
    exact Module.Invertible.congr (Submodule.equivMapOfInjective (e : Y.Lie →ₗ[B] Y'.Lie) e.injective (Y.lieOne j))

end S_CerednikDrinfeld_FormalODModule_IsSpecial_of_isODHom_of_comp_eq_id
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_IsSpecial_of_isODHom_of_comp_eq_id (solution)
