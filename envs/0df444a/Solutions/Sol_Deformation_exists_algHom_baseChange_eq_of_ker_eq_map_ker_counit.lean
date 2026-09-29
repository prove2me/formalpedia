-- Prove2me | solution 1 for Deformation.exists_algHom_baseChange_eq_of_ker_eq_map_ker_counit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4335a6b9-5f0e-5a06-9fad-80700e9f8dbb

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_algHom_baseChange_eq_of_ker_eq_map_ker_counit

set_option autoImplicit false

open scoped TensorProduct
open Function

universe u v w₁ w₂ w₃ w'

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.map_map wittHom wittHomMap coe_wittHomMap TruncWitt.fontaineKer TruncWitt.map_mem_fontaineKer"
namespace FontaineKerStab
p2m_open "Deformation"

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime]
variable {k : Type v} [CommRing k] [Algebra 𝓞 k]

noncomputable abbrev red {X : Type w₁} [CommRing X] [Algebra 𝓞 X] {Y : Type w'} [CommRing Y]
    [Algebra 𝓞 Y] (x : X →ₐ[𝓞] Y) : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y :=
  Algebra.TensorProduct.map (AlgHom.id k k) x

theorem red_tmul {X : Type w₁} [CommRing X] [Algebra 𝓞 X] {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
    (x : X →ₐ[𝓞] Y) (c : k) (r : X) : red (k := k) x (c ⊗ₜ[𝓞] r) = c ⊗ₜ[𝓞] x r := by
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem red_comp {X : Type w₁} [CommRing X] [Algebra 𝓞 X] {Y : Type w₂} [CommRing Y] [Algebra 𝓞 Y]
    {Z : Type w₃} [CommRing Z] [Algebra 𝓞 Z] (x : X →ₐ[𝓞] Y) (y : Y →ₐ[𝓞] Z) :
    red (k := k) (y.comp x) = (red (k := k) y).comp (red (k := k) x) := by
  refine Algebra.TensorProduct.ext' fun c r => ?_
  simp

theorem tmul_algebraMap {X : Type w₁} [CommRing X] [Algebra 𝓞 X] (c : k) (o : 𝓞) :
    (c ⊗ₜ[𝓞] algebraMap 𝓞 X o : k ⊗[𝓞] X) = algebraMap k (k ⊗[𝓞] X) (o • c) := by
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

def Cond (p : ℕ) [Fact p.Prime] {X : Type w₁} [CommRing X] [Bialgebra 𝓞 X]
    {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y] (χ : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y) : Prop :=
  ∀ (n : ℕ) (m : Deformation.wittHom k p n (k ⊗[𝓞] X)),
    (m : TruncatedWittVector p n (k ⊗[𝓞] X)) ∈ Deformation.TruncWitt.fontaineKer p n
        (Algebra.TensorProduct.includeRight : X →ₐ[𝓞] k ⊗[𝓞] X).toRingHom →
      Deformation.TruncWitt.map χ.toRingHom (m : TruncatedWittVector p n (k ⊗[𝓞] X)) ∈
        Deformation.TruncWitt.fontaineKer p n
          (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] k ⊗[𝓞] Y).toRingHom

theorem cond_comp {𝒮 : Type w₁} [CommRing 𝒮] [Bialgebra 𝓞 𝒮] {ℛ : Type w₂} [CommRing ℛ]
    [Bialgebra 𝓞 ℛ] {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
    (q : 𝒮 →ₐc[𝓞] ℛ) (χ : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y) (hχ : Cond p χ) :
    Cond p (χ.comp (Bialgebra.TensorProduct.map (BialgHom.id k k) q :
      k ⊗[𝓞] 𝒮 →ₐ[k] k ⊗[𝓞] ℛ)) := by
  intro n m hm
  set qk : k ⊗[𝓞] 𝒮 →ₐc[k] k ⊗[𝓞] ℛ := Bialgebra.TensorProduct.map (BialgHom.id k k) q with hqk
  have hcomm : (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom.comp
      (q : 𝒮 →ₐ[𝓞] ℛ).toRingHom =
      (qk : k ⊗[𝓞] 𝒮 →ₐ[k] k ⊗[𝓞] ℛ).toRingHom.comp
        (Algebra.TensorProduct.includeRight : 𝒮 →ₐ[𝓞] k ⊗[𝓞] 𝒮).toRingHom := by
    refine RingHom.ext fun s => ?_
    simp [hqk, Algebra.TensorProduct.includeRight_apply]
  have hm' : (Deformation.wittHomMap p n qk m : TruncatedWittVector p n (k ⊗[𝓞] ℛ)) ∈
      Deformation.TruncWitt.fontaineKer p n
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom := by
    rw [Deformation.coe_wittHomMap]
    exact Deformation.TruncWitt.map_mem_fontaineKer (q : 𝒮 →ₐ[𝓞] ℛ).toRingHom
      (qk : k ⊗[𝓞] 𝒮 →ₐ[k] k ⊗[𝓞] ℛ).toRingHom _ hcomm hm
  have := hχ n _ hm'
  rw [Deformation.coe_wittHomMap, Deformation.TruncWitt.map_map] at this
  exact this

noncomputable abbrev unitPoint (𝒮' : Type w₁) [CommRing 𝒮'] [Bialgebra 𝓞 𝒮'] (Y : Type w')
    [CommRing Y] [Algebra 𝓞 Y] : 𝒮' →ₐ[𝓞] Y :=
  (Algebra.ofId 𝓞 Y).comp (Bialgebra.counitAlgHom 𝓞 𝒮')

theorem exists_algHom_red_eq
    {𝒮 : Type w₁} [CommRing 𝒮] [Bialgebra 𝓞 𝒮]
    {𝒮' : Type w₂} [CommRing 𝒮'] [Bialgebra 𝓞 𝒮']
    {ℛ : Type w₃} [CommRing ℛ] [Bialgebra 𝓞 ℛ]
    (φ : 𝒮' →ₐc[𝓞] 𝒮) (q : 𝒮 →ₐc[𝓞] ℛ) (hq : Surjective q)
    (hexact : RingHom.ker (q : 𝒮 →ₐ[𝓞] ℛ) =
      Ideal.map (φ : 𝒮' →ₐ[𝓞] 𝒮) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 𝒮')))
    {Y : Type w'} [CommRing Y] [Algebra 𝓞 Y]
    (hH : ∀ ψ : k ⊗[𝓞] 𝒮 →ₐ[k] k ⊗[𝓞] Y, Cond p ψ → ∃ x : 𝒮 →ₐ[𝓞] Y, red x = ψ)
    (hH' : ∀ y y' : 𝒮' →ₐ[𝓞] Y, red (k := k) y = red y' → y = y')
    (χ : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] Y) (hχ : Cond p χ) :
    ∃ x : ℛ →ₐ[𝓞] Y, red x = χ := by
  classical
  set qk : k ⊗[𝓞] 𝒮 →ₐc[k] k ⊗[𝓞] ℛ := Bialgebra.TensorProduct.map (BialgHom.id k k) q with hqk

  obtain ⟨xH, hxH⟩ := hH (χ.comp (qk : k ⊗[𝓞] 𝒮 →ₐ[k] k ⊗[𝓞] ℛ)) (cond_comp q χ hχ)

  have hqφ : ∀ s : 𝒮', q (φ s) = algebraMap 𝓞 ℛ (Coalgebra.counit (R := 𝓞) s) := by
    intro s
    have hs : s - algebraMap 𝓞 𝒮' (Coalgebra.counit (R := 𝓞) s) ∈
        RingHom.ker (Bialgebra.counitAlgHom 𝓞 𝒮') := by
      rw [RingHom.mem_ker, map_sub]
      change Coalgebra.counit s - Coalgebra.counit (algebraMap 𝓞 𝒮' (Coalgebra.counit s)) = 0
      rw [Bialgebra.counit_algebraMap, sub_self]
    have hmem : (φ : 𝒮' →ₐ[𝓞] 𝒮) (s - algebraMap 𝓞 𝒮' (Coalgebra.counit (R := 𝓞) s)) ∈
        RingHom.ker (q : 𝒮 →ₐ[𝓞] ℛ) := hexact ▸ Ideal.mem_map_of_mem _ hs
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero] at hmem
    exact hmem

  have hred : red (k := k) (xH.comp (φ : 𝒮' →ₐ[𝓞] 𝒮)) = red (unitPoint 𝒮' Y) := by
    rw [red_comp, hxH]
    refine Algebra.TensorProduct.ext' fun c s => ?_
    rw [AlgHom.comp_apply, red_tmul, AlgHom.comp_apply, red_tmul]
    change χ (qk (c ⊗ₜ[𝓞] φ s)) = c ⊗ₜ[𝓞] (unitPoint 𝒮' Y) s
    have h1 : qk (c ⊗ₜ[𝓞] φ s) = c ⊗ₜ[𝓞] q (φ s) := rfl
    have h2 : (unitPoint 𝒮' Y) s = algebraMap 𝓞 Y (Coalgebra.counit (R := 𝓞) s) := rfl
    rw [h1, hqφ, tmul_algebraMap, AlgHom.commutes, h2, tmul_algebraMap]
  have hxφ : xH.comp (φ : 𝒮' →ₐ[𝓞] 𝒮) = unitPoint 𝒮' Y := hH' _ _ hred

  have hle : RingHom.ker (q : 𝒮 →ₐ[𝓞] ℛ).toRingHom ≤ RingHom.ker xH.toRingHom := by
    change RingHom.ker (q : 𝒮 →ₐ[𝓞] ℛ) ≤ _
    rw [hexact, Ideal.map_le_iff_le_comap]
    intro s hs
    rw [RingHom.mem_ker] at hs
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change xH.comp (φ : 𝒮' →ₐ[𝓞] 𝒮) s = 0
    rw [hxφ, AlgHom.comp_apply, Algebra.ofId_apply]
    change algebraMap 𝓞 Y (Bialgebra.counitAlgHom 𝓞 𝒮' s) = 0
    rw [hs, map_zero]
  have hq' : Surjective (q : 𝒮 →ₐ[𝓞] ℛ).toRingHom := hq
  let x₀ : ℛ →+* Y := (q : 𝒮 →ₐ[𝓞] ℛ).toRingHom.liftOfSurjective hq' ⟨xH.toRingHom, hle⟩
  have hx₀ : ∀ s, x₀ (q s) = xH s := fun s =>
    (q : 𝒮 →ₐ[𝓞] ℛ).toRingHom.liftOfRightInverse_comp_apply _ _ ⟨xH.toRingHom, hle⟩ s
  let x : ℛ →ₐ[𝓞] Y :=
    { x₀ with
      commutes' := fun o => by
        have : algebraMap 𝓞 ℛ o = q (algebraMap 𝓞 𝒮 o) := ((q : 𝒮 →ₐ[𝓞] ℛ).commutes o).symm
        change x₀ (algebraMap 𝓞 ℛ o) = _
        rw [this, hx₀, AlgHom.commutes] }
  have hxq : ∀ s, x (q s) = xH s := hx₀

  refine ⟨x, Algebra.TensorProduct.ext' fun c r => ?_⟩
  obtain ⟨s, rfl⟩ := hq r
  rw [red_tmul, hxq, ← red_tmul (k := k) xH c s, hxH, AlgHom.comp_apply]
  rfl

end Deformation.FontaineKerStab

open Deformation.FontaineKerStab in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    {𝒮 : Type w₁} [CommRing 𝒮] [Bialgebra 𝓞 𝒮]
    {𝒮' : Type w₂} [CommRing 𝒮'] [Bialgebra 𝓞 𝒮']
    {ℛ : Type w₃} [CommRing ℛ] [Bialgebra 𝓞 ℛ]
    (φ : 𝒮' →ₐc[𝓞] 𝒮) (q : 𝒮 →ₐc[𝓞] ℛ) (hq : Function.Surjective q)
    (hexact : RingHom.ker (q : 𝒮 →ₐ[𝓞] ℛ) =
      Ideal.map (φ : 𝒮' →ₐ[𝓞] 𝒮) (RingHom.ker (Bialgebra.counitAlgHom 𝓞 𝒮')))
    (Y : Type w') [CommRing Y] [Algebra 𝓞 Y]
    (hH : ∀ ψ : TensorProduct 𝓞 k 𝒮 →ₐ[k] TensorProduct 𝓞 k Y,
      (∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k 𝒮)),
        (m : TruncatedWittVector p n (TensorProduct 𝓞 k 𝒮)) ∈ Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : 𝒮 →ₐ[𝓞] TensorProduct 𝓞 k 𝒮).toRingHom →
          Deformation.TruncWitt.map ψ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k 𝒮)) ∈
            Deformation.TruncWitt.fontaineKer p n
              (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 k Y).toRingHom) →
      ∃ x : 𝒮 →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = ψ)
    (hH' : ∀ y y' : 𝒮' →ₐ[𝓞] Y,
      Algebra.TensorProduct.map (AlgHom.id k k) y = Algebra.TensorProduct.map (AlgHom.id k k) y' →
        y = y')
    (χ : TensorProduct 𝓞 k ℛ →ₐ[k] TensorProduct 𝓞 k Y)
    (hχ : ∀ (n : ℕ) (m : Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ)),
      (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)) ∈ Deformation.TruncWitt.fontaineKer p n
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom →
        Deformation.TruncWitt.map χ.toRingHom (m : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)) ∈
          Deformation.TruncWitt.fontaineKer p n
            (Algebra.TensorProduct.includeRight : Y →ₐ[𝓞] TensorProduct 𝓞 k Y).toRingHom) :
    ∃ x : ℛ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = χ :=
  exists_algHom_red_eq (p := p) φ q hq hexact (fun ψ hψ => hH ψ hψ) (fun y y' h => hH' y y' h) χ hχ

end S_Deformation_exists_algHom_baseChange_eq_of_ker_eq_map_ker_counit
end P2MW
export P2MW.S_Deformation_exists_algHom_baseChange_eq_of_ker_eq_map_ker_counit (solution)
