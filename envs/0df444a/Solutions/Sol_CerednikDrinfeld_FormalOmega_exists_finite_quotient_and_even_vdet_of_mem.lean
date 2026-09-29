-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_finite_quotient_and_even_vdet_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3e3e04f1-a1a0-51b1-b143-078d766ba8dd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_finite_quotient_and_even_vdet_of_mem

set_option autoImplicit false

open scoped MatrixGroups

namespace F6GroupParity

theorem relIndex_ne_zero_of_even {G : Type} [Group G] (χ : G →* Multiplicative ℤ)
    (Γ Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (χ x))) :
    Γ'.relIndex Γ ≠ 0 := by
  let ψ : ↥Γ →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (((Multiplicative.toAdd (χ (x : G))) : ℤ) : ZMod 2)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul, map_mul, toAdd_mul, Int.cast_add, ofAdd_add] }
  have hψ : ∀ x : ↥Γ, ψ x = 1 ↔ Even (Multiplicative.toAdd (χ (x : G))) := by
    intro x
    rw [even_iff_two_dvd]
    change Multiplicative.ofAdd (((Multiplicative.toAdd (χ (x : G))) : ℤ) : ZMod 2) = 1 ↔ _
    rw [ofAdd_eq_one]
    have h := ZMod.intCast_zmod_eq_zero_iff_dvd (Multiplicative.toAdd (χ (x : G))) 2
    simpa using h
  have hker : ψ.ker = Γ'.subgroupOf Γ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hΓ', hψ]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  show (Γ'.subgroupOf Γ).index ≠ 0
  rw [← hker, Subgroup.index_ker]
  exact Nat.card_pos.ne'

theorem relIndex_map_ne_zero {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (Γ Γ' : Subgroup G) (hle : Γ' ≤ Γ) (h : Γ'.relIndex Γ ≠ 0) :
    (Γ'.map f).relIndex (Γ.map f) ≠ 0 := by
  have heq : (Γ'.map f).subgroupOf (Γ.map f) = (Γ'.subgroupOf Γ).map (f.subgroupMap Γ) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨y, hle hy⟩, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]; exact hy
      · exact Subtype.ext hyx
    · rintro ⟨z, hz, hzx⟩
      refine ⟨(z : G), ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hz; exact hz
      · exact congrArg Subtype.val hzx
  have hdvd : ((Γ'.map f).subgroupOf (Γ.map f)).index ∣ (Γ'.subgroupOf Γ).index := by
    rw [heq]; exact Subgroup.index_map_dvd _ (MonoidHom.subgroupMap_surjective f Γ)
  intro h0
  apply h
  show (Γ'.subgroupOf Γ).index = 0
  have : ((Γ'.map f).subgroupOf (Γ.map f)).index = 0 := h0
  rw [this] at hdvd
  exact Nat.eq_zero_of_zero_dvd hdvd

end F6GroupParity

open F6GroupParity in

theorem solution

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))
    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))

    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ'.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal) (hNidx : N.relIndex (Γ'.map ρ) ≠ 0) :
    ∃ (G₂ : Type) (_ : Group G₂) (_ : Finite G₂) (θ : ↥Γ →* G₂),
      Function.Surjective θ ∧ (∀ γ : ↥Γ, θ γ = 1 ↔ ρ (γ : G) ∈ N) ∧
      (∀ γ : ↥Γ, ρ (γ : G) ∈ N → Even (Multiplicative.toAdd (vdet (σ (γ : G))))) := by
  classical
  haveI hN : (N.subgroupOf (Γ.map ρ)).Normal := hNnorm
  have hΓ'le : Γ' ≤ Γ := fun x hx => ((hΓ' x).mp hx).1
  have hle2 : Γ'.map ρ ≤ Γ.map ρ := Subgroup.map_mono hΓ'le

  have hidx : (N.subgroupOf (Γ.map ρ)).index ≠ 0 := by
    show N.relIndex (Γ.map ρ) ≠ 0
    rw [← Subgroup.relIndex_mul_relIndex (H := N) (K := Γ'.map ρ) (L := Γ.map ρ) hNle hle2]
    exact mul_ne_zero hNidx
      (relIndex_map_ne_zero ρ Γ Γ' hΓ'le (relIndex_ne_zero_of_even (vdet.comp σ) Γ Γ' hΓ'))
  haveI hfin : Finite (↥(Γ.map ρ) ⧸ N.subgroupOf (Γ.map ρ)) := by
    haveI := Subgroup.fintypeOfIndexNeZero hidx
    infer_instance
  let θ : ↥Γ →* ↥(Γ.map ρ) ⧸ N.subgroupOf (Γ.map ρ) :=
    (QuotientGroup.mk' (N.subgroupOf (Γ.map ρ))).comp (ρ.subgroupMap Γ)
  refine ⟨↥(Γ.map ρ) ⧸ N.subgroupOf (Γ.map ρ), inferInstance, hfin, θ, ?_, ?_, ?_⟩
  · exact (QuotientGroup.mk'_surjective _).comp (MonoidHom.subgroupMap_surjective ρ Γ)
  · intro γ
    show ((ρ.subgroupMap Γ γ : ↥(Γ.map ρ)) : ↥(Γ.map ρ) ⧸ N.subgroupOf (Γ.map ρ)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  · intro γ hγN
    obtain ⟨δ, hδ, hδγ⟩ := Subgroup.mem_map.mp (hNle hγN)
    have hδeven : Even (Multiplicative.toAdd (vdet (σ δ))) := ((hΓ' δ).mp hδ).2

    have hcen : (σ δ)⁻¹ * σ (γ : G) ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K₀) := by
      rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul, map_inv, ← hρ, ← hρ, hδγ, inv_mul_cancel]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
    obtain ⟨c, hc⟩ := hcen
    have hγeq : σ (γ : G) = σ δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
      rw [hc, mul_inv_cancel_left]

    have vdet_congr : ∀ g h : Matrix.GeneralLinearGroup (Fin 2) K₀,
        (Matrix.GeneralLinearGroup.det g : K₀) = (Matrix.GeneralLinearGroup.det h : K₀) → vdet g = vdet h := by
      intro g h hgh
      obtain ⟨u, hu⟩ := (hvdet h (Multiplicative.toAdd (vdet h))).mp (by simp)
      have := (hvdet g (Multiplicative.toAdd (vdet h))).mpr ⟨u, by rw [hgh]; exact hu⟩
      simpa using this

    let d : Matrix.GeneralLinearGroup (Fin 2) K₀ :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(c : K₀), 1]) (by simp)
    have hdval : (d : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![(c : K₀), 1] := rfl
    have hddet : (Matrix.GeneralLinearGroup.det d : K₀) = c := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hdval, Matrix.det_diagonal]
      simp
    have hd : (Matrix.GeneralLinearGroup.det (d * d) : K₀) =
        (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) c) : K₀) := by
      rw [map_mul, Matrix.GeneralLinearGroup.det_scalar, Units.val_mul, Units.val_pow_eq_pow_val,
        Fintype.card_fin, hddet, pow_two]
    have hsc : Even (Multiplicative.toAdd (vdet (Matrix.GeneralLinearGroup.scalar (Fin 2) c))) := by
      rw [← vdet_congr _ _ hd, map_mul, toAdd_mul]
      exact ⟨_, rfl⟩
    rw [hγeq, map_mul, toAdd_mul]
    exact hδeven.add hsc

end S_CerednikDrinfeld_FormalOmega_exists_finite_quotient_and_even_vdet_of_mem
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_finite_quotient_and_even_vdet_of_mem (solution)
