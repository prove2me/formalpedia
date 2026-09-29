-- Prove2me | solution 1 for Deformation.HondaSystem.map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/261e3b3b-a0bf-50c6-a0dc-76554f7e3565

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Theorems.Thm_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing
import Theorems.Thm_Deformation_DieudonneModule_frobenius_bijective_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct

universe u v

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞))
    (G : ℕ → Type v) [∀ v, CommRing (G v)] [∀ v, HopfAlgebra (ZMod p) (G v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (G v)] [∀ v, Module.Finite (ZMod p) (G v)]
    (s : ∀ v, G (v + 1) →ₐc[ZMod p] G v)
    (π : ∀ v, (Fin r → 𝓞) →+ Deformation.DieudonneModule (ZMod p) p (G v))
    (hπ : ∀ v, Function.Surjective (π v))
    (hπker : ∀ v x, π v x = 0 ↔ ∃ y, x = (p : 𝓞) ^ v • y)
    (hπF : ∀ v x, π v (H₁.F x) = Deformation.DieudonneModule.frobenius (ZMod p) p (G v) (π v x))
    (hπs : ∀ v x, Deformation.DieudonneModule.map (ZMod p) p (s v) (π (v + 1) x) = π v x)
    (v : ℕ)
    (Gc Ge : Type v) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc]
    [Module.Finite (ZMod p) Gc] [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge]
    [Module.Finite (ZMod p) Ge]
    (qc : G v →ₐc[ZMod p] Gc) (πe : G v →ₐc[ZMod p] Ge) (Θ : G v →ₐc[ZMod p] Gc ⊗[ZMod p] Ge)
    (hΘ : Function.Bijective Θ)
    (hΘapply : ∀ b, Θ b = Algebra.TensorProduct.map (qc : G v →ₐ[ZMod p] Gc) (πe : G v →ₐ[ZMod p] Ge)
      (Coalgebra.comul (R := ZMod p) b))
    (hGc : IsLocalRing Gc) (hGe : IsReduced Ge)
    (Mc Met : Submodule 𝓞 (Fin r → 𝓞))
    (hMet : ∀ m, m ∈ Met ↔ ∀ N : ℕ, ∃ y, (H₁.F ^ N) y = m)
    (hMc : ∀ m, m ∈ Mc ↔ ∀ k : ℕ, ∃ N : ℕ, ∃ y, (H₁.F ^ N) m = (p : 𝓞) ^ k • y) :
    (∀ m ∈ Mc, Deformation.DieudonneModule.map (ZMod p) p πe (π v m) = 0) ∧
    (∀ m ∈ Met, Deformation.DieudonneModule.map (ZMod p) p qc (π v m) = 0) := by

  have hsemiπ : Function.Semiconj (π v) H₁.F (Deformation.DieudonneModule.frobenius (ZMod p) p (G v)) :=
    fun x => hπF v x
  have hsemi_map : ∀ {B : Type v} [CommRing B] [HopfAlgebra (ZMod p) B] (φ : G v →ₐc[ZMod p] B),
      Function.Semiconj (Deformation.DieudonneModule.map (ZMod p) p φ)
        (Deformation.DieudonneModule.frobenius (ZMod p) p (G v))
        (Deformation.DieudonneModule.frobenius (ZMod p) p B) :=
    fun φ z => Deformation.DieudonneModule.map_frobenius φ z
  constructor
  ·
    intro m hm
    obtain ⟨N, y, hy⟩ := (hMc m).1 hm v
    have h1 : (Deformation.DieudonneModule.frobenius (ZMod p) p (G v))^[N] (π v m) = 0 := by
      rw [← hsemiπ.iterate_right N m, ← Module.End.pow_apply, hy]
      exact (hπker v _).2 ⟨y, rfl⟩
    apply ((Deformation.DieudonneModule.frobenius_bijective_of_isReduced p Ge hGe).1).iterate N
    rw [← (hsemi_map πe).iterate_right N (π v m), h1, map_zero, Function.iterate_fixed (map_zero _)]
  ·
    intro m hm
    obtain ⟨n, hn⟩ := Deformation.DieudonneModule.exists_frobenius_iterate_eq_zero_of_isLocalRing p Gc hGc
    obtain ⟨y, hy⟩ := (hMet m).1 hm n
    rw [← hy, Module.End.pow_apply, hsemiπ.iterate_right n y, (hsemi_map qc).iterate_right n (π v y)]
    exact hn _

end S_Deformation_HondaSystem_map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct
end P2MW
export P2MW.S_Deformation_HondaSystem_map_eq_zero_of_mem_of_isCompl_of_bijective_tensorProduct (solution)
