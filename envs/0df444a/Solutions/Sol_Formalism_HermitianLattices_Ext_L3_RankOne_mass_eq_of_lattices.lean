-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.mass_eq_of_lattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:54:15.794802+00:00
-- url     : https://prove2.me/submissions/5c71dc32-bc35-40d4-ba36-ef2711c8dbb5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNeZeroOfIsLattice
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_isLattice_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_exists_inv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_gmap_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_loc_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mem_isom_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mass_transfer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution {h₁ h₂ : K →ₗ⋆[K] K →ₗ[K] K} (hn₁ : h₁ 1 1 ≠ 0) (hn₂ : h₂ 1 1 ≠ 0)
    {A B : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A) (hB : Submodule.IsLattice K B)
    (hex : ∃ s, IsClassReps h₁ A s) : mass h₂ B = mass h₁ A := by
  obtain ⟨A', hA', hA'A⟩ := exists_inv hA
  obtain ⟨B', hB', hB'B⟩ := exists_inv hB
  have hC : Submodule.IsLattice K (B * A') := isLattice_mul hB hA'
  have hJ : Submodule.IsLattice K (A * B') := isLattice_mul hA hB'
  have hJC : (A * B') * (B * A') = 1 := by
    calc (A * B') * (B * A') = (A' * A) * (B' * B) := by ring
      _ = 1 := by rw [hA'A, hB'B, one_mul]
  have t1 : ∀ g : K ≃ₗ[K] K, (Equiv.refl (K ≃ₗ[K] K)) g ∈ isom h₂ ↔ g ∈ isom h₁ := fun g => by
    rw [Equiv.refl_apply, mem_isom_iff hn₂, mem_isom_iff hn₁]
  have t2 : ∀ (g : K ≃ₗ[K] K) (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (gmap g M) =
        gmap ((Equiv.refl (K ≃ₗ[K] K)) g) (mulE (B * A') (A * B') hJC M) := fun g M =>
    gmap_mul g (B * A') M
  have t3 : ∀ (p : Ideal (𝓞 K)), p.IsMaximal → ∀ (M : Submodule (𝓞 K) K),
      mulE (B * A') (A * B') hJC (loc p M) = loc p (mulE (B * A') (A * B') hJC M) :=
    fun p hp M => loc_mul hp (B * A') M
  have t4 : ∀ (M : Submodule (𝓞 K) K),
      Submodule.IsLattice K (mulE (B * A') (A * B') hJC M) ↔ Submodule.IsLattice K M := by
    intro M
    show Submodule.IsLattice K (B * A' * M) ↔ Submodule.IsLattice K M
    constructor
    · intro hM
      have e := isLattice_mul hJ hM
      rwa [← mul_assoc, hJC, one_mul] at e
    · intro hM
      exact isLattice_mul hC hM
  have hΦA : mulE (B * A') (A * B') hJC A = B := by
    show B * A' * A = B
    rw [mul_assoc, hA'A, mul_one]
  have he := (mass_transfer (mulE (B * A') (A * B') hJC) (Equiv.refl _) t1 t2 t3 t4 hex).2
  rw [hΦA] at he
  exact he
end Formalism.HermitianLattices.Ext.L3.RankOne
