-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.mk_lin_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:55.100075+00:00
-- url     : https://prove2.me/submissions/00c9bd77-9fae-4d16-b692-143c967a1213

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldTer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_lin_sub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_form_right
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {m : ℕ} (z : Fin m → ↥L) (g : Fin m → 𝓞 K)
variable {z g}
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i))
    (hg1 : ∀ i, g i - 1 ∈ extP K 𝔭 ^ k) (a b : Fin m → 𝓞 K) :
    (Submodule.Quotient.mk (lin z a) : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk (lin z b) ↔ ∀ i, a i - b i ∈ extP K 𝔭 ^ k := by
  rw [Submodule.Quotient.eq, lin_sub]
  constructor
  · intro hmem i
    have key : ∀ x : ↥L, x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) →
        ∃ y ∈ extP K 𝔭 ^ k, h (z i : V) (x : V) = algebraMap (𝓞 K) K y := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
      · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (z i : V) (z i).2 (m : V) m.2)
        refine ⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩
        rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]
      · obtain ⟨u, hu, hu'⟩ := hx
        obtain ⟨w, hw, hw'⟩ := hy
        exact ⟨u + w, Ideal.add_mem _ hu hw, by rw [Submodule.coe_add, map_add, hu', hw', map_add]⟩
    obtain ⟨y, hy, hyeq⟩ := key _ hmem
    rw [form_right hzo hzg] at hyeq
    have h1 : (a - b) i * g i ∈ extP K 𝔭 ^ k := by
      rw [IsFractionRing.injective (𝓞 K) K hyeq]
      exact hy
    have h2 : (a - b) i * (g i - 1) ∈ extP K 𝔭 ^ k := Ideal.mul_mem_left _ _ (hg1 i)
    have h3 : a i - b i = (a - b) i * g i - (a - b) i * (g i - 1) := by
      simp only [Pi.sub_apply]
      ring
    rw [h3]
    exact Ideal.sub_mem _ h1 h2
  · intro hab
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hab i) Submodule.mem_top
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
