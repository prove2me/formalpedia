-- Prove2me | solution 1 for Formalism.UG.P.adelstab_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:56:30.935235+00:00
-- url     : https://prove2.me/submissions/ab1cfd50-33f4-4448-9afa-5a711f993dda

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Theorems.Thm_Formalism_UG_P_adelstab_tr_mem
import Theorems.Thm_Formalism_UG_P_adelstab_dual
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_adelstab_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_levelafC_mul
import Theorems.Thm_Formalism_UG_P_sf_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (G : GL n 𝒜) (L : Submodule 𝒮 (n → 𝒜)) (c₂ d : 𝓞 F) (hc₂ : c₂ ≠ 0)
    (hd : d ≠ 0) (hL : ∀ v ∈ L, ∀ i, levelafC E c₂ * v i ∈ 𝒮)
    (hG : ∀ i j, levelafC E d * (G : Matrix n n 𝒜) i j ∈ 𝒮) :
    Module.Finite (𝓞 E) (adelstabLam F E G L) := by
  classical
  set β := Module.finBasis F E
  obtain ⟨d₀, hd₀, -, hd₀i⟩ := sf_den (fun i => β i)
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  set u : E := algebraMap (𝓞 F) E (d * c₂)
  have hu : u ≠ 0 := adelstab_algebraMap_ne_zero _ (mul_ne_zero hd hc₂)
  set q : E := (d₀ * u)⁻¹
  set W : Submodule (𝓞 F) (n → E) := Submodule.span (𝓞 F)
    (Set.range fun p : n × Fin (Module.finrank F E) => (Pi.single p.1 (q * β' p.2) : n → E))
  have hle : (adelstabLam F E G L).restrictScalars (𝓞 F) ≤ W := by
    intro x hx
    have hw := hL _ hx
    set w := ((G⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i))
    have hx' : (fun i => ι (x i)) = (G : Matrix n n 𝒜) *ᵥ w := by
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have hj : ∀ j, ι (u * x j) ∈ 𝒮 := by
      intro j
      rw [map_mul, adelstab_incl_C, levelafC_mul, congrFun hx' j]
      simp only [mulVec, dotProduct, Finset.mul_sum]
      refine sum_mem fun k _ => ?_
      have : levelafC E d * levelafC E c₂ * ((G : Matrix n n 𝒜) j k * w k) =
          (levelafC E d * (G : Matrix n n 𝒜) j k) * (levelafC E c₂ * w k) := by ring
      rw [this]
      exact mul_mem (hG j k) (hw k)
    have hmem : ∀ j, d₀ * (u * x j) ∈ Submodule.span (𝓞 F) (Set.range β') :=
      fun j => adelstab_dual β d₀ hd₀i _ (adelstab_tr_mem _ (hj j))
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun j _ => ?_
    let Lj : E →ₗ[𝓞 F] (n → E) := (LinearMap.single (𝓞 F) (fun _ => E) j) ∘ₗ
      ((LinearMap.mulLeft F q).restrictScalars (𝓞 F))
    have h1 : Lj (d₀ * (u * x j)) = Pi.single j (x j) := by
      have hd0 : d₀ * u ≠ 0 := mul_ne_zero hd₀ hu
      simp only [Lj, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        LinearMap.mulLeft_apply, LinearMap.coe_single, q]
      congr 1
      rw [← mul_assoc, ← mul_assoc, mul_assoc _ d₀ u, inv_mul_cancel₀ hd0, one_mul]
    rw [← h1]
    have h2 := Submodule.mem_map_of_mem (f := Lj) (hmem j)
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨(j, i), by simp [Lj]⟩
  have : Module.Finite (𝓞 F) W := Module.Finite.span_of_finite _ (Set.finite_range _)
  have : IsNoetherian (𝓞 F) W := inferInstance
  have : IsNoetherian (𝓞 F) ((adelstabLam F E G L).restrictScalars (𝓞 F)) := isNoetherian_of_le hle
  have : Module.Finite (𝓞 F) (adelstabLam F E G L) := inferInstanceAs
    (Module.Finite (𝓞 F) ((adelstabLam F E G L).restrictScalars (𝓞 F)))
  exact Module.Finite.of_restrictScalars_finite (𝓞 F) (𝓞 E) _
end Formalism.UG.P
