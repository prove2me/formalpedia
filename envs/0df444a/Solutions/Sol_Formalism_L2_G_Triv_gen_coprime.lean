-- Prove2me | solution 1 for Formalism.L2.G.Triv.gen_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:44:37.358844+00:00
-- url     : https://prove2.me/submissions/432968a2-0447-45ab-a57d-63e13b5e8e49

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_GenCoprime
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_G_Triv_iwU_coprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
namespace Formalism.L2.G.Triv
theorem _root_.solution (U : Subgroup (GL (Fin k) 𝒜)) (g : ℕ) (hg : g.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (g : 𝓞 F) ∈ v.asIdeal) (ρ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (h : GL (Fin k) (v.adicCompletion F))
    (hU : ∀ z ∈ U, h⁻¹ * bc ρ (bc (prV (E := E) v) z) * h ∈ iwU F k v)
    (x : GL (Fin k) 𝒜) (γ : GL (Fin k) E) (hγ : x⁻¹ * bc (inclE (F := F) 𝔸) γ * x ∈ U) (N : ℕ) (hN : Nat.Coprime N g)
    (hγN : bc (inclE (F := F) 𝔸) γ ^ N = 1) : γ = 1 := by
  have hφ : ∀ A : GL (Fin k) E, bc ρ (bc (prV (E := E) v) (bc (inclE (F := F) 𝔸) A))
      = bc (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) A := by
    intro A
    apply Units.ext
    ext i j
    simp [bc]
  have hinj : Function.Injective (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) :=
    RingHom.injective _
  have hz : (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x) ^ N = 1 := by
    rw [show x⁻¹ * bc (inclE (F := F) 𝔸) γ * x = MulAut.conj x⁻¹ (bc (inclE (F := F) 𝔸) γ) by
      simp [MulAut.conj_apply], ← map_pow, hγN, map_one]
  have hmem := hU _ hγ
  have hwN : (bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x))) ^ N = 1 := by
    rw [← map_pow, ← map_pow, hz, map_one, map_one]
  have hδN : (h⁻¹ * bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) * h) ^ N = 1 := by
    rw [show h⁻¹ * bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) * h
        = MulAut.conj h⁻¹ (bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x))) by
      simp only [MulAut.conj_apply, inv_inv], ← map_pow, hwN, map_one]
  have hδ1 := iwU_coprime v g hg hv _ hmem N hN hδN
  have hw1 : bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) = 1 := by
    calc _ = h * (h⁻¹ * bc ρ (bc (prV (E := E) v) (x⁻¹ * bc (inclE (F := F) 𝔸) γ * x)) * h) * h⁻¹ := by
          group
      _ = 1 := by rw [hδ1]; group
  simp only [map_mul, map_inv] at hw1
  rw [hφ] at hw1
  have hγ1 : bc (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) γ = 1 := by
    calc _ = bc ρ (bc (prV (E := E) v) x) * ((bc ρ (bc (prV (E := E) v) x))⁻¹
          * bc (ρ.comp ((prV (E := E) v).comp (inclE (F := F) 𝔸))) γ * bc ρ (bc (prV (E := E) v) x))
          * (bc ρ (bc (prV (E := E) v) x))⁻¹ := by group
      _ = 1 := by rw [hw1]; group
  apply Units.ext
  ext i j
  apply hinj
  have e := congrArg (fun A : GL (Fin k) (v.adicCompletion F) => A.1 i j) hγ1
  simpa [bc, Matrix.one_apply, apply_ite] using e
end Formalism.L2.G.Triv
