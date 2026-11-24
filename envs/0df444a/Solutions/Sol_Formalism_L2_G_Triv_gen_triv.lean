-- Prove2me | solution 1 for Formalism.L2.G.Triv.gen_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:59:48.084678+00:00
-- url     : https://prove2.me/submissions/72940390-ec05-4ab9-8284-4499ee0c7300

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_GenCoprime
import Theorems.Thm_Formalism_L2_G_Triv_gen_coprime
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_L2_G_Triv_finite_stabAt_of_local
import Theorems.Thm_Formalism_UG_P_rational_points_le_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.BasicNotions
namespace Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
private lemma inv_mul_mul_pow {G : Type} [Group G] (x y : G) (n : ℕ) :
    (x⁻¹ * y * x) ^ n = x⁻¹ * y ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group
end Formalism.L2.G.Triv
end
end

set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
namespace Formalism.L2.G.Triv
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤)
    (U : Subgroup (GL (Fin k) 𝒜))
    (hU : ∀ x ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) x ∈ stabGL (latS (F := F) (v.adicCompletion F) (SV E v) Λ))
    (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (v : Fin 2 → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, (g i : 𝓞 F) ∈ (v i).asIdeal) (ρ : ∀ i, E ⊗[F] (v i).adicCompletion F →+* (v i).adicCompletion F)
    (h : ∀ i, GL (Fin k) ((v i).adicCompletion F))
    (hUg : ∀ i, ∀ z ∈ U, (h i)⁻¹ * bc (ρ i) (bc (prV (E := E) (v i)) z) * h i ∈ iwU F k (v i))
    (x : UPts σ J 𝔸) (γ : GL (Fin k) E) (hγJ : γ ∈ UJ (σ : E →+* E) J)
    (hγ : (x : GL (Fin k) 𝒜)⁻¹ * bc (inclE (F := F) 𝔸) γ * x ∈ U) : γ = 1 := by
  have hyR : bc (inclE (F := F) 𝔸) γ ∈ ratPts σ J 𝔸 := ⟨γ, hγJ, rfl⟩
  have hyU : bc (inclE (F := F) 𝔸) γ ∈ UPts σ J 𝔸 :=
    Formalism.UG.P.rational_points_le_holds F E (Fin k) σ J 𝔸 hyR
  have hpowU : ∀ m : ℕ, (x : GL (Fin k) 𝒜)⁻¹ * bc (inclE (F := F) 𝔸) γ ^ m * x ∈ U := by
    intro m
    rw [← inv_mul_mul_pow]
    exact U.pow_mem hγ m
  haveI hfinS := finite_stabAt_of_local σ J hτ hH hdet hdef Λ hfin hspan U hU x
  let f : ℕ → stabAt ((ratPts σ J 𝔸).subgroupOf (UPts σ J 𝔸)) (U.subgroupOf (UPts σ J 𝔸)) x :=
    fun m => ⟨⟨⟨bc (inclE (F := F) 𝔸) γ ^ m, pow_mem hyU m⟩, Subgroup.mem_subgroupOf.2 (pow_mem hyR m)⟩,
      by
        show _ ∈ U.subgroupOf (UPts σ J 𝔸)
        exact Subgroup.mem_subgroupOf.2 (hpowU m)⟩
  obtain ⟨m₁, m₂, hne12, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hpow : bc (inclE (F := F) 𝔸) γ ^ m₁ = bc (inclE (F := F) 𝔸) γ ^ m₂ := by
    have e := congrArg (fun s => ((s.1 : UPts σ J 𝔸) : GL (Fin k) 𝒜)) heq
    exact e

  obtain ⟨N, hN0, hyN⟩ : ∃ N : ℕ, 0 < N ∧ bc (inclE (F := F) 𝔸) γ ^ N = 1 := by
    rcases Nat.lt_or_gt_of_ne hne12 with hlt | hlt
    · refine ⟨m₂ - m₁, Nat.sub_pos_of_lt hlt, ?_⟩
      have e : bc (inclE (F := F) 𝔸) γ ^ m₂
          = bc (inclE (F := F) 𝔸) γ ^ m₁ * bc (inclE (F := F) 𝔸) γ ^ (m₂ - m₁) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [← hpow] at e
      exact mul_left_cancel (a := bc (inclE (F := F) 𝔸) γ ^ m₁) (by rw [mul_one]; exact e.symm)
    · refine ⟨m₁ - m₂, Nat.sub_pos_of_lt hlt, ?_⟩
      have e : bc (inclE (F := F) 𝔸) γ ^ m₁
          = bc (inclE (F := F) 𝔸) γ ^ m₂ * bc (inclE (F := F) 𝔸) γ ^ (m₁ - m₂) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hpow] at e
      exact mul_left_cancel (a := bc (inclE (F := F) 𝔸) γ ^ m₂) (by rw [mul_one]; exact e.symm)

  obtain ⟨a, m, hm, hNam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' (g 0) (hg 0).one_lt.ne'
  have hg0m : Nat.Coprime m (g 0) :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (hg 0)).mpr hm)
  have hγ1 : γ ^ (g 0 ^ a) = 1 := by
    refine gen_coprime U (g 0) (hg 0) (v 0) (hv 0) (ρ 0) (h 0) (hUg 0) (x : GL (Fin k) 𝒜)
      (γ ^ (g 0 ^ a)) ?_ m hg0m ?_
    · rw [map_pow]
      exact hpowU _
    · rw [map_pow, ← pow_mul, ← hNam]
      exact hyN
  have hcop : Nat.Coprime (g 0 ^ a) (g 1) :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes (hg 0) (hg 1)).mpr hne)
  refine gen_coprime U (g 1) (hg 1) (v 1) (hv 1) (ρ 1) (h 1) (hUg 1) (x : GL (Fin k) 𝒜) γ hγ
    (g 0 ^ a) hcop ?_
  rw [← map_pow, hγ1, map_one]
end Formalism.L2.G.Triv
