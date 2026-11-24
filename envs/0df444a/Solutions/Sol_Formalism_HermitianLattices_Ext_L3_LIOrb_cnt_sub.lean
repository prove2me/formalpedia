-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:52:31.245171+00:00
-- url     : https://prove2.me/submissions/4d425846-3f65-4c45-8b40-2e973f286d69

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_congrP_add_of_mem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_smul_iff_unif
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_unif_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {A B : Submodule (𝓞 K) V} (hA : locF 𝔭 A = A) (hB : locF 𝔭 B = B)
    (hAi : IsIntegralAt 𝔭 h A) (hBA : B ≤ A) {k : ℕ}
    (hk : ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V) ≤ B)
    (hfin : Finite (↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B))) (n : 𝓞 F) {Ω : Set V}
    (hΩB : Ω ⊆ B) (hΩ : ∀ y ∈ Ω, ∀ z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V), y + z ∈ Ω) :
    cnt h B 𝔭 k n Ω = Nat.card (↥A ⧸ B.submoduleOf A) * cnt h A 𝔭 k n Ω := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  obtain ⟨c, hc⟩ : ∃ c : K, c = algebraMap F K (π : F) ^ k := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by rw [hc]; exact pow_ne_zero _ (D2.unif_ne_zero hπ')
  have memA : ∀ x : V, x ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V) ↔ ∃ y ∈ A, x = c • y := by
    intro x
    have := D2.mem_smul_iff_unif h𝔭 hπ hπ' A (k := k) (x := x)
    rwa [hA, ← hc] at this
  have memB : ∀ x : V, x ∈ ((extP K 𝔭) ^ k • B : Submodule (𝓞 K) V) ↔ ∃ y ∈ B, x = c • y := by
    intro x
    have := D2.mem_smul_iff_unif h𝔭 hπ hπ' B (k := k) (x := x)
    rwa [hB, ← hc] at this
  let m : ↥A →ₗ[𝓞 K] ↥B := LinearMap.codRestrict B
    (((LinearMap.lsmul K V c).restrictScalars (𝓞 K)).comp A.subtype)
    (fun a => hk ((memA _).2 ⟨a, a.2, rfl⟩))
  have hm : ∀ a : ↥A, ((m a : ↥B) : V) = c • (a : V) := fun a => rfl
  let ψ : ↥A →ₗ[𝓞 K] (↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B)) :=
    (Submodule.mkQ _).comp m
  have hψ : ∀ a : ↥A, ψ a = Submodule.Quotient.mk (m a) := fun a => rfl
  have hker : LinearMap.ker ψ = B.submoduleOf A := by
    ext a
    rw [LinearMap.mem_ker, hψ, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, hm, memB]
    change _ ↔ (a : V) ∈ B
    constructor
    · rintro ⟨y, hy, e⟩
      rw [smul_right_injective V hc0 e]
      exact hy
    · intro ha
      exact ⟨a, ha, rfl⟩
  let ψb : (↥A ⧸ B.submoduleOf A) →ₗ[𝓞 K] (↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B)) :=
    Submodule.liftQ _ ψ hker.ge
  have hψb : ∀ a : ↥A, ψb (Submodule.Quotient.mk a) = Submodule.Quotient.mk (m a) := fun a => rfl
  have ψb_inj : Function.Injective ψb := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  let φ : (↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B)) →ₗ[𝓞 K]
      (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
    Submodule.mapQ _ _ (Submodule.inclusion hBA) (by
      intro y hy
      rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
      rw [Submodule.mem_smul_top_iff] at hy
      exact Submodule.smul_mono le_rfl hBA hy)
  have hφ : ∀ y : ↥B, φ (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (Submodule.inclusion hBA y) := fun y => rfl
  have hφψ : ∀ q, φ (ψb q) = 0 := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hψb, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff]
    exact (memA _).2 ⟨a, a.2, rfl⟩
  choose y0 hy0 using fun x : {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
    ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} => x.2
  let yB : {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
    ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} → ↥B :=
    fun x => ⟨y0 x, hΩB (hy0 x).2.2⟩
  have hφy : ∀ x, φ (Submodule.Quotient.mk (yB x)) = x.1 := fun x => (hy0 x).1
  let Fn : (↥A ⧸ B.submoduleOf A) × {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
    ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} →
      {x : ↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B) //
    ∃ y : ↥B, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} :=
    fun p => ⟨Submodule.Quotient.mk (yB p.2) + ψb p.1, by
      obtain ⟨q, x⟩ := p
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hz : c • (a : V) ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V) := (memA _).2 ⟨a, a.2, rfl⟩
      exact ⟨yB x + m a, rfl, congrP_add_of_mem hF h𝔭 hA hAi (y0 x).2 hz (hy0 x).2.1,
        hΩ _ (hy0 x).2.2 _ hz⟩⟩
  have hFn : ∀ p, (Fn p).1 = Submodule.Quotient.mk (yB p.2) + ψb p.1 := fun p => rfl
  have hbij : Function.Bijective Fn := by
    constructor
    · rintro ⟨q, x⟩ ⟨q', x'⟩ e
      have e1 := congrArg Subtype.val e
      rw [hFn, hFn] at e1
      have e2 := congrArg φ e1
      simp only [map_add, hφψ, hφy, add_zero] at e2
      have e3 : x = x' := Subtype.ext e2
      subst e3
      have e4 : q = q' := ψb_inj (add_left_cancel e1)
      rw [e4]
    · rintro ⟨_, y, rfl, hcy, hyΩ⟩
      let x : {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
        ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
        CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} :=
        ⟨Submodule.Quotient.mk (Submodule.inclusion hBA y), _, rfl, hcy, hyΩ⟩
      have h1 : Submodule.inclusion hBA y - y0 x ∈
          ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
        rw [← Submodule.Quotient.eq]
        exact (hy0 x).1.symm
      rw [Submodule.mem_smul_top_iff, memA] at h1
      obtain ⟨a, ha, e⟩ := h1
      refine ⟨(Submodule.Quotient.mk ⟨a, ha⟩, x), Subtype.ext ?_⟩
      rw [hFn, hψb, ← Submodule.Quotient.mk_add]
      congr 1
      apply Subtype.ext
      change ((y0 x : ↥A) : V) + c • a = y
      rw [← e]
      change ((y0 x : ↥A) : V) + ((y : V) - (y0 x : ↥A)) = y
      abel
  exact (Nat.card_congr (Equiv.ofBijective Fn hbij)).symm.trans (Nat.card_prod _ _)
end Formalism.HermitianLattices.Ext.L3.LIOrb
