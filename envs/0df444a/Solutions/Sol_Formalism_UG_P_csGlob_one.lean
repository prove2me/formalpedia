-- Prove2me | solution 1 for Formalism.UG.P.csGlob_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:32:16.597406+00:00
-- url     : https://prove2.me/submissions/cecc63eb-65f6-4000-a2d3-062e3e10f6de

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlobApprox
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Theorems.Thm_Formalism_UG_P_csGlob_int
import Theorems.Thm_Formalism_UG_P_csGlob_approx
import Theorems.Thm_Formalism_UG_P_csGlob_single
import Theorems.Thm_Formalism_UG_P_adelstabL_upper
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_levelafC_mul


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
theorem _root_.solution (hA : Formalism.UG.CS.IntAdApprox) (Λ : Submodule (𝓞 E) (n → E))
    (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    Formalism.UG.CS.globLat (F := F) 1 Λ = Λ := by
  classical
  obtain ⟨m, hm0, hsingle⟩ := csGlob_single Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  set c₁ : 𝓞 F := (m : 𝓞 F)
  have hc₁ : c₁ ≠ 0 := Int.cast_ne_zero.2 hm0
  have hcE : algebraMap (𝓞 F) E c₁ = (m : E) := map_intCast _ _
  have key : ∀ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∃ y ∈ Λ, ∃ s : n → 𝒜,
      (∀ i, s i ∈ 𝒮) ∧ u = fun i => ι (y i) + levelafC E c₁ * s i := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x, hx, rfl⟩ := hu
      exact ⟨x, hx, 0, fun _ => zero_mem _, by ext i; simp⟩
    | zero => exact ⟨0, zero_mem _, 0, fun _ => zero_mem _, by ext i; simp⟩
    | add u w _ _ hu hw =>
      obtain ⟨y, hy, s, hs, rfl⟩ := hu
      obtain ⟨y', hy', s', hs', rfl⟩ := hw
      refine ⟨y + y', add_mem hy hy', s + s', fun i => add_mem (hs i) (hs' i), ?_⟩
      ext i
      simp only [Pi.add_apply, map_add]
      ring
    | smul a u _ hu =>
      obtain ⟨y, hy, s, hs, rfl⟩ := hu
      obtain ⟨b, t, ht, hab⟩ := csGlob_approx (F := F) (E := E) hA (c₁ * c₂) (mul_ne_zero hc₁ hc₂) (a : 𝒜) a.2
      have hy2 : ∀ i, levelafC E c₂ * ι (y i) ∈ 𝒮 := h₂ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
      refine ⟨b • y, Λ.smul_mem b hy, fun i => levelafC E c₂ * ι (y i) * t + (a : 𝒜) * s i,
        fun i => add_mem (mul_mem (hy2 i) ht) (mul_mem a.2 (hs i)), ?_⟩
      ext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
      rw [show algebraMap 𝒮 𝒜 a = (a : 𝒜) from rfl, hab, levelafC_mul]
      ring
  ext x
  constructor
  · intro hx
    have hx' : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
      have : ((1⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈
          latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := hx
      rwa [inv_one, Units.val_one, one_mulVec] at this
    obtain ⟨y, hy, s, hs, he⟩ := key _ hx'
    have hmE : (m : E) ≠ 0 := Int.cast_ne_zero.2 hm0
    have hint : ∀ i, IsIntegral ℤ ((x i - y i) * (m : E)⁻¹) := by
      intro i
      apply csGlob_int (F := F)
      have hi := congrFun he i
      rw [map_mul, map_sub, hi, ← adelstab_incl_C, hcE, add_sub_cancel_left, mul_right_comm,
        ← map_mul, mul_inv_cancel₀ hmE, map_one, one_mul]
      exact hs i
    have hdiff : x - y = ∑ i, (⟨_, hint i⟩ : 𝓞 E) • (Pi.single i (m : E) : n → E) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def]
        show (x - y) j = (x j - y j) * (m : E)⁻¹ * (m : E)
        rw [inv_mul_cancel_right₀ hmE, Pi.sub_apply]
      · intro k _ hkj
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hkj), smul_zero]
      · exact fun h => absurd (Finset.mem_univ j) h
    have hxy : x = y + (x - y) := by abel
    rw [hxy, hdiff]
    exact add_mem hy (sum_mem fun i _ => Λ.smul_mem _ (hsingle i))
  · intro hx
    show ((1⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ
    rw [inv_one, Units.val_one, one_mulVec]
    exact Submodule.subset_span ⟨x, hx, rfl⟩
end Formalism.UG.P
