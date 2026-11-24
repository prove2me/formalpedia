-- Prove2me | solution 1 for Formalism.UG.P.csScale_den
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:04.841339+00:00
-- url     : https://prove2.me/submissions/5a1ffa6f-aed2-471e-98eb-638ea0274d8e

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Theorems.Thm_Formalism_UG_P_csScale_hform_add_left
import Theorems.Thm_Formalism_UG_P_csScale_hform_add_right
import Theorems.Thm_Formalism_UG_P_csScale_hform_zero_left
import Theorems.Thm_Formalism_UG_P_csScale_hform_zero_right
import Theorems.Thm_Formalism_UG_P_csScale_hform_smul_left
import Theorems.Thm_Formalism_UG_P_csScale_hform_smul_right
import Theorems.Thm_Formalism_UG_P_csScale_sigma_int

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
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
    (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) * hform (σ : E →+* E) J x y) := by
  classical
  have hint : ∀ k : ℤ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)
  have hden : ∀ z : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * z) := by
    intro z
    have hq : IsAlgebraic ℚ z := (Algebra.IsIntegral.isIntegral (R := ℚ) z).isAlgebraic
    have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hq
    obtain ⟨m, hm, hmi⟩ := hz.exists_integral_multiple
    exact ⟨m, hm, by rwa [zsmul_eq_mul] at hmi⟩
  obtain ⟨S, hS⟩ := Module.Finite.iff_fg.mp hfin
  choose f hf0 hfi using fun p : (n → E) × (n → E) => hden (hform (σ : E →+* E) J p.1 p.2)
  refine ⟨∏ p ∈ S ×ˢ S, f p, Finset.prod_ne_zero_iff.mpr fun p _ => hf0 p, ?_⟩
  have hgen : ∀ s ∈ S, ∀ t ∈ S,
      IsIntegral ℤ (((∏ p ∈ S ×ˢ S, f p : ℤ) : E) * hform (σ : E →+* E) J s t) := by
    intro s hs t ht
    have hp : (s, t) ∈ S ×ˢ S := Finset.mem_product.mpr ⟨hs, ht⟩
    rw [← Finset.mul_prod_erase _ _ hp, Int.cast_mul, mul_comm ((f (s, t) : ℤ) : E), mul_assoc]
    exact (hint _).mul (hfi (s, t))
  intro x hx y hy
  rw [← hS] at hx hy
  induction hx using Submodule.span_induction generalizing y with
  | mem s hs =>
    induction hy using Submodule.span_induction with
    | mem t ht => exact hgen s hs t ht
    | zero => rw [csScale_hform_zero_right, mul_zero]; exact isIntegral_zero
    | add u v _ _ hu hv => rw [csScale_hform_add_right, mul_add]; exact hu.add hv
    | smul a u _ hu =>
      rw [← algebraMap_smul E a u, csScale_hform_smul_right, mul_left_comm]
      exact (NumberField.RingOfIntegers.isIntegral_coe a).mul hu
  | zero => rw [csScale_hform_zero_left, mul_zero]; exact isIntegral_zero
  | add u v _ _ hu hv => rw [csScale_hform_add_left, mul_add]; exact (hu y hy).add (hv y hy)
  | smul a u _ hu =>
    rw [← algebraMap_smul E a u, csScale_hform_smul_left, mul_left_comm]
    exact (csScale_sigma_int σ a).mul (hu y hy)
end Formalism.UG.P
