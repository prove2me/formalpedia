-- Prove2me | solution 1 for Formalism.UG.P.csSpan_back
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:56.094535+00:00
-- url     : https://prove2.me/submissions/661fd5c3-65fc-4251-9d30-f2b3d3a83bf3

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Theorems.Thm_Formalism_UG_P_csSpan_approx
import Theorems.Thm_Formalism_UG_P_adelstabL_lower
import Theorems.Thm_Formalism_UG_P_adelstabL_upper
import Theorems.Thm_Formalism_UG_P_adelstab_algebraMap_ne_zero
import Theorems.Thm_Formalism_UG_P_adelstab_entries
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C
import Theorems.Thm_Formalism_UG_P_levelafC_mul
import Theorems.Thm_Formalism_UG_P_levelaf_exists_denom


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
    (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (g : GL n 𝒜) (u : n → 𝒜)
    (hu : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
    u ∈ Submodule.span 𝒮 ((fun x : n → E => fun i => ι (x i)) ''
      (Formalism.UG.CS.globLat g Λ : Set (n → E))) := by
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  obtain ⟨d, hd, c, hc, hg, hg'⟩ := levelaf_exists_denom (F := F) (E := E) g
  have eg := adelstab_entries g d c hc hg
  have eg' := adelstab_entries (g⁻¹) d c hc hg'

  have hint : ∀ i, levelafC E (d * c₂) * u i ∈ 𝒮 := by
    intro i
    set w := ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u with hw
    have hu' : u = (g : Matrix n n 𝒜) *ᵥ w := by
      rw [hw, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    rw [hu', mulVec, dotProduct, Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    have : levelafC E (d * c₂) * ((g : Matrix n n 𝒜) i j * w j) =
        (levelafC E d * (g : Matrix n n 𝒜) i j) * (levelafC E c₂ * w j) := by
      rw [levelafC_mul]; ring
    rw [this]
    exact mul_mem (eg i j) (h₂ w hu j)

  have hM : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) →
      ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => levelafC E (c₁ * d) * v i) ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
    intro v hv
    have : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => levelafC E (c₁ * d) * v i) =
        fun i => levelafC E c₁ *
          ∑ j, (levelafC E d * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i j) * v j := by
      ext i
      rw [mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [levelafC_mul]; ring
    rw [this]
    exact h₁ _ fun i => sum_mem fun j _ => mul_mem (eg' i j) (hv j)

  have hD : d * c₂ * (c₁ * d) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hd hc₂) (mul_ne_zero hc₁ hd)
  choose x' hx' w hw hxw using fun i => csSpan_approx hA _ hD (hint i)
  set α := algebraMap (𝓞 F) E (d * c₂) with hα
  have hα0 : α ≠ 0 := adelstab_algebraMap_ne_zero _ (mul_ne_zero hd hc₂)
  have hαu : IsUnit (ι α) := (IsUnit.mk0 α hα0).map ι
  set x : n → E := fun i => x' i / α with hxdef
  have hux : ∀ i, u i = ι (x i) + levelafC E (c₁ * d) * w i := by
    intro i
    apply hαu.mul_left_cancel
    rw [hα, adelstab_incl_C, mul_add, ← adelstab_incl_C, ← hα, ← map_mul, hxdef,
      mul_div_cancel₀ _ hα0, ← mul_assoc, hα, adelstab_incl_C, ← levelafC_mul, ← hxw i]
  have hxmem : x ∈ Formalism.UG.CS.globLat g Λ := by
    show ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ
    have : (fun i => ι (x i)) = u - fun i => levelafC E (c₁ * d) * w i := by
      ext i; rw [Pi.sub_apply, hux i]; ring
    rw [this, mulVec_sub]
    exact sub_mem hu (hM w hw)
  set β := algebraMap (𝓞 F) E (c₁ * d) with hβ
  have hsk : ∀ k, (Pi.single k β : n → E) ∈ Formalism.UG.CS.globLat g Λ := by
    intro k
    show ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι ((Pi.single k β : n → E) i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ
    have : (fun i => ι ((Pi.single k β : n → E) i)) =
        fun i => levelafC E (c₁ * d) * (Pi.single k (1 : 𝒜) : n → 𝒜) i := by
      ext i
      by_cases h : i = k
      · subst h; simp [hβ, adelstab_incl_C, levelafC_mul]
      · simp [h]
    rw [this]
    refine hM _ fun i => ?_
    by_cases h : i = k
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_apply, if_neg h]; exact zero_mem _
  have hdec : u = (fun i => ι (x i)) +
      ∑ k, (⟨w k, hw k⟩ : 𝒮) • (fun i => ι ((Pi.single k β : n → E) i)) := by
    ext i
    rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single i, hux i]
    · show _ = _ + (_ : 𝒮) • ι ((Pi.single i β : n → E) i)
      rw [Pi.single_eq_same, Subring.smul_def, smul_eq_mul, hβ, adelstab_incl_C, mul_comm]
    · intro k _ hki
      show (_ : 𝒮) • ι ((Pi.single k β : n → E) i) = 0
      rw [Pi.single_apply, if_neg (Ne.symm hki), map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [hdec]
  exact add_mem (Submodule.subset_span ⟨x, hxmem, rfl⟩)
    (sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsk k, rfl⟩))
end Formalism.UG.P
