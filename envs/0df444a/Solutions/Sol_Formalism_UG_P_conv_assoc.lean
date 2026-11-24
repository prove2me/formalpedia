-- Prove2me | solution 1 for Formalism.UG.P.conv_assoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:26:18.112511+00:00
-- url     : https://prove2.me/submissions/5ca3cbad-80f7-4ceb-a8c8-34a11f9ab88e

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AssocFin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeAssoc
import Theorems.Thm_Formalism_UG_P_out_smul_out
import Theorems.Thm_Formalism_UG_P_finite_supp_inv
import Theorems.Thm_Formalism_UG_P_finite_supp_translate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G] (K : Subgroup G)
namespace Formalism.UG.P
theorem _root_.solution (hK : IsCommensurated K) {k : Type} [CommRing k] (f₁ f₂ f₃ : G → k)
    (h₁ : FinDosetSupp K f₁) (h₂ : IsBiInv K f₂) (h₃ : IsBiInv K f₃) (h₃' : FinDosetSupp K f₃) :
    conv K (conv K f₁ f₂) f₃ = conv K f₁ (conv K f₂ f₃) := by
  classical
  funext g
  have hA := finite_supp_translate (K := K) hK f₁ h₁ 1
  have hB := finite_supp_inv (K := K) hK f₃ h₃' g
  have sA : ∀ x : G ⧸ K, x ∉ hA.toFinset → f₁ x.out = 0 := by
    intro x hx
    simpa using hx
  have sB : ∀ y : G ⧸ K, y ∉ hB.toFinset → f₃ (y.out⁻¹ * g) = 0 := by
    intro y hy
    simpa using hy
  generalize hA.toFinset = A at sA
  generalize hB.toFinset = B at sB

  have key : ∀ x z : G ⧸ K, f₂ z.out * f₃ (z.out⁻¹ * (x.out⁻¹ * g)) =
      f₂ (x.out⁻¹ * (x.out • z).out) * f₃ ((x.out • z).out⁻¹ * g) := by
    intro x z
    obtain ⟨c, hc⟩ := out_smul_out K x.out z
    rw [hc]
    have e2 : x.out⁻¹ * (x.out * z.out * c) = ((1 : K) : G) * z.out * c := by
      simp [mul_assoc]
    have e3 : (x.out * z.out * c)⁻¹ * g =
        ((c⁻¹ : K) : G) * (z.out⁻¹ * (x.out⁻¹ * g)) * ((1 : K) : G) := by
      simp [mul_assoc]
    rw [e2, e3, h₂, h₃]
  have inner : ∀ x : G ⧸ K, conv K f₂ f₃ (x.out⁻¹ * g) =
      ∑ y ∈ B, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    intro x
    calc conv K f₂ f₃ (x.out⁻¹ * g)
        = ∑ᶠ z : G ⧸ K, f₂ z.out * f₃ (z.out⁻¹ * (x.out⁻¹ * g)) := rfl
      _ = ∑ᶠ z : G ⧸ K, (fun y : G ⧸ K => f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g))
            (MulAction.toPerm x.out z) := finsum_congr (fun z => key x z)
      _ = ∑ᶠ y : G ⧸ K, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) :=
            finsum_comp_equiv (MulAction.toPerm x.out : G ⧸ K ≃ G ⧸ K)
              (f := fun y : G ⧸ K => f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g))
      _ = ∑ y ∈ B, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
        apply finsum_eq_sum_of_support_subset
        intro y hy
        by_contra h
        exact (Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])
  have L : conv K (conv K f₁ f₂) f₃ g =
      ∑ y ∈ B, ∑ x ∈ A, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    rw [show conv K (conv K f₁ f₂) f₃ g =
      ∑ᶠ y : G ⧸ K, (∑ᶠ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * y.out)) * f₃ (y.out⁻¹ * g) from rfl]
    rw [finsum_eq_sum_of_support_subset _ (s := B) ?_]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [finsum_eq_sum_of_support_subset _ (s := A) ?_, Finset.sum_mul]
      intro x hx
      by_contra h
      exact (Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])
    · intro y hy
      by_contra h
      exact (Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])
  have R : conv K f₁ (conv K f₂ f₃) g =
      ∑ x ∈ A, ∑ y ∈ B, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    rw [show conv K f₁ (conv K f₂ f₃) g = ∑ᶠ x : G ⧸ K, f₁ x.out * conv K f₂ f₃ (x.out⁻¹ * g) from rfl]
    rw [finsum_eq_sum_of_support_subset _ (s := A) ?_]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [inner x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    · intro x hx
      by_contra h
      exact (Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])
  rw [L, R, Finset.sum_comm]
end Formalism.UG.P
