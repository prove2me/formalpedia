-- Prove2me | solution 1 for Formalism.UG.P.hecke_act_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:15.889545+00:00
-- url     : https://prove2.me/submissions/1d8003c2-aac6-468c-9d14-a2d16ea6d046

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Theorems.Thm_Formalism_UG_P_out_smul
import Theorems.Thm_Formalism_UG_P_finsum_out_mul
import Theorems.Thm_Formalism_UG_P_finite_supp
import Theorems.Thm_Formalism_UG_P_amf_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
private theorem finite_support_left_translate_of_biinvariant {k : Type} [CommRing k] (K : Subgroup G) (f : G → k)
    (hbi : ∀ (a b : K) (g : G), f (↑a * g * ↑b) = f g) (hfin : {x : G ⧸ K | f x.out ≠ 0}.Finite)
    (a : G) : {x : G ⧸ K | f (a * x.out) ≠ 0}.Finite := by
  refine (hfin.preimage (f := fun x : G ⧸ K => a • x)
    fun _ _ _ _ h => MulAction.injective a h).subset ?_
  intro x hx
  show f (a • x).out ≠ 0
  obtain ⟨κ, hκ⟩ := out_smul K a x
  rw [hκ]
  have e : f (a * x.out * ↑κ) = f (a * x.out) := by simpa using hbi 1 κ (a * x.out)
  rw [e]
  exact hx
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.HeckeActMul := by
  intro G _ Γ K k _ W _ _ ρ hK f₁ hf₁ f₂ hf₂ φ hφ
  have hbi₂ : ∀ (a b : K) (g : G), f₂ (↑a * g * ↑b) = f₂ g :=
    (show IsBiInv K f₂ ∧ FinDosetSupp K f₂ from hf₂).1
  have hfin₁ := finite_supp K hK f₁ hf₁
  have hfin₂ := finite_supp K hK f₂ hf₂
  funext g
  simp only [hAct, conv]
  have hA : ∀ y : G ⧸ K, ∑ᶠ z : G ⧸ K, f₂ z.out • φ (g * y.out * z.out) =
      ∑ᶠ x : G ⧸ K, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) := by
    intro y
    have := finsum_out_mul K y.out (fun h => f₂ (y.out⁻¹ * h) • φ (g * h)) (by
      intro h c
      show f₂ (y.out⁻¹ * (h * ↑c)) • φ (g * (h * ↑c)) = f₂ (y.out⁻¹ * h) • φ (g * h)
      rw [(by simp [mul_assoc] : y.out⁻¹ * (h * ↑c) = ↑(1 : K) * (y.out⁻¹ * h) * ↑c), hbi₂,
        (by rw [mul_assoc] : g * (h * ↑c) = g * h * ↑c), amf_right hφ])
    simpa [mul_assoc] using this
  simp_rw [hA]
  set A := hfin₁.toFinset with hAdef
  have hB : ∀ y : G ⧸ K, {x : G ⧸ K | f₂ (y.out⁻¹ * x.out) ≠ 0}.Finite :=
    fun y => finite_support_left_translate_of_biinvariant K f₂ hbi₂ hfin₂ y.out⁻¹
  have hX : (⋃ y ∈ A, {x : G ⧸ K | f₂ (y.out⁻¹ * x.out) ≠ 0}).Finite :=
    A.finite_toSet.biUnion fun y _ => hB y
  set X := hX.toFinset with hXdef
  have hAsub : ∀ y : G ⧸ K, f₁ y.out ≠ 0 → y ∈ A := fun y hy => hfin₁.mem_toFinset.2 hy
  have hXsub : ∀ y x : G ⧸ K, f₁ y.out ≠ 0 → f₂ (y.out⁻¹ * x.out) ≠ 0 → x ∈ X := by
    intro y x h1 h2
    rw [hX.mem_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 (hAsub y h1)) h2
  have hL : ∀ x : G ⧸ K, ∑ᶠ y : G ⧸ K, f₁ y.out * f₂ (y.out⁻¹ * x.out) =
      ∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out) := by
    intro x
    apply finsum_eq_sum_of_support_subset
    intro y hy
    exact hAsub y (left_ne_zero_of_mul hy)
  simp_rw [hL]
  have eL : ∑ᶠ x : G ⧸ K, (∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out)) • φ (g * x.out) =
      ∑ x ∈ X, (∑ y ∈ A, f₁ y.out * f₂ (y.out⁻¹ * x.out)) • φ (g * x.out) := by
    apply finsum_eq_sum_of_support_subset
    intro x hx
    obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_smul hx)
    exact hXsub y x (left_ne_zero_of_mul hy) (right_ne_zero_of_mul hy)
  have eR : ∑ᶠ y : G ⧸ K, f₁ y.out • ∑ᶠ x : G ⧸ K, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) =
      ∑ y ∈ A, f₁ y.out • ∑ x ∈ X, f₂ (y.out⁻¹ * x.out) • φ (g * x.out) := by
    rw [finsum_eq_sum_of_support_subset (s := A) _ (fun y hy => hAsub y (left_ne_zero_of_smul hy))]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [finsum_eq_sum_of_support_subset (s := X) _
      (fun x hx => hXsub y x (hfin₁.mem_toFinset.1 hy) (left_ne_zero_of_smul hx))]
  rw [eL, eR]
  simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm
end Formalism.UG.P
