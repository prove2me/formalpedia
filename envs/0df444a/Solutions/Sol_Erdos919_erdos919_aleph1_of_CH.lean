-- Prove2me | solution 1 for Erdos919.erdos919_aleph1_of_CH
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:43:32.7454+00:00
-- url     : https://prove2.me/submissions/50a4e595-50d4-4587-926e-cc7b899ad7f1

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_ColorableOn_mono_set
public import Theorems.Thm_Erdos919_ColorableOn_toNat
public import Theorems.Thm_Erdos919_shift_lower
public import Theorems.Thm_Erdos919_shift_colorableOn
public import Theorems.Thm_Erdos919_smallCard_comap
public import Theorems.Thm_Erdos919_mk_W
public import Theorems.Thm_Erdos919_aleph1_lt_aleph2
public import Theorems.Thm_Erdos919_exists_gt_of_small
public import Theorems.Thm_Erdos919_erdos919_aleph1_iff

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (hCH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph1 G := by
  apply erdos919_aleph1_iff.2
  have hV : Nonempty (W.{u} ≃ {p : W.{u} × W.{u} // p.1 < p.2}) := by
    apply Cardinal.eq.1
    apply le_antisymm
    · have hnx : ∀ i : W.{u}, ∃ j, i < j := fun i => by
        obtain ⟨u, hu⟩ := exists_gt_of_small (J := PUnit) (fun _ => i)
          (by rw [mk_punit]; exact one_le_aleph0.trans (aleph0_le_aleph 1))
        exact ⟨u, hu PUnit.unit⟩
      choose nx hnx using hnx
      exact mk_le_of_injective
        (f := fun i => (⟨(i, nx i), hnx i⟩ : {p : W.{u} × W.{u} // p.1 < p.2}))
        (fun a b h => by simpa using congrArg (fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.1) h)
    · calc #{p : W.{u} × W.{u} // p.1 < p.2} ≤ #(W.{u} × W.{u}) := mk_subtype_le _
        _ = #W.{u} := by rw [mk_prod, Cardinal.lift_id, mk_W, mul_eq_self (aleph0_le_aleph 2)]
  obtain ⟨e⟩ := hV
  have hcont : #(ℕ → Bool) = 𝔠 := by rw [← power_def, mk_bool, mk_nat, two_power_aleph0]
  refine ⟨(shift W).comap e, smallCard_comap e ?_, ⟨fun c => ?_⟩⟩
  · intro X hX
    let S : Set W.{u} := (fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.1) '' X ∪
      (fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.2) '' X
    have hS : #S ≤ ℵ₁ :=
      calc #S ≤ #((fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.1) '' X) +
            #((fun p : {p : W.{u} × W.{u} // p.1 < p.2} => p.1.2) '' X) := mk_union_le _ _
        _ ≤ ℵ₁ + ℵ₁ := add_le_add (mk_image_le.trans hX) (mk_image_le.trans hX)
        _ = ℵ₁ := add_eq_self (aleph0_le_aleph 1)
    have hS' : Cardinal.lift.{0} #S ≤ Cardinal.lift.{u} #(ℕ → Bool) := by
      rw [Cardinal.lift_uzero, hcont, lift_continuum]
      exact hS.trans aleph_one_le_continuum
    obtain ⟨emb⟩ := lift_mk_le'.1 hS'
    classical
    let f : W.{u} → ℕ → Bool := fun x => if h : x ∈ S then emb ⟨x, h⟩ else fun _ => false
    have hf : Set.InjOn f S := by
      intro x hx y hy hxy
      simp only [f, hx, hy, dite_true] at hxy
      exact congrArg Subtype.val (emb.injective hxy)
    exact ((shift_colorableOn S f hf).mono_set
      (fun p hp => ⟨Or.inl ⟨p, hp, rfl⟩, Or.inr ⟨p, hp, rfl⟩⟩)).toNat
  · have hinj := shift_lower (coloringOfComap e c)
    have h1 := lift_mk_le_lift_mk_of_injective hinj
    rw [Cardinal.lift_uzero, mk_set, mk_nat, two_power_aleph0, hCH, mk_W] at h1
    simp only [lift_aleph, Ordinal.lift_one] at h1
    exact absurd h1 (not_le.2 aleph1_lt_aleph2)
end Erdos919
