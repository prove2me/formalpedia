-- Prove2me | solution 1 for DGPNash.Gadget.prop42_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:55:16.891589+00:00
-- url     : https://prove2.me/submissions/2f0b2097-a2f5-4411-a3c6-f0d9bcd0aa02

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame
import Definitions.Def_DGPNash_Gadget_BasicGadgets

set_option autoImplicit false

namespace B9d6bebb

open DGPNash.Gadget

def e : (MulRole → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 where
  toFun s := (s .v1, s .v2, s .w)
  invFun p := fun r => match r with
    | .v1 => p.1
    | .v2 => p.2.1
    | .w => p.2.2
  left_inv s := by funext r; cases r <;> rfl
  right_inv p := rfl

lemma univ_eq : (Finset.univ : Finset MulRole) = {MulRole.v1, MulRole.v2, MulRole.w} := by
  ext x; cases x <;> simp

lemma sum_eq (f : (MulRole → Fin 2) → ℝ) :
    ∑ s, f s = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, f (e.symm (a, b, c)) := by
  rw [Fintype.sum_equiv e f (fun p => f (e.symm p)) (fun x => by simp)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

lemma prod_eq (f : MulRole → ℝ) : ∏ i, f i = f .v1 * (f .v2 * f .w) := by
  rw [univ_eq, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]

lemma eapp_v1 (a b c : Fin 2) : e.symm (a, b, c) .v1 = a := rfl
lemma eapp_v2 (a b c : Fin 2) : e.symm (a, b, c) .v2 = b := rfl
lemma eapp_w (a b c : Fin 2) : e.symm (a, b, c) .w = c := rfl

lemma pp (u : MulRole → (MulRole → Fin 2) → ℝ) (τ : MulRole → Fin 2 → ℝ) (i : MulRole) :
    AGT.expectedPayoff (S := fun _ => Fin 2) u τ i =
      ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2,
        τ .v1 a * (τ .v2 b * τ .w c) * u i (e.symm (a, b, c)) := by
  unfold AGT.expectedPayoff AGT.profileProb
  rw [sum_eq]
  simp only [prod_eq, eapp_v1, eapp_v2, eapp_w]

lemma pay_v2_0 (α : ℝ) (σ : MulRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (mulPayoff α) σ .v2 0 =
      (σ .v1 0 + σ .v1 1) * σ .w 1 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, mulPayoff, ind, eapp_v1, eapp_v2, eapp_w]
  ring

lemma pay_v2_1 (α : ℝ) (σ : MulRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (mulPayoff α) σ .v2 1 =
      (σ .v1 0 + σ .v1 1) * σ .w 0 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, mulPayoff, ind, eapp_v1, eapp_v2, eapp_w]
  ring

lemma pay_w_0 (α : ℝ) (σ : MulRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (mulPayoff α) σ .w 0 =
      σ .v1 1 * (σ .v2 0 + σ .v2 1) * α := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, mulPayoff, ind, eapp_v1, eapp_v2, eapp_w]
  ring

lemma pay_w_1 (α : ℝ) (σ : MulRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (mulPayoff α) σ .w 1 =
      (σ .v1 0 + σ .v1 1) * σ .v2 1 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, mulPayoff, ind, eapp_v1, eapp_v2, eapp_w]
  ring

theorem main (α : ℝ) (hα : 0 ≤ α) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (σ : MulRole → Fin 2 → ℝ) (hσ : IsEpsNash (S := fun _ => Fin 2) (mulPayoff α) ε σ) :
    |σ .v2 1 - min (α * σ .v1 1) 1| ≤ ε := by
  obtain ⟨hmix, hws⟩ := hσ
  obtain ⟨hw0, hws1⟩ := hmix .w
  obtain ⟨hv10, hv1s⟩ := hmix .v1
  obtain ⟨hv20, hv2s⟩ := hmix .v2
  simp only [Fin.sum_univ_two] at hws1 hv1s hv2s
  have nw0 := hw0 0; have nw1 := hw0 1
  have na0 := hv10 0; have na1 := hv10 1
  have nb0 := hv20 0; have nb1 := hv20 1
  have Hw01 := hws .w 0 1
  have Hw10 := hws .w 1 0
  have Hv01 := hws .v2 0 1
  have Hv10 := hws .v2 1 0
  rw [pay_w_0, pay_w_1] at Hw01 Hw10
  rw [pay_v2_0, pay_v2_1] at Hv01 Hv10
  rw [hv1s, hv2s] at Hw01 Hw10
  rw [hv1s] at Hv01 Hv10
  have hx : 0 ≤ α * σ .v1 1 := mul_nonneg hα na1
  rw [abs_le]
  constructor
  · by_contra h
    rw [not_le] at h
    have hm : min (α * σ .v1 1) 1 ≤ α * σ .v1 1 := min_le_left _ _
    have hm1 : min (α * σ .v1 1) 1 ≤ 1 := min_le_right _ _
    have h1 : σ .w 1 = 0 := Hw01 (by nlinarith)
    have h2 : σ .v2 0 = 0 := Hv10 (by rw [h1]; linarith)
    linarith
  · by_contra h
    rw [not_le] at h
    rcases min_choice (α * σ .v1 1) 1 with hm | hm <;> rw [hm] at h
    · have h1 : σ .w 0 = 0 := Hw10 (by nlinarith)
      have h2 : σ .v2 1 = 0 := Hv01 (by rw [h1]; linarith)
      linarith
    · linarith

end B9d6bebb

open DGPNash.Gadget in
theorem solution (α : ℝ) (hα : 0 ≤ α) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (σ : MulRole → Fin 2 → ℝ) (hσ : IsEpsNash (S := fun _ => Fin 2) (mulPayoff α) ε σ) :
    |σ .v2 1 - min (α * σ .v1 1) 1| ≤ ε := by
  exact B9d6bebb.main α hα ε hε0 hε σ hσ
