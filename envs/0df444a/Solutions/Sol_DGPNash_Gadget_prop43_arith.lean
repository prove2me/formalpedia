-- Prove2me | solution 1 for DGPNash.Gadget.prop43_arith
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T12:30:21.573314+00:00
-- url     : https://prove2.me/submissions/ae3160ff-dd8d-4025-9c7b-157d4e42c677

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame
import Definitions.Def_DGPNash_Gadget_BasicGadgets

set_option autoImplicit false

namespace P85342506

open DGPNash.Gadget

def e : (ArithRole → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 × Fin 2 where
  toFun s := (s .v1, s .v2, s .v3, s .w)
  invFun p := fun r => match r with
    | .v1 => p.1
    | .v2 => p.2.1
    | .v3 => p.2.2.1
    | .w => p.2.2.2
  left_inv s := by funext r; cases r <;> rfl
  right_inv p := rfl

lemma univ_eq : (Finset.univ : Finset ArithRole) = {ArithRole.v1, ArithRole.v2, ArithRole.v3, ArithRole.w} := by
  ext x; cases x <;> simp

lemma sum_eq (f : (ArithRole → Fin 2) → ℝ) :
    ∑ s, f s = ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2, f (e.symm (a, b, c, d)) := by
  rw [Fintype.sum_equiv e f (fun p => f (e.symm p)) (fun x => by simp)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

lemma prod_eq (f : ArithRole → ℝ) : ∏ i, f i = f .v1 * (f .v2 * (f .v3 * f .w)) := by
  rw [univ_eq, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_pair (by decide)]

lemma eapp_v1 (a b c d : Fin 2) : e.symm (a, b, c, d) .v1 = a := rfl
lemma eapp_v2 (a b c d : Fin 2) : e.symm (a, b, c, d) .v2 = b := rfl
lemma eapp_v3 (a b c d : Fin 2) : e.symm (a, b, c, d) .v3 = c := rfl
lemma eapp_w (a b c d : Fin 2) : e.symm (a, b, c, d) .w = d := rfl

lemma pp (u : ArithRole → (ArithRole → Fin 2) → ℝ) (τ : ArithRole → Fin 2 → ℝ) (i : ArithRole) :
    AGT.expectedPayoff (S := fun _ => Fin 2) u τ i =
      ∑ a : Fin 2, ∑ b : Fin 2, ∑ c : Fin 2, ∑ d : Fin 2,
        τ .v1 a * (τ .v2 b * (τ .v3 c * τ .w d)) * u i (e.symm (a, b, c, d)) := by
  unfold AGT.expectedPayoff AGT.profileProb
  rw [sum_eq]
  simp only [prod_eq, eapp_v1, eapp_v2, eapp_v3, eapp_w]

lemma pay_v3_0 (α β γ : ℝ) (σ : ArithRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (arithPayoff α β γ) σ .v3 0 =
      (σ .v1 0 + σ .v1 1) * (σ .v2 0 + σ .v2 1) * σ .w 1 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, arithPayoff, ind, eapp_v1, eapp_v2, eapp_v3, eapp_w]
  ring

lemma pay_v3_1 (α β γ : ℝ) (σ : ArithRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (arithPayoff α β γ) σ .v3 1 =
      (σ .v1 0 + σ .v1 1) * (σ .v2 0 + σ .v2 1) * σ .w 0 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, arithPayoff, ind, eapp_v1, eapp_v2, eapp_v3, eapp_w]
  ring

lemma pay_w_0 (α β γ : ℝ) (σ : ArithRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (arithPayoff α β γ) σ .w 0 =
      (σ .v3 0 + σ .v3 1) * (β * (σ .v1 0 * σ .v2 1) + α * (σ .v1 1 * σ .v2 0)
        + (α + β + γ) * (σ .v1 1 * σ .v2 1)) := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, arithPayoff, ind, eapp_v1, eapp_v2, eapp_v3, eapp_w]
  ring

lemma pay_w_1 (α β γ : ℝ) (σ : ArithRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (arithPayoff α β γ) σ .w 1 =
      (σ .v1 0 + σ .v1 1) * (σ .v2 0 + σ .v2 1) * σ .v3 1 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, arithPayoff, ind, eapp_v1, eapp_v2, eapp_v3, eapp_w]
  ring

theorem main (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1) (σ : ArithRole → Fin 2 → ℝ)
    (hσ : IsEpsNash (S := fun _ => Fin 2) (arithPayoff α β γ) ε σ) :
    |σ .v3 1 - min (α * σ .v1 1 + β * σ .v2 1 + γ * σ .v1 1 * σ .v2 1) 1| ≤ ε := by
  obtain ⟨hmix, hws⟩ := hσ
  obtain ⟨hw0, hws1⟩ := hmix .w
  obtain ⟨hv10, hv1s⟩ := hmix .v1
  obtain ⟨hv20, hv2s⟩ := hmix .v2
  obtain ⟨hv30, hv3s⟩ := hmix .v3
  simp only [Fin.sum_univ_two] at hws1 hv1s hv2s hv3s
  have nw0 := hw0 0; have nw1 := hw0 1
  have na0 := hv10 0; have na1 := hv10 1
  have nb0 := hv20 0; have nb1 := hv20 1
  have nc0 := hv30 0; have nc1 := hv30 1
  have Hw01 := hws .w 0 1
  have Hw10 := hws .w 1 0
  have Hv01 := hws .v3 0 1
  have Hv10 := hws .v3 1 0
  rw [pay_w_0, pay_w_1] at Hw01 Hw10
  rw [pay_v3_0, pay_v3_1] at Hv01 Hv10
  rw [hv1s, hv2s, hv3s] at Hw01 Hw10
  rw [hv1s, hv2s] at Hv01 Hv10
  have hX : β * (σ .v1 0 * σ .v2 1) + α * (σ .v1 1 * σ .v2 0)
        + (α + β + γ) * (σ .v1 1 * σ .v2 1)
      = α * σ .v1 1 + β * σ .v2 1 + γ * σ .v1 1 * σ .v2 1 := by
    have e1 : σ .v1 0 = 1 - σ .v1 1 := by linarith
    have e2 : σ .v2 0 = 1 - σ .v2 1 := by linarith
    rw [e1, e2]; ring
  rw [hX] at Hw01 Hw10
  have hx : 0 ≤ α * σ .v1 1 + β * σ .v2 1 + γ * σ .v1 1 * σ .v2 1 := by
    have := mul_nonneg hα na1
    have := mul_nonneg hβ nb1
    have := mul_nonneg (mul_nonneg hγ na1) nb1
    linarith
  rw [abs_le]
  constructor
  · by_contra h
    rw [not_le] at h
    have hm := min_le_left (α * σ .v1 1 + β * σ .v2 1 + γ * σ .v1 1 * σ .v2 1) 1
    have hm1 := min_le_right (α * σ .v1 1 + β * σ .v2 1 + γ * σ .v1 1 * σ .v2 1) 1
    have h1 : σ .w 1 = 0 := Hw01 (by linarith)
    have h2 : σ .v3 0 = 0 := Hv10 (by rw [h1]; linarith)
    linarith
  · by_contra h
    rw [not_le] at h
    rcases min_choice (α * σ .v1 1 + β * σ .v2 1 + γ * σ .v1 1 * σ .v2 1) 1 with hm | hm <;>
      rw [hm] at h
    · have h1 : σ .w 0 = 0 := Hw10 (by linarith)
      have h2 : σ .v3 1 = 0 := Hv01 (by rw [h1]; linarith)
      linarith
    · linarith

end P85342506

open DGPNash.Gadget in
theorem solution (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1) (σ : ArithRole → Fin 2 → ℝ)
    (hσ : IsEpsNash (S := fun _ => Fin 2) (arithPayoff α β γ) ε σ) :
    |σ .v3 1 - min (α * σ .v1 1 + β * σ .v2 1 + γ * σ .v1 1 * σ .v2 1) 1| ≤ ε := by
  exact P85342506.main α β γ hα hβ hγ ε hε0 hε σ hσ
