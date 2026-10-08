-- Prove2me | solution 1 for DGPNash.Gadget.prop45_const
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:32:14.989254+00:00
-- url     : https://prove2.me/submissions/41e2a9a6-c33f-4150-a90b-653a2b0c8eba

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame
import Definitions.Def_DGPNash_Gadget_BasicGadgets

set_option autoImplicit false

namespace B3d500b7

open DGPNash.Gadget

def e : (ConstRole → Fin 2) ≃ Fin 2 × Fin 2 where
  toFun s := (s .w, s .v1)
  invFun p := fun r => match r with
    | .w => p.1
    | .v1 => p.2
  left_inv s := by funext r; cases r <;> rfl
  right_inv p := rfl

lemma univ_eq : (Finset.univ : Finset ConstRole) = {ConstRole.w, ConstRole.v1} := by
  ext x; cases x <;> simp

lemma sum_eq (f : (ConstRole → Fin 2) → ℝ) :
    ∑ s, f s = ∑ a : Fin 2, ∑ b : Fin 2, f (e.symm (a, b)) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ (fun x => by simp)

lemma prod_eq (f : ConstRole → ℝ) : ∏ i, f i = f .w * f .v1 := by
  rw [univ_eq, Finset.prod_pair (by decide)]

lemma eapp_w (a b : Fin 2) : e.symm (a, b) .w = a := rfl
lemma eapp_v1 (a b : Fin 2) : e.symm (a, b) .v1 = b := rfl

lemma pp (u : ConstRole → (ConstRole → Fin 2) → ℝ) (τ : ConstRole → Fin 2 → ℝ) (i : ConstRole) :
    AGT.expectedPayoff (S := fun _ => Fin 2) u τ i =
      ∑ a : Fin 2, ∑ b : Fin 2, τ .w a * τ .v1 b * u i (e.symm (a, b)) := by
  unfold AGT.expectedPayoff AGT.profileProb
  rw [sum_eq]
  simp only [prod_eq, eapp_w, eapp_v1]

lemma pay_v1_0 (α : ℝ) (σ : ConstRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (constPayoff α) σ .v1 0 = σ .w 1 * 1 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, constPayoff, ind, eapp_w, eapp_v1]

lemma pay_v1_1 (α : ℝ) (σ : ConstRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (constPayoff α) σ .v1 1 = σ .w 0 * 1 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, constPayoff, ind, eapp_w, eapp_v1]

lemma pay_w_0 (α : ℝ) (σ : ConstRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (constPayoff α) σ .w 0 =
      (σ .v1 0 + σ .v1 1) * α := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, constPayoff, ind, eapp_w, eapp_v1]
  ring

lemma pay_w_1 (α : ℝ) (σ : ConstRole → Fin 2 → ℝ) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) (constPayoff α) σ .w 1 = σ .v1 1 * 1 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, constPayoff, ind, eapp_w, eapp_v1]

theorem main (α : ℝ) (hα : 0 ≤ α) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (σ : ConstRole → Fin 2 → ℝ) (hσ : IsEpsNash (S := fun _ => Fin 2) (constPayoff α) ε σ) :
    |σ .v1 1 - min α 1| ≤ ε := by
  obtain ⟨hmix, hws⟩ := hσ
  obtain ⟨hw0, hws1⟩ := hmix .w
  obtain ⟨hv0, hvs1⟩ := hmix .v1
  simp only [Fin.sum_univ_two] at hws1 hvs1
  have nw0 := hw0 0; have nw1 := hw0 1; have nv0 := hv0 0; have nv1 := hv0 1
  have Hw01 := hws .w 0 1
  have Hw10 := hws .w 1 0
  have Hv01 := hws .v1 0 1
  have Hv10 := hws .v1 1 0
  rw [pay_w_0, pay_w_1] at Hw01 Hw10
  rw [pay_v1_0, pay_v1_1] at Hv01 Hv10
  rw [hvs1] at Hw01 Hw10
  rw [abs_le]
  constructor
  · by_contra h
    rw [not_le] at h
    have hm : min α 1 ≤ α := min_le_left _ _
    have hm1 : min α 1 ≤ 1 := min_le_right _ _
    have h1 : σ .w 1 = 0 := Hw01 (by linarith)
    have h2 : σ .v1 0 = 0 := Hv10 (by rw [h1]; linarith)
    linarith
  · by_contra h
    rw [not_le] at h
    rcases min_choice α 1 with hm | hm <;> rw [hm] at h
    · have h1 : σ .w 0 = 0 := Hw10 (by linarith)
      have h2 : σ .v1 1 = 0 := Hv01 (by rw [h1]; linarith)
      linarith
    · linarith

end B3d500b7

open DGPNash.Gadget in
theorem solution (α : ℝ) (hα : 0 ≤ α) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε < 1)
    (σ : ConstRole → Fin 2 → ℝ) (hσ : IsEpsNash (S := fun _ => Fin 2) (constPayoff α) ε σ) :
    |σ .v1 1 - min α 1| ≤ ε := by
  exact B3d500b7.main α hα ε hε0 hε σ hσ
