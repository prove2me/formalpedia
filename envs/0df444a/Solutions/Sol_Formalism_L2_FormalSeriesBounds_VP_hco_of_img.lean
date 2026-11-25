-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.hco_of_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:14.876741+00:00
-- url     : https://prove2.me/submissions/c3892f45-5055-4858-a078-85fb91a4e464

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
open Formalism.L2.FormalSeriesBounds.VP
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {ι : Type} (cp : ι → Fin n) (uv : ι → Fin dd → C) (ℓ : ι)
    (co : Fin N × WVO (IS I0) → C)
    (h : ∃ ρ col, pl (ρ, col) = cp ℓ ∧ (∀ ρ' w, ρ' ≠ ρ → co (ρ', w) = 0) ∧
      (fun x : Fin 2 × Fin dd => if x.1 = col then uv ℓ x.2 else 0) =
        ∑ w : WVO (IS I0), co (ρ, w) • (Y.rawSelf (p w.1)).u w.2.1 w.2.2) (b : Fin n) (i : Fin dd) :
    ∑ x, co x * MS Y p pl x (b, i) = if b = cp ℓ then uv ℓ i else 0 := by
  obtain ⟨ρ, col, hpl, hco0, hvec⟩ := h
  have key : ∀ c : Fin 2, (∑ x : Fin N × WVO (IS I0),
      co x * (if pl (x.1, c) = b then uS Y p x.2 (c, i) else 0)) =
      if pl (ρ, c) = b then (if c = col then uv ℓ i else 0) else 0 := by
    intro c
    rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ
      (fun ρ' _ hρ' => Finset.sum_eq_zero fun w _ => by simp [hco0 ρ' w hρ']) (by simp)]
    by_cases hb' : pl (ρ, c) = b
    · have h1 := congrFun hvec (c, i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      simp only [hb', if_true]
      rw [h1]
      rfl
    · simp [hb']
  simp only [MS, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [key]
  rw [Finset.sum_eq_single col (fun c _ hc => by simp [hc]) (by simp)]
  simp only [if_true]
  by_cases hb : b = cp ℓ
  · simp [hb, hpl]
  · have h2 : pl (ρ, col) ≠ b := fun h' => hb (h'.symm.trans hpl)
    simp [h2, hb]
end Formalism.L2.FormalSeriesBounds.VP
