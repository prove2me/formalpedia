-- Prove2me | solution 1 for BrinSquier.compact_closure_supp_commutator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T22:38:22.975189+00:00
-- url     : https://prove2.me/submissions/e70c3e31-710c-4a3f-a619-5a058fad1d61

import Definitions.Def_BrinSquier
import Mathlib

namespace BS_aux
open BrinSquier

lemma inv_formula_bot {f : ℝ ≃o ℝ} {b M : ℝ} (h : ∀ y < M, f y = 1 * y + b) :
    ∀ w < M + b, f⁻¹ w = w - b := by
  intro w hw
  have h1 : f (w - b) = w := by rw [h _ (by linarith)]; ring
  exact f.injective (by rw [RelIso.apply_inv_self, h1])

lemma inv_formula_top {f : ℝ ≃o ℝ} {b M : ℝ} (h : ∀ y > M, f y = 1 * y + b) :
    ∀ w > M + b, f⁻¹ w = w - b := by
  intro w hw
  have h1 : f (w - b) = w := by rw [h _ (by linarith)]; ring
  exact f.injective (by rw [RelIso.apply_inv_self, h1])

/-- Two maps that are translations near `-∞` have an identity commutator there. -/
lemma commutator_id_bot {f g : ℝ ≃o ℝ} (hfb : SlopeAtBot f 1) (hgb : SlopeAtBot g 1) :
    ∃ M : ℝ, ∀ y < M, (f * g * f⁻¹ * g⁻¹) y = y := by
  obtain ⟨bf, Mf, hf⟩ := hfb
  obtain ⟨bg, Mg, hg⟩ := hgb
  refine ⟨min (min (Mg + bg) (Mf + bf + bg)) (min (Mg + bg + bf) (Mf + bf)), fun y hy => ?_⟩
  have b1 : y < Mg + bg := lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_left _ _))
  have b2 : y < Mf + bf + bg := lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_right _ _))
  have b3 : y < Mg + bg + bf := lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_left _ _))
  have b4 : y < Mf + bf := lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_right _ _))
  show f (g (f⁻¹ (g⁻¹ y))) = y
  rw [inv_formula_bot hg y b1, inv_formula_bot hf _ (by linarith),
    hg _ (by linarith), hf _ (by linarith)]
  ring

lemma commutator_id_top {f g : ℝ ≃o ℝ} (hft : SlopeAtTop f 1) (hgt : SlopeAtTop g 1) :
    ∃ M : ℝ, ∀ y > M, (f * g * f⁻¹ * g⁻¹) y = y := by
  obtain ⟨bf, Mf, hf⟩ := hft
  obtain ⟨bg, Mg, hg⟩ := hgt
  refine ⟨max (max (Mg + bg) (Mf + bf + bg)) (max (Mg + bg + bf) (Mf + bf)), fun y hy => ?_⟩
  have b1 : y > Mg + bg := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hy
  have b2 : y > Mf + bf + bg := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hy
  have b3 : y > Mg + bg + bf := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hy
  have b4 : y > Mf + bf := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hy
  show f (g (f⁻¹ (g⁻¹ y))) = y
  rw [inv_formula_top hg y b1, inv_formula_top hf _ (by linarith),
    hg _ (by linarith), hf _ (by linarith)]
  ring

end BS_aux

open BS_aux BrinSquier in
theorem solution {f g : ℝ ≃o ℝ}
    (hfb : SlopeAtBot f 1) (hft : SlopeAtTop f 1)
    (hgb : SlopeAtBot g 1) (hgt : SlopeAtTop g 1) :
    IsCompact (closure (supp (f * g * f⁻¹ * g⁻¹))) := by
  obtain ⟨Mlo, hlo⟩ := commutator_id_bot hfb hgb
  obtain ⟨Mhi, hhi⟩ := commutator_id_top hft hgt
  have hsub : supp (f * g * f⁻¹ * g⁻¹) ⊆ Set.Icc Mlo Mhi := by
    intro x hx
    constructor
    · by_contra hc
      exact hx (hlo x (not_le.mp hc))
    · by_contra hc
      exact hx (hhi x (not_le.mp hc))
  exact IsCompact.of_isClosed_subset (isCompact_Icc (a := Mlo) (b := Mhi)) isClosed_closure
    (closure_minimal hsub isClosed_Icc)
