-- Prove2me | solution 1 for BrandLicensing.Intensive.eq_A3_inHouse_profit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:58:38.838458+00:00
-- url     : https://prove2.me/submissions/c76a97c3-f280-4791-a11b-fcf26e4a5afe

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model
open BrandLicensing.Intensive

theorem solution(P : Params) (hP : P.Standing) (eC eE : ℝ)
    (h : IsInHouseEq P eC eE) :
    piInHouse P eC eE = piH_cf P := by
  obtain ⟨hα0, hα1, hθ, hμ, hρ0, hρ1, hl0, hl1, hε⟩ := hP
  have ha0 : 0 ≤ 1 - P.α := by linarith
  have ha1 : 1 - P.α ≤ 1 := by linarith
  have ha2 : (1 - P.α) ^ 2 ≤ 1 := by nlinarith
  have hXi : 0 < Xi P := by
    unfold Xi; nlinarith [mul_nonneg hρ0 (sq_nonneg (1 - P.α)), mul_le_mul_of_nonneg_left ha2 hρ0]
  have hcs : 0 ≤ eCH_cf P := by
    unfold eCH_cf; apply div_nonneg _ hXi.le
    apply mul_nonneg hμ.le; nlinarith [mul_nonneg hl0 (sq_nonneg (1 - P.α)), mul_le_mul_of_nonneg_left (mul_le_one₀ hl1 (sq_nonneg _) ha2) hρ0]
  have hes : 0 ≤ eEH_cf P := by
    unfold eEH_cf; apply div_nonneg _ hXi.le
    apply mul_nonneg (mul_nonneg ha0 hμ.le)
    nlinarith [mul_le_mul_of_nonneg_left ha2 hρ0, mul_nonneg hl0 hρ0]
  have hpos : ∀ c e : ℝ, 0 ≤ c → 0 ≤ e → max (e + (1 - P.α) * c - 0) 0 = e + (1 - P.α) * c := by
    intro c e hc he; rw [max_eq_left]; ring; nlinarith [mul_nonneg ha0 hc]
  set cs := eCH_cf P with hcs_def
  set es := eEH_cf P with hes_def
  have hXne : Xi P ≠ 0 := hXi.ne'
  have hX0 : Xi P = P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ := rfl
  have F1 : P.μ + P.ρ * (1 - P.α) * (es + (1 - P.α) * cs) / 2 - cs = 0 := by
    rw [hcs_def, hes_def]; unfold eCH_cf eEH_cf; field_simp; rw [hX0]; ring
  have F2 : P.μ * P.lam * (1 - P.α) + P.ρ * (es + (1 - P.α) * cs) / 2 - P.θ * es = 0 := by
    rw [hcs_def, hes_def]; unfold eCH_cf eEH_cf; field_simp; rw [hX0]; ring
  have hval : piInHouse P cs es = piH_cf P := by
    unfold piInHouse piM vC; rw [hpos cs es hcs hes]
    rw [hcs_def, hes_def]; unfold eCH_cf eEH_cf piH_cf; field_simp; rw [hX0]; ring
  have hA : 0 < 1 - P.ρ * (1 - P.α) ^ 2 / 2 := by nlinarith [mul_le_mul_of_nonneg_left ha2 hρ0]
  have key : ∀ c e : ℝ, 0 ≤ c → 0 ≤ e → piInHouse P c e ≤ piInHouse P cs es := by
    intro c e hc he
    unfold piInHouse piM vC; rw [hpos c e hc he, hpos cs es hcs hes]
    have hX : Xi P = P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ := rfl
    have hQ : 0 ≤ (1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) ^ 2 - P.ρ * (1 - P.α) * (c - cs) * (e - es) + (P.θ - P.ρ / 2) * (e - es) ^ 2 := by
      have h1 : 0 ≤ (1 - P.ρ * (1 - P.α) ^ 2 / 2) * ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) ^ 2 - P.ρ * (1 - P.α) * (c - cs) * (e - es) + (P.θ - P.ρ / 2) * (e - es) ^ 2) := by
        nlinarith [sq_nonneg ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) - P.ρ * (1 - P.α) * (e - es) / 2), mul_nonneg hXi.le (sq_nonneg (e - es))]
      exact (mul_nonneg_iff_of_pos_left hA).mp h1
    have hid : (P.μ * (cs + P.lam * (1 - P.α) * (es - P.ε)) + P.ρ * (es + (1 - P.α) * cs) ^ 2 / 4 - P.θ * es ^ 2 / 2 - cs ^ 2 / 2) - (P.μ * (c + P.lam * (1 - P.α) * (e - P.ε)) + P.ρ * (e + (1 - P.α) * c) ^ 2 / 4 - P.θ * e ^ 2 / 2 - c ^ 2 / 2) = ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) ^ 2 - P.ρ * (1 - P.α) * (c - cs) * (e - es) + (P.θ - P.ρ / 2) * (e - es) ^ 2) / 2 - (P.μ + P.ρ * (1 - P.α) * (es + (1 - P.α) * cs) / 2 - cs) * (c - cs) - (P.μ * P.lam * (1 - P.α) + P.ρ * (es + (1 - P.α) * cs) / 2 - P.θ * es) * (e - es) := by ring
    rw [F1, F2] at hid
    linarith
  apply le_antisymm
  · rw [← hval]; exact key eC eE h.1 h.2.1
  · rw [← hval]; exact h.2.2 cs hcs es hes
