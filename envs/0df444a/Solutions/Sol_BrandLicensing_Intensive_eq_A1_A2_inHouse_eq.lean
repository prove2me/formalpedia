-- Prove2me | solution 1 for BrandLicensing.Intensive.eq_A1_A2_inHouse_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:58:43.714571+00:00
-- url     : https://prove2.me/submissions/eac7f098-a04c-4bd8-b4d3-817707551773

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model
open BrandLicensing.Intensive

theorem solution(P : Params) (hP : P.Standing) (eC eE : ℝ) :
    IsInHouseEq P eC eE ↔ eC = eCH_cf P ∧ eE = eEH_cf P := by
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
  have gap : ∀ c e : ℝ, 0 ≤ c → 0 ≤ e → piInHouse P cs es - piInHouse P c e = ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) ^ 2 - P.ρ * (1 - P.α) * (c - cs) * (e - es) + (P.θ - P.ρ / 2) * (e - es) ^ 2) / 2 ∧ 0 ≤ ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) ^ 2 - P.ρ * (1 - P.α) * (c - cs) * (e - es) + (P.θ - P.ρ / 2) * (e - es) ^ 2) := by
    intro c e hc he
    unfold piInHouse piM vC; rw [hpos c e hc he, hpos cs es hcs hes]
    have hX : Xi P = P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ := rfl
    have hQ : 0 ≤ (1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) ^ 2 - P.ρ * (1 - P.α) * (c - cs) * (e - es) + (P.θ - P.ρ / 2) * (e - es) ^ 2 := by
      have h1 : 0 ≤ (1 - P.ρ * (1 - P.α) ^ 2 / 2) * ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) ^ 2 - P.ρ * (1 - P.α) * (c - cs) * (e - es) + (P.θ - P.ρ / 2) * (e - es) ^ 2) := by
        nlinarith [sq_nonneg ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) - P.ρ * (1 - P.α) * (e - es) / 2), mul_nonneg hXi.le (sq_nonneg (e - es))]
      exact (mul_nonneg_iff_of_pos_left hA).mp h1
    have hid : (P.μ * (cs + P.lam * (1 - P.α) * (es - P.ε)) + P.ρ * (es + (1 - P.α) * cs) ^ 2 / 4 - P.θ * es ^ 2 / 2 - cs ^ 2 / 2) - (P.μ * (c + P.lam * (1 - P.α) * (e - P.ε)) + P.ρ * (e + (1 - P.α) * c) ^ 2 / 4 - P.θ * e ^ 2 / 2 - c ^ 2 / 2) = ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (c - cs) ^ 2 - P.ρ * (1 - P.α) * (c - cs) * (e - es) + (P.θ - P.ρ / 2) * (e - es) ^ 2) / 2 - (P.μ + P.ρ * (1 - P.α) * (es + (1 - P.α) * cs) / 2 - cs) * (c - cs) - (P.μ * P.lam * (1 - P.α) + P.ρ * (es + (1 - P.α) * cs) / 2 - P.θ * es) * (e - es) := by ring
    rw [F1, F2] at hid
    exact ⟨by linarith, hQ⟩
  have key : ∀ c e : ℝ, 0 ≤ c → 0 ≤ e → piInHouse P c e ≤ piInHouse P cs es := by
    intro c e hc he; obtain ⟨g1, g2⟩ := gap c e hc he; linarith
  constructor
  · rintro ⟨hc, he, hmax⟩
    have h1 := hmax cs hcs es hes
    obtain ⟨g1, g2⟩ := gap eC eE hc he
    have hQ0 : (1 - P.ρ * (1 - P.α) ^ 2 / 2) * (eC - cs) ^ 2 - P.ρ * (1 - P.α) * (eC - cs) * (eE - es) + (P.θ - P.ρ / 2) * (eE - es) ^ 2 = 0 := by linarith
    have hsq : ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (eC - cs) - P.ρ * (1 - P.α) * (eE - es) / 2) ^ 2 + Xi P / 2 * (eE - es) ^ 2 = 0 := by
      rw [hX0]; linear_combination (1 - P.ρ * (1 - P.α) ^ 2 / 2) * hQ0
    have t1 := sq_nonneg ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (eC - cs) - P.ρ * (1 - P.α) * (eE - es) / 2)
    have t2 : 0 ≤ Xi P / 2 * (eE - es) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have t3 : Xi P / 2 * (eE - es) ^ 2 = 0 := by linarith
    have hy2 : (eE - es) ^ 2 = 0 := by
      rcases mul_eq_zero.mp t3 with h0 | h0
      · linarith
      · exact h0
    have hy : eE = es := by have := pow_eq_zero_iff two_ne_zero |>.mp hy2; linarith
    have hx2 : ((1 - P.ρ * (1 - P.α) ^ 2 / 2) * (eC - cs)) ^ 2 = 0 := by
      rw [hy, sub_self] at hsq; simpa using hsq
    have hx : (1 - P.ρ * (1 - P.α) ^ 2 / 2) * (eC - cs) = 0 := pow_eq_zero_iff two_ne_zero |>.mp hx2
    rcases mul_eq_zero.mp hx with h0 | h0
    · exact absurd h0 hA.ne'
    · exact ⟨by linarith, hy⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hcs, hes, fun c hc e he => key c e hc he⟩
