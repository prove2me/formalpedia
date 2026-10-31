-- Prove2me | solution 1 for FramingFulfillment.RFF.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:06:59.098925+00:00
-- url     : https://prove2.me/submissions/2c3843f9-2e6e-4ce1-84cb-1dd305d11ad0

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model
import Theorems.Thm_FramingFulfillment_RFF_lemma_2

open FramingFulfillment.RFF Finset

theorem solution (P : Inst) (hP : P.Standing) (j : Fin P.J) (x : Fin P.I → Fin P.R → ℝ)
    (h10a : ∀ r, ∑ i, x i r ≤ (P.Q r : ℝ)) (h10b : ∀ i, ∑ r, x i r = 1)
    (h10e : ∀ i r, 0 ≤ x i r ∧ x i r ≤ 1) (d : FramingDecomp x) :
    (∑ φ ∈ P.Omega, P.rho j d φ = 1) ∧
    (∀ i, ∑ φ ∈ P.Omega, P.rho j d φ * P.thetaPhi j φ i = P.thetaX j x i) ∧
    (∀ i, ∑ φ ∈ P.Omega, P.rho j d φ * P.revPhi j φ i = P.revX j x i) := by
  classical
  have L2 := (FramingFulfillment.RFF.lemma_2 P hP x h10a h10b h10e).2
  obtain ⟨-, -, -, -, -, -, hvpos, hv0, -, -⟩ := hP
  have hvnn : ∀ i r, 0 ≤ P.v i j r := by
    intro i r
    by_cases h : r = P.noDisp
    · rw [h, hv0]
    · exact (hvpos i j r h).le
  obtain ⟨hα, hαsum, hBl, hBrep⟩ := d.isDecomp
  -- the assignment of each integral matrix
  have hex : ∀ l, ∃ φ : Fin P.I → Fin P.R,
      (∀ ψ : Fin P.I → Fin P.R,
        (∀ i r, ψ i = r ↔ d.B l (Fin.castAdd (Itil x) i) r = 1) ↔ ψ = φ) ∧ φ ∈ P.Omega := by
    intro l
    obtain ⟨⟨φ, hφ, huniq⟩, hmem⟩ := L2 (d.B l) (hBl l).1 (hBl l).2
    exact ⟨φ, fun ψ => ⟨fun h => huniq ψ h, fun h => h ▸ hφ⟩, hmem φ hφ⟩
  choose φl hφl hφlm using hex
  have hBφ : ∀ l i r, d.B l (Fin.castAdd (Itil x) i) r = if φl l i = r then 1 else 0 := by
    intro l i r
    have hc := (hφl l (φl l)).2 rfl
    split_ifs with h
    · exact (hc i r).1 h
    · exact ((hBl l).1 _ r).resolve_right (fun h' => h ((hc i r).2 h'))
  -- general sum formula
  have hG : ∀ G : (Fin P.I → Fin P.R) → ℝ,
      (∑ φ ∈ P.Omega, rhoTil d φ * G φ) = ∑ l, d.α l * G (φl l) := by
    intro G
    simp only [rhoTil, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single (φl l)]
    · rw [if_pos ((hφl l (φl l)).2 rfl)]
    · intro b _ hb
      rw [if_neg (fun h => hb ((hφl l b).1 h)), zero_mul]
    · intro h; exact absurd (hφlm l) h
  -- linear functionals of a coordinate
  have hlin : ∀ (i : Fin P.I) (h : Fin P.R → ℝ),
      (∑ φ ∈ P.Omega, rhoTil d φ * h (φ i)) = ∑ r, x i r * h r := by
    intro i h
    rw [hG (fun φ => h (φ i))]
    have : ∀ r, x i r = ∑ l, d.α l * (if φl l i = r then 1 else 0) := by
      intro r
      have := hBrep (Fin.castAdd (Itil x) i) r
      simp only [Bmat, Fin.addCases_left] at this
      rw [this]; simp_rw [hBφ]
    simp_rw [this, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single (φl l i)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have h1 : (∑ φ ∈ P.Omega, rhoTil d φ) = 1 := by
    have := hG (fun _ => 1); simp only [mul_one] at this; rw [this, hαsum]
  -- denominator
  set Den := 1 + ∑ l, ∑ r, P.v l j r * x l r with hDen
  have hden_eq : (1 + ∑ φ' ∈ P.Omega, rhoTil d φ' * ∑ i, P.vPhi j φ' i) = Den := by
    rw [hDen]; congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (hlin i (fun r => P.v i j r)).trans ?_
    refine Finset.sum_congr rfl fun r _ => ?_; ring
  have hDpos : 0 < Den := by
    have : 0 ≤ ∑ l, ∑ r, P.v l j r * x l r :=
      Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun r _ =>
        mul_nonneg (hvnn l r) (h10e l r).1
    linarith
  have hVpos : ∀ φ : Fin P.I → Fin P.R, 0 < 1 + ∑ k, P.vPhi j φ k := by
    intro φ
    have : 0 ≤ ∑ k, P.vPhi j φ k := Finset.sum_nonneg fun k _ => hvnn k (φ k)
    linarith
  have hrho : ∀ φ ∈ P.Omega, P.rho j d φ = rhoTil d φ * (1 + ∑ i, P.vPhi j φ i) / Den := by
    intro φ hφ
    simp only [Inst.rho, if_pos hφ, hden_eq]
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · rw [Finset.sum_congr rfl hrho, ← Finset.sum_div]
    have : (∑ φ ∈ P.Omega, rhoTil d φ * (1 + ∑ i, P.vPhi j φ i)) =
        (∑ φ ∈ P.Omega, rhoTil d φ) + ∑ φ' ∈ P.Omega, rhoTil d φ' * ∑ i, P.vPhi j φ' i := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun φ _ => ?_; ring
    rw [this, h1, hden_eq, div_self hDpos.ne']
  · have : ∀ φ ∈ P.Omega, P.rho j d φ * P.thetaPhi j φ i =
        (P.lam j / Den) * (rhoTil d φ * P.v i j (φ i)) := by
      intro φ hφ
      rw [hrho φ hφ]
      simp only [Inst.thetaPhi, Inst.vPhi]
      have := (hVpos φ).ne'
      simp only [Inst.vPhi] at this
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hlin i (fun r => P.v i j r)]
    simp only [Inst.thetaX, hDen]
    rw [div_mul_eq_mul_div]
    congr 2
    refine Finset.sum_congr rfl fun r _ => ?_; ring
  · have : ∀ φ ∈ P.Omega, P.rho j d φ * P.revPhi j φ i =
        (P.lam j / Den) * (rhoTil d φ * (P.v i j (φ i) * P.p i (φ i))) := by
      intro φ hφ
      rw [hrho φ hφ]
      simp only [Inst.revPhi, Inst.vPhi]
      have := (hVpos φ).ne'
      simp only [Inst.vPhi] at this
      field_simp
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum,
      hlin i (fun r => P.v i j r * P.p i r)]
    simp only [Inst.revX, hDen]
    rw [div_mul_eq_mul_div]
    congr 2
    refine Finset.sum_congr rfl fun r _ => ?_; ring
