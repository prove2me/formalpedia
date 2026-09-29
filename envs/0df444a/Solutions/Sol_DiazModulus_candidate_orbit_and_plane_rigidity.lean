-- Prove2me | solution 1 for DiazModulus.candidate_orbit_and_plane_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T14:15:27.431241+00:00
-- url     : https://prove2.me/submissions/7e5d1c32-8d82-499c-989d-e7e89b2f3a6e

import Definitions.Def_DiazModulus
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_DiazModulus_diaz_locus_dictionary
import Theorems.Thm_Diaz_orbit_of_candidate
import Theorems.Thm_Diaz_transcendental_of_candidate
import Theorems.Thm_Diaz_elliptic_axis_alignment
import Theorems.Thm_Diaz_norm_mem_iff
import Theorems.Thm_Diaz_normal_form

open Complex ComplexConjugate

-- Algebraicity over `ℚ` is unchanged by the embedding `ℝ ↪ ℂ`.
private theorem fb2_alg_ofReal {x : ℝ} : IsAlgebraic ℚ ((x : ℂ)) ↔ IsAlgebraic ℚ x :=
  isAlgebraic_algebraMap_iff (A := ℂ) (S := ℝ) (R := ℚ) Complex.ofReal_injective

-- The mathematics, with every platform input taken as an explicit hypothesis.
private theorem core
    (hdict : DiazModulus.Qbar = Diaz.Qbar ∧
      ∀ u : ℂ, DiazModulus.IsCandidate u ↔
        (u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp u) ∧ IsAlgebraic ℚ (u * conj u)))
    (horbit : ∀ {u : ℂ}, u ≠ 0 → IsAlgebraic ℚ (Complex.exp u) →
      IsAlgebraic ℚ (u * conj u) →
      (∀ v ∈ ({u, -u, conj u, -conj u} : Set ℂ),
          v ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp v) ∧ v * conj v = u * conj u)
        ∧ u ≠ -u ∧ u ≠ conj u ∧ u ≠ -conj u
        ∧ -u ≠ conj u ∧ -u ≠ -conj u ∧ conj u ≠ -conj u)
    (htrc : ∀ {u : ℂ}, u ≠ 0 → IsAlgebraic ℚ (Complex.exp u) → Transcendental ℚ u)
    (halign : ∀ {u : ℂ}, ¬ IsAlgebraic ℚ u → IsAlgebraic ℚ (u * conj u) →
      (conj u ≠ u ∧ conj u ≠ -u) ∧ ∀ γ : ℂ, IsAlgebraic ℚ γ → conj u ≠ γ * u)
    (hnorm : ∀ {K : Subfield ℂ} {t : ℂ}, Transcendental K t → t * conj t ∈ K → ∀ a b : ℚ,
      ((a : ℂ) * t + (b : ℂ) * conj t) * conj ((a : ℂ) * t + (b : ℂ) * conj t) ∈ K
        ↔ a = 0 ∨ b = 0)
    (hnf : ∀ {u : ℂ}, u ≠ 0 → (IsAlgebraic ℚ ‖u‖ ↔ IsAlgebraic ℚ (u * conj u)))
    {u : ℂ} (h : DiazModulus.IsCandidate u) :
    (∀ v ∈ ({u, -u, conj u, -conj u} : Set ℂ), DiazModulus.IsCandidate v)
      ∧ (u ≠ -u ∧ u ≠ conj u ∧ u ≠ -conj u ∧ -u ≠ conj u ∧ -u ≠ -conj u ∧ conj u ≠ -conj u)
      ∧ (∀ γ : ℂ, IsAlgebraic ℚ γ → conj u ≠ γ * u)
      ∧ (∀ a b : ℚ,
          IsAlgebraic ℚ ((‖(a : ℂ) * u + (b : ℂ) * conj u‖ : ℝ) : ℂ) ↔ (a = 0 ∨ b = 0)) := by
  obtain ⟨hu0, hexp, hrho⟩ := (hdict.2 u).1 h
  obtain ⟨horb, hd⟩ := horbit hu0 hexp hrho
  have hutr : Transcendental ℚ u := htrc hu0 hexp
  have hQalg : Algebra.IsAlgebraic ℚ (↥DiazModulus.Qbar) := hdict.1 ▸ Diaz.QbarIsAlgebraic
  have hT : Transcendental (↥DiazModulus.Qbar) u :=
    (Algebra.IsAlgebraic.transcendental_iff ℚ (↥DiazModulus.Qbar)).mp hutr
  have hQ : u * conj u ∈ DiazModulus.Qbar := DiazModulus.mem_Qbar_iff.mpr hrho
  refine ⟨?_, hd, (halign hutr hrho).2, ?_⟩
  · intro v hv
    obtain ⟨hv0, hvexp, hvn⟩ := horb v hv
    exact (hdict.2 v).2 ⟨hv0, hvexp, hvn ▸ hrho⟩
  · intro a b
    set w : ℂ := (a : ℂ) * u + (b : ℂ) * conj u with hw_def
    have key : w * conj w ∈ DiazModulus.Qbar ↔ a = 0 ∨ b = 0 := hnorm hT hQ a b
    by_cases hw0 : w = 0
    · have hz : w * conj w ∈ DiazModulus.Qbar := by
        rw [hw0]; simpa using (zero_mem DiazModulus.Qbar)
      refine ⟨fun _ => key.mp hz, fun _ => ?_⟩
      rw [hw0]
      simp [isAlgebraic_zero (R := ℚ) (A := ℂ)]
    · refine ⟨fun hna => key.mp (DiazModulus.mem_Qbar_iff.mpr ((hnf hw0).mp
        (fb2_alg_ofReal.mp hna))), fun hab => fb2_alg_ofReal.mpr ((hnf hw0).mpr
          (DiazModulus.mem_Qbar_iff.mp (key.mpr hab)))⟩


open DiazModulus in
theorem solution {u : ℂ} (h : IsCandidate u) :
    (∀ v ∈ ({u, -u, conj u, -conj u} : Set ℂ), IsCandidate v)
      ∧ (u ≠ -u ∧ u ≠ conj u ∧ u ≠ -conj u ∧ -u ≠ conj u ∧ -u ≠ -conj u ∧ conj u ≠ -conj u)
      ∧ (∀ γ : ℂ, IsAlgebraic ℚ γ → conj u ≠ γ * u)
      ∧ (∀ a b : ℚ,
          IsAlgebraic ℚ ((‖(a : ℂ) * u + (b : ℂ) * conj u‖ : ℝ) : ℂ) ↔ (a = 0 ∨ b = 0)) :=
  core diaz_locus_dictionary (fun h1 h2 h3 => Diaz.orbit_of_candidate h1 h2 h3)
    (fun h1 h2 => Diaz.transcendental_of_candidate h1 h2)
    (fun h1 h2 => Diaz.elliptic_axis_alignment h1 h2)
    (fun h1 h2 a b => Diaz.norm_mem_iff h1 h2 a b)
    (fun h1 => (Diaz.normal_form h1).1) h

