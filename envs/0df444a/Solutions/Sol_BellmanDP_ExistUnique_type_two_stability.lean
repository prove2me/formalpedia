-- Prove2me | solution 1 for BellmanDP.ExistUnique.type_two_stability
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:37:59.844016+00:00
-- url     : https://prove2.me/submissions/c077bfa2-dc19-4671-8064-d0f1f4ca383b

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes



namespace BellmanDP.ExistUnique

theorem lub_le_add_t2s {S : Type*} {A B : S → ℝ} {x y K : ℝ}
    (hx : IsLUB (Set.range A) x) (hy : IsLUB (Set.range B) y) (hK : ∀ q, A q ≤ B q + K) :
    x ≤ y + K := by
  apply hx.2
  rintro _ ⟨q, rfl⟩
  have := hy.1 ⟨q, rfl⟩
  have := hK q
  linarith

theorem abs_lub_sub_t2s {S : Type*} {A B : S → ℝ} {x y K : ℝ}
    (hx : IsLUB (Set.range A) x) (hy : IsLUB (Set.range B) y) (hK : ∀ q, |A q - B q| ≤ K) :
    |x - y| ≤ K := by
  have h1 := lub_le_add_t2s hx hy (fun q => by have := (abs_le.mp (hK q)).2; linarith)
  have h2 := lub_le_add_t2s hy hx (fun q => by have := (abs_le.mp (hK q)).1; linarith)
  rw [abs_le]; constructor <;> linarith

theorem t2s_core {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g G h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N))
    (hg : TypeTwo D g h T) (hG : TypeTwo D G h T)
    (f F : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf_bdd : BoundedOnBoundedParts D f) (hf : ∀ p ∈ D, SolvesAt g h T f p)
    (hF_bdd : BoundedOnBoundedParts D F) (hF : ∀ p ∈ D, SolvesAt G h T F p)
    (c a : ℝ) (ha : a < 1) (hh : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, |h p q| ≤ a)
    (hTc : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, ‖T p q‖ ≤ c) :
    ∀ p ∈ D, ‖p‖ ≤ c →
      |F p - f p| ≤ radialSup D (fun p q => G p q - g p q) c / (1 - a) := by
  intro p0 hp0 hc0
  set u := radialSup D (fun p q => G p q - g p q) c with hu_def
  obtain ⟨Mg, hMg⟩ := hg.g_bdd c
  obtain ⟨MG, hMG⟩ := hG.g_bdd c
  have hu : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q, |G p q - g p q| ≤ u := by
    intro p hp hpc q
    apply le_csSup
    · refine ⟨MG + Mg, ?_⟩
      rintro x ⟨p', hp', hpc', q', rfl⟩
      have := hMg p' hp' hpc' q'
      have := hMG p' hp' hpc' q'
      calc |G p' q' - g p' q'| ≤ |G p' q'| + |g p' q'| := abs_sub _ _
        _ ≤ MG + Mg := by linarith
    · exact ⟨p, hp, hpc, q, rfl⟩
  obtain ⟨Mf, hMf⟩ := hf_bdd c
  obtain ⟨MF, hMF⟩ := hF_bdd c
  set E := sSup {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ x = |F p - f p|} with hE_def
  have hbdd : BddAbove {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ x = |F p - f p|} := by
    refine ⟨MF + Mf, ?_⟩
    rintro x ⟨p', hp', hpc', rfl⟩
    have := hMf p' hp' hpc'
    have := hMF p' hp' hpc'
    calc |F p' - f p'| ≤ |F p'| + |f p'| := abs_sub _ _
      _ ≤ MF + Mf := by linarith
  have hE : ∀ p ∈ D, ‖p‖ ≤ c → |F p - f p| ≤ E := fun p hp hpc =>
    le_csSup hbdd (show |F p - f p| ∈ {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ x = |F p - f p|} from ⟨p, hp, hpc, rfl⟩)
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) (hE p0 hp0 hc0)
  have ha0 : 0 ≤ a := le_trans (abs_nonneg _) (hh p0 hp0 hc0 (Classical.arbitrary S))
  have hstep : ∀ p ∈ D, ‖p‖ ≤ c → |F p - f p| ≤ u + a * E := by
    intro p hp hpc
    apply abs_lub_sub_t2s (hF p hp) (hf p hp)
    intro q
    simp only [stageReturn]
    have h1 := hu p hp hpc q
    have h2 := hE (T p q) (hg.mapsTo p hp q) (hTc p hp hpc q)
    have h3 := hh p hp hpc q
    have h4 : |h p q * (F (T p q) - f (T p q))| ≤ a * E := by
      rw [abs_mul]; exact mul_le_mul h3 h2 (abs_nonneg _) ha0
    calc |G p q + h p q * F (T p q) - (g p q + h p q * f (T p q))|
        = |(G p q - g p q) + h p q * (F (T p q) - f (T p q))| := by ring_nf
      _ ≤ |G p q - g p q| + |h p q * (F (T p q) - f (T p q))| := abs_add_le _ _
      _ ≤ u + a * E := by linarith
  have hEle : E ≤ u + a * E := by
    apply csSup_le (⟨_, p0, hp0, hc0, rfl⟩ : Set.Nonempty {x : ℝ | ∃ p ∈ D, ‖p‖ ≤ c ∧ x = |F p - f p|})
    intro x hx
    obtain ⟨p', hp', hpc', rfl⟩ := hx
    exact hstep p' hp' hpc'
  rw [le_div_iff₀ (by linarith)]
  have := hE p0 hp0 hc0
  nlinarith

end BellmanDP.ExistUnique

open BellmanDP.ExistUnique


theorem solution {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g G h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N))
    (hg : TypeTwo D g h T) (hG : TypeTwo D G h T)
    (f F : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf_bdd : BoundedOnBoundedParts D f) (hf : ∀ p ∈ D, SolvesAt g h T f p)
    (hF_bdd : BoundedOnBoundedParts D F) (hF : ∀ p ∈ D, SolvesAt G h T F p)
    (c a : ℝ) (ha : a < 1) (hh : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, |h p q| ≤ a)
    (hTc : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, ‖T p q‖ ≤ c) :
    ∀ p ∈ D, ‖p‖ ≤ c →
      |F p - f p| ≤ radialSup D (fun p q => G p q - g p q) c / (1 - a) := by
  exact t2s_core D g G h T hg hG f F hf_bdd hf hF_bdd hF c a ha hh hTc
