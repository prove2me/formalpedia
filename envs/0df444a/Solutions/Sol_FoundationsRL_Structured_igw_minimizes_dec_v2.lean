-- Prove2me | solution 1 for FoundationsRL.Structured.igw_minimizes_dec_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:29:09.917361+00:00
-- url     : https://prove2.me/submissions/bc0b49be-522c-4453-b979-e32a07dbd960

import Mathlib
import Definitions.Def_FoundationsRL_Structured_DEC
import Definitions.Def_FoundationsRL_Contextual_IsIGW

namespace EG88

/-- per-arm value -/
noncomputable def V {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (q : Fin A → ℝ) (a : Fin A) : ℝ :=
  fhat a - ∑ π, q π * fhat π + (1 - q a) / (4 * γ * q a)

theorem erase_sums {A : ℕ} (q g : Fin A → ℝ) (a : Fin A) :
    ∑ π ∈ Finset.univ.erase a, q π = (∑ π, q π) - q a ∧
    ∑ π ∈ Finset.univ.erase a, q π * g π = (∑ π, q π * g π) - q a * g a := by
  constructor
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]; ring
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]; ring

theorem upper {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (hγ : 0 < γ) (q : Fin A → ℝ)
    (hq : ∀ π, 0 < q π) (hs : ∑ π, q π = 1) (f : Fin A → ℝ) (a : Fin A) :
    ∑ π, q π * (f a - f π - γ * (f π - fhat π) ^ 2) ≤ V fhat γ q a := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have h1 : ∑ π ∈ Finset.univ.erase a, q π * (f a - f π - γ * (f π - fhat π) ^ 2) ≤
      ∑ π ∈ Finset.univ.erase a, (q π * (fhat a + (f a - fhat a) + 1 / (4 * γ)) - q π * fhat π) := by
    refine Finset.sum_le_sum fun π _ => ?_
    have hqπ := hq π
    have : -(f π - fhat π) - γ * (f π - fhat π) ^ 2 ≤ 1 / (4 * γ) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * γ * (f π - fhat π) + 1)]
    nlinarith
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (erase_sums q fhat a).1, (erase_sums q fhat a).2, hs] at h1
  have hqa := hq a
  have key : (f a - fhat a) * (1 - q a) - γ * q a * (f a - fhat a) ^ 2 ≤
      (1 - q a) ^ 2 / (4 * γ * q a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * γ * q a * (f a - fhat a) - (1 - q a))]
  have e : (1 - q a) / (4 * γ * q a) = (1 - q a) ^ 2 / (4 * γ * q a) + (1 - q a) * (1 / (4 * γ)) := by
    field_simp; ring
  unfold V
  rw [e]
  nlinarith

theorem attain {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (hγ : 0 < γ) (q : Fin A → ℝ)
    (hq : ∀ π, 0 < q π) (hs : ∑ π, q π = 1) (a : Fin A) :
    ∃ f : Fin A → ℝ, ∑ π, q π * (f a - f π - γ * (f π - fhat π) ^ 2) = V fhat γ q a := by
  let D := (1 - q a) / (2 * γ * q a)
  refine ⟨fun π => if π = a then fhat a + D else fhat π - 1 / (2 * γ), ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have h1 : ∑ π ∈ Finset.univ.erase a, q π * ((fun π => if π = a then fhat a + D else fhat π - 1 / (2 * γ)) a -
      (fun π => if π = a then fhat a + D else fhat π - 1 / (2 * γ)) π -
      γ * ((fun π => if π = a then fhat a + D else fhat π - 1 / (2 * γ)) π - fhat π) ^ 2) =
      ∑ π ∈ Finset.univ.erase a, (q π * (fhat a + D + 1 / (4 * γ)) - q π * fhat π) := by
    refine Finset.sum_congr rfl fun π hπ => ?_
    have : π ≠ a := Finset.ne_of_mem_erase hπ
    simp only [this, if_true, if_false]
    field_simp; ring
  rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, (erase_sums q fhat a).1, (erase_sums q fhat a).2, hs]
  simp only [if_true]
  have hqa := (hq a).ne'
  unfold V
  simp only [D]
  field_simp
  ring

theorem ge_of_le_star {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (q : Fin A → ℝ) (hq : ∀ π, 0 ≤ q π)
    (piStar : (Fin A → ℝ) → Fin A) (hpiStar : ∀ f : Fin A → ℝ, ∀ π : Fin A, f π ≤ f (piStar f))
    (f : Fin A → ℝ) (a : Fin A) :
    ∑ π, q π * (f a - f π - γ * (f π - fhat π) ^ 2) ≤
      ∑ π, q π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2) :=
  Finset.sum_le_sum fun π _ => mul_le_mul_of_nonneg_left (by linarith [hpiStar f a]) (hq π)

theorem sumV {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (hγ : 0 < γ) (q : Fin A → ℝ)
    (hq : ∀ π, 0 < q π) (hs : ∑ π, q π = 1) :
    ∑ a, q a * V fhat γ q a = ((A : ℝ) - 1) / (4 * γ) := by
  unfold V
  have : ∀ a, q a * (fhat a - ∑ π, q π * fhat π + (1 - q a) / (4 * γ * q a)) =
      q a * fhat a - q a * (∑ π, q π * fhat π) + (1 / (4 * γ) - q a * (1 / (4 * γ))) := by
    intro a; have := (hq a).ne'; field_simp
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
  simp; ring

theorem zero_case {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (q : Fin A → ℝ) (hq0 : ∀ π, 0 ≤ q π)
    (hq1 : ∑ π, q π = 1)
    (piStar : (Fin A → ℝ) → Fin A) (hpiStar : ∀ f : Fin A → ℝ, ∀ π : Fin A, f π ≤ f (piStar f))
    (a : Fin A) (ha : q a = 0) (c : ℝ) :
    ∃ f : Fin A → ℝ, c ≤ ∑ π, q π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2) := by
  set M := c - fhat a + ∑ π, q π * fhat π with hM
  set g : Fin A → ℝ := Function.update fhat a (fhat a + M) with hg
  refine ⟨g, le_trans ?_ (ge_of_le_star fhat γ q hq0 piStar hpiStar g a)⟩
  have hga : g a = fhat a + M := by simp [hg]
  have : ∀ π, q π * (g a - g π - γ * (g π - fhat π) ^ 2) = q π * (fhat a + M) - q π * fhat π := by
    intro π
    by_cases h : π = a
    · rw [h, ha]; ring
    · have : g π = fhat π := by simp [hg, h]
      rw [this, hga]; ring
  rw [Finset.sum_congr rfl fun π _ => this π, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1, hM]
  linarith

end EG88

open FoundationsRL.Structured in
theorem solution {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (piStar : (Fin A → ℝ) → Fin A) (hpiStar : ∀ f : Fin A → ℝ, ∀ π : Fin A, f π ≤ f (piStar f))
    (bstar : Fin A) (p : Fin A → ℝ) (hIGW : FoundationsRL.Contextual.IsIGW A fhat (2 * γ) bstar p) :
    (⨆ f : Fin A → ℝ,
        (((∑ π, p π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) : ℝ) : EReal))
        = ((((A : ℝ) - 1) / (4 * γ) : ℝ) : EReal) ∧
    (⨅ q : {q : Fin A → ℝ // (∀ π, 0 ≤ q π) ∧ ∑ π, q π = 1},
        ⨆ f : Fin A → ℝ,
          (((∑ π, q.1 π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) : ℝ) : EReal))
        = ((((A : ℝ) - 1) / (4 * γ) : ℝ) : EReal) := by
  obtain ⟨hgr, ⟨lam, ⟨hl1, hlA⟩, hp⟩, hp0, hp1⟩ := hIGW
  set c := ((A : ℝ) - 1) / (4 * γ) with hc
  have hppos : ∀ π, 0 < p π := by
    intro π; rw [hp π]
    have := hgr π
    apply one_div_pos.mpr; nlinarith
  -- V is constant for p
  have hVconst : ∀ a, EG88.V fhat γ p a = c := by
    have hK : ∀ a, EG88.V fhat γ p a = fhat bstar - ∑ π, p π * fhat π + (lam - 1) / (4 * γ) := by
      intro a
      have hden : 0 < lam + 2 * (2 * γ) * (fhat bstar - fhat a) := by nlinarith [hgr a]
      have e : (1 - p a) / (4 * γ * p a) = (lam + 2 * (2 * γ) * (fhat bstar - fhat a) - 1) / (4 * γ) := by
        rw [hp a]
        generalize lam + 2 * (2 * γ) * (fhat bstar - fhat a) = d at hden ⊢
        have := hden.ne'
        field_simp
      unfold EG88.V
      rw [e]
      field_simp
      ring
    intro a
    rw [hK a]
    have hsum := EG88.sumV fhat γ hγ p hppos hp1
    simp only [hK] at hsum
    rw [← Finset.sum_mul, hp1, one_mul] at hsum
    exact hsum
  -- lower bound: for any q, some f achieves ≥ c
  have hlow : ∀ q : Fin A → ℝ, (∀ π, 0 ≤ q π) → ∑ π, q π = 1 →
      ∃ f : Fin A → ℝ, c ≤ ∑ π, q π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2) := by
    intro q hq0 hq1
    by_cases hz : ∃ a, q a = 0
    · obtain ⟨a, ha⟩ := hz
      exact EG88.zero_case fhat γ q hq0 hq1 piStar hpiStar a ha c
    · push Not at hz
      have hqpos : ∀ π, 0 < q π := fun π => lt_of_le_of_ne (hq0 π) (hz π).symm
      have hex : ∃ a, c ≤ EG88.V fhat γ q a := by
        by_contra hcon
        push Not at hcon
        have hs := EG88.sumV fhat γ hγ q hqpos hq1
        have : ∑ a, q a * EG88.V fhat γ q a < ∑ a, q a * c :=
          Finset.sum_lt_sum_of_nonempty ⟨bstar, Finset.mem_univ _⟩
            fun a _ => mul_lt_mul_of_pos_left (hcon a) (hqpos a)
        rw [← Finset.sum_mul, hq1, one_mul] at this
        linarith
      obtain ⟨a, ha⟩ := hex
      obtain ⟨f, hf⟩ := EG88.attain fhat γ hγ q hqpos hq1 a
      exact ⟨f, ha.trans (hf ▸ EG88.ge_of_le_star fhat γ q hq0 piStar hpiStar f a)⟩
  have hfirst : (⨆ f : Fin A → ℝ,
        (((∑ π, p π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) : ℝ) : EReal)) = (c : EReal) := by
    apply le_antisymm
    · refine iSup_le fun f => EReal.coe_le_coe_iff.mpr ?_
      have := EG88.upper fhat γ hγ p hppos hp1 f (piStar f)
      rw [hVconst] at this
      exact this
    · obtain ⟨f, hf⟩ := hlow p hp0 hp1
      exact le_iSup_of_le f (EReal.coe_le_coe_iff.mpr hf)
  refine ⟨hfirst, le_antisymm ?_ ?_⟩
  · exact iInf_le_of_le ⟨p, hp0, hp1⟩ hfirst.le
  · refine le_iInf fun q => ?_
    obtain ⟨f, hf⟩ := hlow q.1 q.2.1 q.2.2
    exact le_iSup_of_le f (EReal.coe_le_coe_iff.mpr hf)
