-- Prove2me | solution 1 for BookProof.ChapterGaugeComprehensiveFixing.physical_ext_iff_comprehensive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:00:21.428963+00:00
-- url     : https://prove2.me/submissions/3696ce89-ce71-4ffb-8058-4423d4535c5b

-- Generated from ChapterGaugeComprehensiveFixing.lean — theorem BookProof.ChapterGaugeComprehensiveFixing.physical_ext_iff_comprehensive
import Mathlib
import Definitions.Def_ChapterGaugeComprehensiveFixing
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeComprehensiveFixing



open BookProof.ChapterGaugeIncompleteFixing


theorem gf_orbit_ind {X G : Type*} [Group G] [MulAction G X] (x : X) :
    IsPhysicalObservable G (fun y : X => by classical exact if ∃ g : G, g • x = y then (1:ℝ) else 0) := by
  classical
  intro g y
  simp only
  by_cases h : ∃ g' : G, g' • x = y
  · obtain ⟨g', rfl⟩ := h
    rw [if_pos ⟨g * g', by rw [mul_smul]⟩, if_pos ⟨g', rfl⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨g', hg'⟩
    exact h ⟨g⁻¹ * g', by rw [mul_smul, hg', inv_smul_smul]⟩

theorem gf_not_comp {X G : Type*} [Group G] [MulAction G X] {S : Set X}
    (hS : ¬ IsComprehensiveGaugeFixing G S) :
    ∃ f f' : X → ℝ, IsPhysicalObservable G f ∧ IsPhysicalObservable G f' ∧
      (∀ s ∈ S, f s = f' s) ∧ f ≠ f' := by
  classical
  unfold IsComprehensiveGaugeFixing at hS
  push_neg at hS
  obtain ⟨x, hx⟩ := hS
  refine ⟨fun y => if ∃ g : G, g • x = y then (1:ℝ) else 0, fun _ => 0, gf_orbit_ind x,
    fun _ _ => rfl, ?_, ?_⟩
  · intro s hs
    simp only
    rw [if_neg]
    rintro ⟨g, hg⟩
    exact hx s hs g⁻¹ (by rw [← hg, inv_smul_smul])
  · intro h
    have := congrFun h x
    beta_reduce at this
    rw [if_pos ⟨1, one_smul G x⟩] at this
    norm_num at this

theorem gf_not_complete {X G : Type*} [Group G] [MulAction G X] {S : Set X}
    (hS : ¬ IsCompleteGaugeFixing' G S) :
    ∃ h : X → ℝ, ¬ ∃ f : X → ℝ, IsPhysicalObservable G f ∧ ∀ s ∈ S, f s = h s := by
  classical
  unfold IsCompleteGaugeFixing' at hS
  push_neg at hS
  obtain ⟨s, hs, t, ht, g, hgt, hne⟩ := hS
  refine ⟨fun x => if x = s then 1 else 0, ?_⟩
  rintro ⟨f, hf, hfS⟩
  have h1 := hfS s hs
  have h2 := hfS t ht
  beta_reduce at h1 h2
  rw [if_pos rfl] at h1
  rw [if_neg (Ne.symm hne)] at h2
  rw [← hgt, hf g s] at h2
  linarith

theorem gf_complete_ext {X G : Type*} [Group G] [MulAction G X] {S : Set X}
    (hS : IsCompleteGaugeFixing' G S) (h : X → ℝ) :
    ∃ f : X → ℝ, IsPhysicalObservable G f ∧ ∀ s ∈ S, f s = h s := by
  classical
  let f : X → ℝ := fun x => if hx : ∃ s ∈ S, ∃ g : G, g • s = x then h (Classical.choose hx) else 0
  have key : ∀ s ∈ S, ∀ g : G, f (g • s) = h s := by
    intro s hs g
    have hx : ∃ s' ∈ S, ∃ g' : G, g' • s' = g • s := ⟨s, hs, g, rfl⟩
    simp only [f, dif_pos hx]
    obtain ⟨hs', g', hg'⟩ := Classical.choose_spec hx
    congr 1
    apply hS _ hs' s hs (g⁻¹ * g')
    rw [mul_smul, hg', inv_smul_smul]
  refine ⟨f, ?_, fun s hs => by simpa using key s hs 1⟩
  intro g x
  by_cases hx : ∃ s ∈ S, ∃ g' : G, g' • s = x
  · obtain ⟨s, hs, g', rfl⟩ := hx
    rw [← mul_smul, key s hs, key s hs]
  · have hx' : ¬ ∃ s ∈ S, ∃ g' : G, g' • s = g • x := by
      rintro ⟨s, hs, g', hg'⟩
      exact hx ⟨s, hs, g⁻¹ * g', by rw [mul_smul, hg', inv_smul_smul]⟩
    simp only [f, dif_neg hx, dif_neg hx']

variable {X : Type*} {G : Type*} [Group G] [MulAction G X] {S : Set X}
theorem solution :
    (∀ f f' : X → ℝ, IsPhysicalObservable G f → IsPhysicalObservable G f' →
        (∀ s ∈ S, f s = f' s) → f = f') ↔ IsComprehensiveGaugeFixing G S := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨f, f', hf, hf', hS, hne⟩ := gf_not_comp hc
    exact hne (h f f' hf hf' hS)
  · intro hS f f' hf hf' hfS
    funext x
    obtain ⟨s, hs, g, rfl⟩ := hS x
    rw [hf, hf', hfS s hs]
