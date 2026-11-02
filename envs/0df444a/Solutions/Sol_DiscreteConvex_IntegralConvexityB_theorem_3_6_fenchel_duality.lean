-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityB.theorem_3_6_fenchel_duality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:38:09.174818+00:00
-- url     : https://prove2.me/submissions/95435e8a-7818-44de-a7a2-0f49fa3cdd4f

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConcave
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsClosedConvexF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsClosedConcaveF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE
import Definitions.Def_DiscreteConvex_IntegralConvexityB_RelInt
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPolyhedralConcave
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConjF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConcConjF
import Theorems.Thm_DiscreteConvex_IntegralConvexityB_theorem_3_5_separation_convex_functions
import Theorems.Thm_DiscreteConvex_IntegralConvexityB_theorem_3_9_farkas_lemma

open DiscreteConvex.IntegralConvexityB
open scoped BigOperators Matrix

variable {V : Type*} [Fintype V]

/-! ### Basic EReal and Domain/Epigraph/Hypograph Helpers -/

private lemma mem_domE_iff_epi {f : (V → ℝ) → EReal} (hf_nbot : NeverBot f) (x : V → ℝ) :
    x ∈ DomE f ↔ ∃ y : ℝ, (x, y) ∈ Epi f := by
  constructor
  · rintro ⟨h1, h2⟩
    lift f x to ℝ using ⟨h1, h2⟩ with y hy
    exact ⟨y, by simp [Epi, ← hy]⟩
  · rintro ⟨y, hy⟩
    refine ⟨?_, hf_nbot x⟩
    intro htop
    have hy' : (⊤ : EReal) ≤ (y : EReal) := htop ▸ hy
    exact EReal.coe_ne_top y (top_le_iff.mp hy')

private lemma mem_domE_iff_hypo {h : (V → ℝ) → EReal} (hh_ntop : NeverTop h) (x : V → ℝ) :
    x ∈ DomE h ↔ ∃ y : ℝ, (x, y) ∈ Hypo h := by
  constructor
  · rintro ⟨h1, h2⟩
    lift h x to ℝ using ⟨h1, h2⟩ with y hy
    exact ⟨y, by simp [Hypo, ← hy]⟩
  · rintro ⟨y, hy⟩
    refine ⟨hh_ntop x, ?_⟩
    intro hbot
    have hy' : (y : EReal) ≤ (⊥ : EReal) := hbot ▸ hy
    exact EReal.coe_ne_bot y (le_bot_iff.mp hy')

private lemma conjF_ne_bot {f : (V → ℝ) → EReal} (hf : IsProperConvex f) (p : V → ℝ) :
    ConjF f p ≠ ⊥ := by
  rcases hf.2.2 with ⟨x0, hx0_top, hx0_bot⟩
  lift f x0 to ℝ using ⟨hx0_top, hx0_bot⟩ with rf0 hrf0
  have hle : ((dotProduct p x0 - rf0 : ℝ) : EReal) ≤ ConjF f p := by
    unfold ConjF
    apply le_sSup
    exact ⟨x0, by rw [← hrf0, EReal.coe_sub]⟩
  intro hbot
  rw [hbot] at hle
  exact EReal.coe_ne_bot (dotProduct p x0 - rf0) (le_bot_iff.mp hle)

private lemma concConjF_ne_top {h : (V → ℝ) → EReal} (hh : IsProperConcave h) (p : V → ℝ) :
    ConcConjF h p ≠ ⊤ := by
  rcases hh.2.2 with ⟨x0, hx0_top, hx0_bot⟩
  lift h x0 to ℝ using ⟨hx0_top, hx0_bot⟩ with rh0 hrh0
  have hle : ConcConjF h p ≤ ((dotProduct p x0 - rh0 : ℝ) : EReal) := by
    unfold ConcConjF
    apply sInf_le
    exact ⟨x0, by rw [← hrh0, EReal.coe_sub]⟩
  intro htop
  rw [htop] at hle
  exact EReal.coe_ne_top (dotProduct p x0 - rh0) (top_le_iff.mp hle)

private lemma conjF_le_iff {f : (V → ℝ) → EReal} (hf_nbot : NeverBot f) (p : V → ℝ) (c : ℝ) :
    ConjF f p ≤ (c : EReal) ↔ ∀ x y1, (x, y1) ∈ Epi f → dotProduct p x - y1 ≤ c := by
  constructor
  · intro hle x y1 hxy1
    have hx_le : ((dotProduct p x : ℝ) : EReal) - f x ≤ (c : EReal) := by
      refine (le_sSup ?_).trans hle
      exact ⟨x, rfl⟩
    have hx_dom : x ∈ DomE f := (mem_domE_iff_epi hf_nbot x).mpr ⟨y1, hxy1⟩
    rcases hx_dom with ⟨htop, hbot⟩
    lift f x to ℝ using ⟨htop, hbot⟩ with rf hrf
    have hrf_le : rf ≤ y1 := by
      have hxy1' : f x ≤ (y1 : EReal) := hxy1
      rw [← hrf] at hxy1'
      exact EReal.coe_le_coe_iff.mp hxy1'
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hx_le
    linarith
  · intro hbound
    unfold ConjF
    apply sSup_le
    rintro v ⟨x, rfl⟩
    by_cases htop : f x = ⊤
    · rw [htop]; exact bot_le
    · have hbot : f x ≠ ⊥ := hf_nbot x
      lift f x to ℝ using ⟨htop, hbot⟩ with rf hrf
      have hle := hbound x rf (by simp [Epi, ← hrf])
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      exact hle

private lemma le_concConjF_iff {h : (V → ℝ) → EReal} (hh_ntop : NeverTop h) (p : V → ℝ) (c : ℝ) :
    (c : EReal) ≤ ConcConjF h p ↔ ∀ x y2, (x, y2) ∈ Hypo h → c ≤ dotProduct p x - y2 := by
  constructor
  · intro hle x y2 hxy2
    have hx_ge : (c : EReal) ≤ ((dotProduct p x : ℝ) : EReal) - h x := by
      refine hle.trans (sInf_le ?_)
      exact ⟨x, rfl⟩
    have hx_dom : x ∈ DomE h := (mem_domE_iff_hypo hh_ntop x).mpr ⟨y2, hxy2⟩
    rcases hx_dom with ⟨htop, hbot⟩
    lift h x to ℝ using ⟨htop, hbot⟩ with rh hrh
    have hy2_le : y2 ≤ rh := by
      have hxy2' : (y2 : EReal) ≤ h x := hxy2
      rw [← hrh] at hxy2'
      exact EReal.coe_le_coe_iff.mp hxy2'
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hx_ge
    linarith
  · intro hbound
    unfold ConcConjF
    apply le_sInf
    rintro v ⟨x, rfl⟩
    by_cases hbot : h x = ⊥
    · rw [hbot]
      change (c : EReal) ≤ ((dotProduct p x : ℝ) : EReal) + - (⊥ : EReal)
      rw [EReal.neg_bot, EReal.coe_add_top]
      exact le_top
    · have htop : h x ≠ ⊤ := hh_ntop x
      lift h x to ℝ using ⟨htop, hbot⟩ with rh hrh
      have hle := hbound x rh (by simp [Hypo, ← hrh])
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      exact hle

private lemma weak_duality_point {f h : (V → ℝ) → EReal}
    (hf : IsProperConvex f) (hh : IsProperConcave h) (x p : V → ℝ) :
    ConcConjF h p - ConjF f p ≤ f x - h x := by
  by_cases hfx_top : f x = ⊤
  · rw [hfx_top]
    have hnh : - h x ≠ ⊥ := by
      intro hbot
      exact hh.2.1 x (EReal.neg_eq_bot_iff.mp hbot)
    change _ ≤ (⊤ : EReal) + (- h x)
    rw [EReal.top_add_of_ne_bot hnh]
    exact le_top
  · by_cases hhx_bot : h x = ⊥
    · rw [hhx_bot]
      have hnf : f x ≠ ⊥ := hf.2.1 x
      change _ ≤ f x + - (⊥ : EReal)
      rw [EReal.neg_bot, EReal.add_top_of_ne_bot hnf]
      exact le_top
    · have hfx_bot : f x ≠ ⊥ := hf.2.1 x
      have hhx_top : h x ≠ ⊤ := hh.2.1 x
      lift f x to ℝ using ⟨hfx_top, hfx_bot⟩ with rf hrf
      lift h x to ℝ using ⟨hhx_top, hhx_bot⟩ with rh hrh
      have h1 : ((dotProduct p x - rf : ℝ) : EReal) ≤ ConjF f p := by
        unfold ConjF
        apply le_sSup
        exact ⟨x, by rw [← hrf, EReal.coe_sub]⟩
      have h2 : ConcConjF h p ≤ ((dotProduct p x - rh : ℝ) : EReal) := by
        unfold ConcConjF
        apply sInf_le
        exact ⟨x, by rw [← hrh, EReal.coe_sub]⟩
      have hsub := EReal.sub_le_sub h2 h1
      refine hsub.trans ?_
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith

private lemma weak_duality {f h : (V → ℝ) → EReal}
    (hf : IsProperConvex f) (hh : IsProperConcave h) :
    sSup {v : EReal | ∃ p : V → ℝ, v = ConcConjF h p - ConjF f p} ≤
      sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} := by
  apply sSup_le
  rintro u ⟨p, rfl⟩
  apply le_sInf
  rintro v ⟨x, rfl⟩
  exact weak_duality_point hf hh x p

/-! ### Part 1: Primal Qualification `(a1) ∨ (a2)` via Theorem 3.5 -/

private noncomputable def shiftEReal (f : (V → ℝ) → EReal) (c : ℝ) : (V → ℝ) → EReal :=
  fun x => f x + (c : EReal)

private lemma domE_shiftEReal (f : (V → ℝ) → EReal) (c : ℝ) :
    DomE (shiftEReal f c) = DomE f := by
  ext x
  change (f x + (c : EReal) ≠ ⊤ ∧ f x + (c : EReal) ≠ ⊥) ↔ (f x ≠ ⊤ ∧ f x ≠ ⊥)
  rcases eq_top_or_lt_top (f x) with htop | htop
  · rw [htop]; simp
  · rcases eq_bot_or_bot_lt (f x) with hbot | hbot
    · rw [hbot]; simp
    · lift f x to ℝ using ⟨htop.ne, hbot.ne'⟩ with r hr
      rw [← EReal.coe_add]
      exact ⟨fun _ => ⟨EReal.coe_ne_top r, EReal.coe_ne_bot r⟩,
        fun _ => ⟨EReal.coe_ne_top (r + c), EReal.coe_ne_bot (r + c)⟩⟩

private lemma neverBot_shiftEReal {f : (V → ℝ) → EReal} (hf : NeverBot f) (c : ℝ) :
    NeverBot (shiftEReal f c) := by
  intro x
  have hdom := Set.ext_iff.mp (domE_shiftEReal f c) x
  by_cases htop : f x = ⊤
  · simp [shiftEReal, htop]
  · have hx : x ∈ DomE f := ⟨htop, hf x⟩
    exact (hdom.mpr hx).2

private lemma epi_shiftEReal (f : (V → ℝ) → EReal) (c : ℝ) (x : V → ℝ) (y : ℝ) :
    (x, y) ∈ Epi (shiftEReal f c) ↔ (x, y - c) ∈ Epi f := by
  change f x + (c : EReal) ≤ (y : EReal) ↔ f x ≤ ((y - c : ℝ) : EReal)
  rcases eq_top_or_lt_top (f x) with htop | htop
  · rw [htop, EReal.top_add_coe, top_le_iff, top_le_iff]
    exact ⟨fun h => absurd h (EReal.coe_ne_top y), fun h => absurd h (EReal.coe_ne_top (y - c))⟩
  · rcases eq_bot_or_bot_lt (f x) with hbot | hbot
    · rw [hbot]; simp
    · lift f x to ℝ using ⟨htop.ne, hbot.ne'⟩ with r hr
      rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith

private lemma isProperConvex_shiftEReal {f : (V → ℝ) → EReal} (hf : IsProperConvex f) (c : ℝ) :
    IsProperConvex (shiftEReal f c) := by
  refine ⟨?_, neverBot_shiftEReal hf.2.1 c, ?_⟩
  · rintro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 a b ha hb hab
    rw [epi_shiftEReal] at h1 h2
    change (a • x1 + b • x2, a * y1 + b * y2) ∈ Epi (shiftEReal f c)
    rw [epi_shiftEReal]
    have hconv := hf.1 h1 h2 ha hb hab
    change (a • x1 + b • x2, a * (y1 - c) + b * (y2 - c)) ∈ Epi f at hconv
    have heq : a * (y1 - c) + b * (y2 - c) = a * y1 + b * y2 - c := by
      calc a * (y1 - c) + b * (y2 - c) = a * y1 + b * y2 - (a + b) * c := by ring
        _ = a * y1 + b * y2 - c := by rw [hab, one_mul]
    rwa [heq] at hconv
  · rw [domE_shiftEReal]
    exact hf.2.2

private lemma isPolyhedralConvex_shiftEReal {f : (V → ℝ) → EReal}
    (hf : IsPolyhedralConvex f) (c : ℝ) :
    IsPolyhedralConvex (shiftEReal f c) := by
  rcases hf with ⟨m, w, c_i, b, heq⟩
  refine ⟨m, w, c_i, fun i => b i + c_i i * c, ?_⟩
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq]
  rw [epi_shiftEReal, heq]
  simp only [Set.mem_setOf_eq, LinFunc]
  constructor <;> intro h i <;> have hi := h i <;> linarith

private lemma primal_sep_at_delta {f h : (V → ℝ) → EReal}
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (ha : (RelInt (DomE f) ∩ RelInt (DomE h)).Nonempty ∨
      (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧ (DomE f ∩ DomE h).Nonempty))
    (delta : ℝ)
    (hge_delta : ∀ x : V → ℝ, (delta : EReal) ≤ f x - h x) :
    ∃ p ∈ DomE (ConjF f) ∩ DomE (ConcConjF h),
      (delta : EReal) ≤ ConcConjF h p - ConjF f p := by
  have ha' : (RelInt (DomE (shiftEReal f (-delta))) ∩ RelInt (DomE h)).Nonempty ∨
      (IsPolyhedralConvex (shiftEReal f (-delta)) ∧ IsPolyhedralConcave h ∧
        (DomE (shiftEReal f (-delta)) ∩ DomE h).Nonempty) := by
    rw [domE_shiftEReal]
    rcases ha with h1 | ⟨hp1, hp2, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨isPolyhedralConvex_shiftEReal hp1 (-delta), hp2, h3⟩
  have hge_shift : ∀ x : V → ℝ, shiftEReal f (-delta) x ≥ h x := by
    intro x
    change h x ≤ f x + ((-delta : ℝ) : EReal)
    by_cases hfx_top : f x = ⊤
    · simp [hfx_top, le_top]
    · by_cases hhx_bot : h x = ⊥
      · simp [hhx_bot]
      · have hfx_bot : f x ≠ ⊥ := hf.2.1 x
        have hhx_top : h x ≠ ⊤ := hh.2.1 x
        lift f x to ℝ using ⟨hfx_top, hfx_bot⟩ with rf hrf
        lift h x to ℝ using ⟨hhx_top, hhx_bot⟩ with rh hrh
        have hd := hge_delta x
        rw [← hrf, ← hrh, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hd
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]
        linarith
  obtain ⟨astar, pstar, hsep⟩ :=
    theorem_3_5_separation_convex_functions (shiftEReal f (-delta)) h
      (isProperConvex_shiftEReal hf (-delta)) hh ha' hge_shift
  have hconj_le : ConjF f pstar ≤ ((-astar - delta : ℝ) : EReal) := by
    rw [conjF_le_iff hf.2.1]
    intro x y1 hxy1
    have hx_dom : x ∈ DomE f := (mem_domE_iff_epi hf.2.1 x).mpr ⟨y1, hxy1⟩
    rcases hx_dom with ⟨htop, hbot⟩
    lift f x to ℝ using ⟨htop, hbot⟩ with rf hrf
    have hrf_le : rf ≤ y1 := by
      have hxy1' : f x ≤ (y1 : EReal) := hxy1
      rw [← hrf] at hxy1'
      exact EReal.coe_le_coe_iff.mp hxy1'
    have h1 : ((astar + dotProduct pstar x : ℝ) : EReal) ≤ ((rf + -delta : ℝ) : EReal) := by
      rw [EReal.coe_add, EReal.coe_add, hrf]
      exact (hsep x).1
    rw [EReal.coe_le_coe_iff] at h1
    linarith
  have hconc_ge : ((-astar : ℝ) : EReal) ≤ ConcConjF h pstar := by
    rw [le_concConjF_iff hh.2.1]
    intro x y2 hxy2
    have hx_dom : x ∈ DomE h := (mem_domE_iff_hypo hh.2.1 x).mpr ⟨y2, hxy2⟩
    rcases hx_dom with ⟨htop, hbot⟩
    lift h x to ℝ using ⟨htop, hbot⟩ with rh hrh
    have hy2_le : y2 ≤ rh := by
      have hxy2' : (y2 : EReal) ≤ h x := hxy2
      rw [← hrh] at hxy2'
      exact EReal.coe_le_coe_iff.mp hxy2'
    have h2 : (rh : EReal) ≤ ((astar + dotProduct pstar x : ℝ) : EReal) := by
      rw [EReal.coe_add, hrh]
      exact (hsep x).2
    rw [EReal.coe_le_coe_iff] at h2
    linarith
  have hp_dom1 : pstar ∈ DomE (ConjF f) := by
    refine ⟨?_, conjF_ne_bot hf pstar⟩
    intro htop
    rw [htop] at hconj_le
    exact EReal.coe_ne_top (-astar - delta) (top_le_iff.mp hconj_le)
  have hp_dom2 : pstar ∈ DomE (ConcConjF h) := by
    refine ⟨concConjF_ne_top hh pstar, ?_⟩
    intro hbot
    rw [hbot] at hconc_ge
    exact EReal.coe_ne_bot (-astar) (le_bot_iff.mp hconc_ge)
  refine ⟨pstar, ⟨hp_dom1, hp_dom2⟩, ?_⟩
  have hsub := EReal.sub_le_sub hconc_ge hconj_le
  have hdelta : ((-astar : ℝ) : EReal) - ((-astar - delta : ℝ) : EReal) = (delta : EReal) := by
    rw [← EReal.coe_sub]
    congr 1
    ring
  rwa [hdelta] at hsub

private lemma fenchel_primal_qual {f h : (V → ℝ) → EReal}
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (ha : (RelInt (DomE f) ∩ RelInt (DomE h)).Nonempty ∨
      (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧ (DomE f ∩ DomE h).Nonempty)) :
    (sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} =
        sSup {v : EReal | ∃ p : V → ℝ, v = ConcConjF h p - ConjF f p}) ∧
      (∀ delta : ℝ,
        sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} = (delta : EReal) →
          ∃ p ∈ DomE (ConjF f) ∩ DomE (ConcConjF h),
            ConcConjF h p - ConjF f p = (delta : EReal)) := by
  have hweak := weak_duality hf hh
  have hdom_inter : (DomE f ∩ DomE h).Nonempty := by
    rcases ha with ⟨x0, hx0f, hx0h⟩ | ⟨_, _, h3⟩
    · exact ⟨x0, hx0f.1, hx0h.1⟩
    · exact h3
  rcases hdom_inter with ⟨x0, ⟨hx0f_top, hx0f_bot⟩, ⟨hx0h_top, hx0h_bot⟩⟩
  lift f x0 to ℝ using ⟨hx0f_top, hx0f_bot⟩ with rf0 hrf0
  lift h x0 to ℝ using ⟨hx0h_top, hx0h_bot⟩ with rh0 hrh0
  have hinf_ne_top : sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} ≠ ⊤ := by
    have hle : sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} ≤ ((rf0 - rh0 : ℝ) : EReal) := by
      apply sInf_le
      exact ⟨x0, by rw [← hrf0, ← hrh0, EReal.coe_sub]⟩
    intro htop
    rw [htop] at hle
    exact EReal.coe_ne_top (rf0 - rh0) (top_le_iff.mp hle)
  have hatt : ∀ delta : ℝ,
      sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} = (delta : EReal) →
        ∃ p ∈ DomE (ConjF f) ∩ DomE (ConcConjF h),
          ConcConjF h p - ConjF f p = (delta : EReal) := by
    intro delta hdelta
    have hge_delta : ∀ x : V → ℝ, (delta : EReal) ≤ f x - h x := by
      intro x
      rw [← hdelta]
      exact sInf_le ⟨x, rfl⟩
    obtain ⟨p, hp_dom, hp_ge⟩ := primal_sep_at_delta hf hh ha delta hge_delta
    have hp_le : ConcConjF h p - ConjF f p ≤ (delta : EReal) := by
      rw [← hdelta]
      have hmem : ConcConjF h p - ConjF f p ∈
          {v : EReal | ∃ p' : V → ℝ, v = ConcConjF h p' - ConjF f p'} := ⟨p, rfl⟩
      exact (le_sSup hmem).trans hweak
    exact ⟨p, hp_dom, le_antisymm hp_le hp_ge⟩
  refine ⟨?_, hatt⟩
  by_cases hinf_bot : sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} = ⊥
  · rw [hinf_bot] at hweak ⊢
    exact (le_bot_iff.mp hweak).symm
  · generalize hval : sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} = val at hinf_ne_top hinf_bot
    lift val to ℝ using ⟨hinf_ne_top, hinf_bot⟩ with delta
    obtain ⟨p, _, hp_eq⟩ := hatt delta hval
    have hge : (delta : EReal) ≤ sSup {v : EReal | ∃ p : V → ℝ, v = ConcConjF h p - ConjF f p} := by
      rw [← hp_eq]
      have hmem : ConcConjF h p - ConjF f p ∈
          {v : EReal | ∃ p' : V → ℝ, v = ConcConjF h p' - ConjF f p'} := ⟨p, rfl⟩
      exact le_sSup hmem
    rw [hval] at hweak
    exact le_antisymm hge hweak

/-! ### Part 2: Closed Qualification `(b1)` via Biconjugate Lower/Upper Bounds -/

private lemma isProperConvex_conjF {f : (V → ℝ) → EReal}
    (hf : IsProperConvex f) (hdom : (DomE (ConjF f)).Nonempty) :
    IsProperConvex (ConjF f) := by
  refine ⟨?_, conjF_ne_bot hf, hdom⟩
  rintro ⟨p1, r1⟩ h1 ⟨p2, r2⟩ h2 a b ha hb hab
  change ConjF f p1 ≤ (r1 : EReal) at h1
  change ConjF f p2 ≤ (r2 : EReal) at h2
  change ConjF f (a • p1 + b • p2) ≤ ((a * r1 + b * r2 : ℝ) : EReal)
  rw [conjF_le_iff hf.2.1] at h1 h2 ⊢
  intro x y1 hxy1
  have h1x := h1 x y1 hxy1
  have h2x := h2 x y1 hxy1
  have hdot : dotProduct (a • p1 + b • p2) x - y1 =
      a * (dotProduct p1 x - y1) + b * (dotProduct p2 x - y1) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    calc a * dotProduct p1 x + b * dotProduct p2 x - y1 =
        a * dotProduct p1 x + b * dotProduct p2 x - (a + b) * y1 := by rw [hab, one_mul]
      _ = a * (dotProduct p1 x - y1) + b * (dotProduct p2 x - y1) := by ring
  rw [hdot]
  nlinarith

private lemma isProperConcave_concConjF {h : (V → ℝ) → EReal}
    (hh : IsProperConcave h) (hdom : (DomE (ConcConjF h)).Nonempty) :
    IsProperConcave (ConcConjF h) := by
  refine ⟨?_, concConjF_ne_top hh, hdom⟩
  rintro ⟨p1, r1⟩ h1 ⟨p2, r2⟩ h2 a b ha hb hab
  change (r1 : EReal) ≤ ConcConjF h p1 at h1
  change (r2 : EReal) ≤ ConcConjF h p2 at h2
  change ((a * r1 + b * r2 : ℝ) : EReal) ≤ ConcConjF h (a • p1 + b • p2)
  rw [le_concConjF_iff hh.2.1] at h1 h2 ⊢
  intro x y2 hxy2
  have h1x := h1 x y2 hxy2
  have h2x := h2 x y2 hxy2
  have hdot : dotProduct (a • p1 + b • p2) x - y2 =
      a * (dotProduct p1 x - y2) + b * (dotProduct p2 x - y2) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    calc a * dotProduct p1 x + b * dotProduct p2 x - y2 =
        a * dotProduct p1 x + b * dotProduct p2 x - (a + b) * y2 := by rw [hab, one_mul]
      _ = a * (dotProduct p1 x - y2) + b * (dotProduct p2 x - y2) := by ring
  rw [hdot]
  nlinarith

private lemma prod_clm_decomp (φ : ((V → ℝ) × ℝ) →L[ℝ] ℝ) :
    ∃ (w : V → ℝ) (c : ℝ), ∀ (x : V → ℝ) (y : ℝ), φ (x, y) = dotProduct w x + c * y := by
  classical
  let w : V → ℝ := fun v => φ (Pi.single v (1 : ℝ), 0)
  let c : ℝ := φ (0, 1)
  refine ⟨w, c, fun x y => ?_⟩
  have hx : x = ∑ v : V, x v • Pi.single v (1 : ℝ) := by
    ext v'
    simp [Finset.sum_apply, Pi.single_apply]
  have hpair : (x, y) = LinearMap.inl ℝ (V → ℝ) ℝ x + y • ((0 : V → ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hpair, map_add, map_smul, smul_eq_mul]
  congr 1
  · have hinl : LinearMap.inl ℝ (V → ℝ) ℝ x = ∑ v : V, x v • (Pi.single v (1 : ℝ), (0 : ℝ)) := by
      conv_lhs => rw [hx]
      rw [map_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [map_smul]
      rfl
    rw [hinl, map_sum]
    change ∑ v : V, φ (x v • (Pi.single v (1 : ℝ), (0 : ℝ))) = ∑ v : V, w v * x v
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  · dsimp [c]
    ring

private lemma le_biconjugate_of_closed {f : (V → ℝ) → EReal}
    (hf : IsProperConvex f) (hcl : IsClosedConvexF f) (x0 : V → ℝ) :
    f x0 ≤ ConjF (ConjF f) x0 := by
  have h_forall_lt : ∀ r : ℝ, (r : EReal) < f x0 → (r : EReal) ≤ ConjF (ConjF f) x0 := by
    intro r hr
    have hnot_epi : (x0, r) ∉ Epi f := by
      intro hmem
      have hle : f x0 ≤ (r : EReal) := hmem
      exact not_le_of_gt hr hle
    obtain ⟨φ, u, hφ_pt, hφ_epi⟩ :=
      geometric_hahn_banach_point_closed hcl.1 hcl.2 hnot_epi
    obtain ⟨w, c, hφ_eq⟩ := prod_clm_decomp φ
    rcases hf.2.2 with ⟨x1, hx1_top, hx1_bot⟩
    lift f x1 to ℝ using ⟨hx1_top, hx1_bot⟩ with y1 hy1
    have hx1_epi : (x1, y1) ∈ Epi f := by simp [Epi, ← hy1]
    have hc_nonneg : 0 ≤ c := by
      by_contra hc_neg
      push_neg at hc_neg
      let t : ℝ := (|u - (dotProduct w x1 + c * y1)| + 1) / (-c)
      have ht_pos : 0 < t := div_pos (by positivity) (by linarith)
      have hx1_t : (x1, y1 + t) ∈ Epi f := by
        change f x1 ≤ ((y1 + t : ℝ) : EReal)
        rw [← hy1, EReal.coe_le_coe_iff]
        linarith
      have hgt := hφ_epi (x1, y1 + t) hx1_t
      rw [hφ_eq] at hgt
      have hmul : c * t = -(|u - (dotProduct w x1 + c * y1)| + 1) := by
        dsimp [t]
        have hc_ne : -c ≠ 0 := by linarith
        calc c * ((|u - (dotProduct w x1 + c * y1)| + 1) / (-c))
            = - ((-c) * ((|u - (dotProduct w x1 + c * y1)| + 1) / (-c))) := by ring
          _ = -(|u - (dotProduct w x1 + c * y1)| + 1) := by rw [mul_div_cancel₀ _ hc_ne]
      have habs := neg_le_abs (u - (dotProduct w x1 + c * y1))
      rw [mul_add, hmul] at hgt
      linarith
    rcases hc_nonneg.lt_or_eq with hc_pos | hc_zero
    · let p : V → ℝ := - c⁻¹ • w
      have hconj_le : ConjF f p ≤ ((-u / c : ℝ) : EReal) := by
        rw [conjF_le_iff hf.2.1]
        intro x y hxy
        have hgt := hφ_epi (x, y) hxy
        rw [hφ_eq] at hgt
        have hdot : dotProduct p x = - c⁻¹ * dotProduct w x := by
          dsimp [p]
          rw [smul_dotProduct, smul_eq_mul]
        rw [hdot]
        have hcalc : (-c⁻¹ * dotProduct w x - y) * c = -(dotProduct w x + c * y) := by
          calc (-c⁻¹ * dotProduct w x - y) * c = -(c⁻¹ * c) * dotProduct w x - y * c := by ring
            _ = -(dotProduct w x + c * y) := by rw [inv_mul_cancel₀ hc_pos.ne']; ring
        have hle : (-c⁻¹ * dotProduct w x - y) * c ≤ -u := by linarith
        exact (le_div_iff₀ hc_pos).mpr hle
      have hr_le : (r : EReal) ≤ ((dotProduct x0 p - (-u / c) : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        have hlt := hφ_pt
        rw [hφ_eq] at hlt
        have hdot : dotProduct x0 p = - c⁻¹ * dotProduct w x0 := by
          rw [dotProduct_comm]
          dsimp [p]
          rw [smul_dotProduct, smul_eq_mul]
        rw [hdot]
        have hcalc : (r - (-c⁻¹ * dotProduct w x0 - -u / c)) * c = dotProduct w x0 + c * r - u := by
          have hc_ne : c ≠ 0 := hc_pos.ne'
          field_simp [hc_ne]
          ring
        nlinarith
      refine hr_le.trans ?_
      refine ( ?_ : ((dotProduct x0 p - (-u / c) : ℝ) : EReal) ≤
          ((dotProduct x0 p : ℝ) : EReal) - ConjF f p ).trans (le_sSup ⟨p, rfl⟩)
      rw [EReal.coe_sub]
      exact EReal.sub_le_sub le_rfl hconj_le
    · have hc0 : c = 0 := hc_zero.symm
      have hx1_not : (x1, y1 - 1) ∉ Epi f := by
        intro hmem
        have hle : f x1 ≤ ((y1 - 1 : ℝ) : EReal) := hmem
        rw [← hy1, EReal.coe_le_coe_iff] at hle
        linarith
      obtain ⟨φ1, u1, hφ1_pt, hφ1_epi⟩ :=
        geometric_hahn_banach_point_closed hcl.1 hcl.2 hx1_not
      obtain ⟨w1, c1, hφ1_eq⟩ := prod_clm_decomp φ1
      have h1_lt := hφ1_pt
      have h1_gt := hφ1_epi (x1, y1) hx1_epi
      rw [hφ1_eq] at h1_lt h1_gt
      have hc1_pos : 0 < c1 := by linarith
      let p1 : V → ℝ := - c1⁻¹ • w1
      let α1 : ℝ := - u1 / c1
      have hp1_bound : ∀ x y, (x, y) ∈ Epi f → dotProduct p1 x - y ≤ α1 := by
        intro x y hxy
        have hgt := hφ1_epi (x, y) hxy
        rw [hφ1_eq] at hgt
        have hdot : dotProduct p1 x = - c1⁻¹ * dotProduct w1 x := by
          dsimp [p1]
          rw [smul_dotProduct, smul_eq_mul]
        rw [hdot]
        have hcalc : (-c1⁻¹ * dotProduct w1 x - y) * c1 = -(dotProduct w1 x + c1 * y) := by
          calc (-c1⁻¹ * dotProduct w1 x - y) * c1 = -(c1⁻¹ * c1) * dotProduct w1 x - y * c1 := by ring
            _ = -(dotProduct w1 x + c1 * y) := by rw [inv_mul_cancel₀ hc1_pos.ne']; ring
        have hle : (-c1⁻¹ * dotProduct w1 x - y) * c1 ≤ -u1 := by linarith
        exact (le_div_iff₀ hc1_pos).mpr hle
      have hw_x0 : dotProduct w x0 < u := by
        have hlt := hφ_pt
        rw [hφ_eq, hc0, zero_mul, add_zero] at hlt
        exact hlt
      have hw_epi : ∀ x y, (x, y) ∈ Epi f → u < dotProduct w x := by
        intro x y hxy
        have hgt := hφ_epi (x, y) hxy
        rw [hφ_eq, hc0, zero_mul, add_zero] at hgt
        exact hgt
      let t : ℝ := max 0 ((r - (dotProduct x0 p1 - α1)) / (u - dotProduct w x0))
      have ht_nn : 0 ≤ t := le_max_left _ _
      let pt : V → ℝ := p1 - t • w
      have hconj_pt : ConjF f pt ≤ ((α1 - t * u : ℝ) : EReal) := by
        rw [conjF_le_iff hf.2.1]
        intro x y hxy
        have h1 := hp1_bound x y hxy
        have h2 := (hw_epi x y hxy).le
        have hdot : dotProduct pt x = dotProduct p1 x - t * dotProduct w x := by
          change dotProduct (p1 - t • w) x = _
          rw [sub_dotProduct, smul_dotProduct t w x, smul_eq_mul]
        rw [hdot]
        nlinarith
      have hr_le : (r : EReal) ≤ ((dotProduct x0 pt - (α1 - t * u) : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        have hdot : dotProduct x0 pt = dotProduct x0 p1 - t * dotProduct w x0 := by
          change dotProduct x0 (p1 - t • w) = _
          rw [dotProduct_sub, dotProduct_smul t x0 w, smul_eq_mul, dotProduct_comm x0 w]
        rw [hdot]
        have ht_ge : (r - (dotProduct x0 p1 - α1)) / (u - dotProduct w x0) ≤ t := le_max_right _ _
        have hden : 0 < u - dotProduct w x0 := by linarith
        have hmul := (div_le_iff₀ hden).mp ht_ge
        linarith
      refine hr_le.trans ?_
      refine ( ?_ : ((dotProduct x0 pt - (α1 - t * u) : ℝ) : EReal) ≤
          ((dotProduct x0 pt : ℝ) : EReal) - ConjF f pt ).trans (le_sSup ⟨pt, rfl⟩)
      rw [EReal.coe_sub]
      exact EReal.sub_le_sub le_rfl hconj_pt
  rcases eq_top_or_lt_top (ConjF (ConjF f) x0) with htop | hlt_top
  · rw [htop]; exact le_top
  · rcases eq_bot_or_bot_lt (ConjF (ConjF f) x0) with hbot | hgt_bot
    · rcases eq_top_or_lt_top (f x0) with hfx_top | hfx_lt
      · have h0 := h_forall_lt 0 (by rw [hfx_top]; exact EReal.coe_lt_top 0)
        rw [hbot] at h0
        exact absurd (le_bot_iff.mp h0) (EReal.coe_ne_bot 0)
      · lift f x0 to ℝ using ⟨hfx_lt.ne, hf.2.1 x0⟩ with rf hrf
        have h1 := h_forall_lt (rf - 1) (by rw [EReal.coe_lt_coe_iff]; linarith)
        rw [hbot] at h1
        exact absurd (le_bot_iff.mp h1) (EReal.coe_ne_bot (rf - 1))
    · lift ConjF (ConjF f) x0 to ℝ using ⟨hlt_top.ne, hgt_bot.ne'⟩ with rc hrc
      rcases eq_top_or_lt_top (f x0) with hfx_top | hfx_lt
      · have h1 := h_forall_lt (rc + 1) (by rw [hfx_top]; exact EReal.coe_lt_top (rc + 1))
        rw [EReal.coe_le_coe_iff] at h1
        linarith
      · lift f x0 to ℝ using ⟨hfx_lt.ne, hf.2.1 x0⟩ with rf hrf
        rw [EReal.coe_le_coe_iff]
        by_contra hlt
        push_neg at hlt
        have hmid := h_forall_lt ((rf + rc) / 2) (by rw [EReal.coe_lt_coe_iff]; linarith)
        rw [EReal.coe_le_coe_iff] at hmid
        linarith

private noncomputable def revNeg (h : (V → ℝ) → EReal) : (V → ℝ) → EReal :=
  fun x => - h (-x)

private lemma epi_revNeg (h : (V → ℝ) → EReal) (x : V → ℝ) (y : ℝ) :
    (x, y) ∈ Epi (revNeg h) ↔ (-x, -y) ∈ Hypo h := by
  change - h (-x) ≤ (y : EReal) ↔ ((-y : ℝ) : EReal) ≤ h (-x)
  rw [EReal.neg_le, ← EReal.coe_neg]

private lemma isProperConvex_revNeg {h : (V → ℝ) → EReal} (hh : IsProperConcave h) :
    IsProperConvex (revNeg h) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 a b ha hb hab
    rw [epi_revNeg] at h1 h2
    change (a • x1 + b • x2, a * y1 + b * y2) ∈ Epi (revNeg h)
    rw [epi_revNeg]
    have hconv := hh.1 h1 h2 ha hb hab
    change (a • (-x1) + b • (-x2), a * (-y1) + b * (-y2)) ∈ Hypo h at hconv
    have hx : a • (-x1) + b • (-x2) = - (a • x1 + b • x2) := by module
    have hy : a * (-y1) + b * (-y2) = - (a * y1 + b * y2) := by ring
    rwa [hx, hy] at hconv
  · intro x hbot
    exact hh.2.1 (-x) (EReal.neg_eq_bot_iff.mp hbot)
  · rcases hh.2.2 with ⟨x0, hx0_top, hx0_bot⟩
    refine ⟨-x0, ?_, ?_⟩
    · simp only [revNeg, neg_neg]
      intro htop
      exact hx0_bot (EReal.neg_eq_top_iff.mp htop)
    · simp only [revNeg, neg_neg]
      intro hbot
      exact hx0_top (EReal.neg_eq_bot_iff.mp hbot)

private lemma isClosedConvexF_revNeg {h : (V → ℝ) → EReal}
    (hh : IsProperConcave h) (hcl : IsClosedConcaveF h) :
    IsClosedConvexF (revNeg h) := by
  refine ⟨(isProperConvex_revNeg hh).1, ?_⟩
  have heq : Epi (revNeg h) = (fun p : (V → ℝ) × ℝ => (-p.1, -p.2)) ⁻¹' (Hypo h) := by
    ext ⟨x, y⟩
    exact epi_revNeg h x y
  rw [heq]
  exact hcl.2.preimage (continuous_fst.neg.prodMk continuous_snd.neg)

private lemma conjF_revNeg (h : (V → ℝ) → EReal) (p : V → ℝ) :
    ConjF (revNeg h) p = - ConcConjF h p := by
  apply le_antisymm
  · unfold ConjF
    apply sSup_le
    rintro v ⟨x, rfl⟩
    rw [EReal.le_neg]
    unfold ConcConjF
    apply sInf_le
    refine ⟨-x, ?_⟩
    dsimp [revNeg]
    have hdot : dotProduct p (-x) = - dotProduct p x := dotProduct_neg p x
    rw [hdot, EReal.coe_neg]
    rcases eq_top_or_lt_top (h (-x)) with htop | hlt_top
    · rw [htop]; simp
    · rcases eq_bot_or_bot_lt (h (-x)) with hbot | hgt_bot
      · rw [hbot]; simp
      · lift h (-x) to ℝ using ⟨hlt_top.ne, hgt_bot.ne'⟩ with r hr
        simp only [← EReal.coe_neg, ← EReal.coe_sub]
        congr 1
        ring
  · rw [EReal.neg_le]
    unfold ConcConjF
    apply le_sInf
    rintro v ⟨x, rfl⟩
    rw [EReal.neg_le]
    unfold ConjF
    apply le_sSup
    refine ⟨-x, ?_⟩
    dsimp [revNeg]
    rw [neg_neg, dotProduct_neg, EReal.coe_neg]
    rcases eq_top_or_lt_top (h x) with htop | hlt_top
    · rw [htop]; simp
    · rcases eq_bot_or_bot_lt (h x) with hbot | hgt_bot
      · rw [hbot]; simp
      · lift h x to ℝ using ⟨hlt_top.ne, hgt_bot.ne'⟩ with r hr
        simp only [← EReal.coe_neg, ← EReal.coe_sub]
        congr 1
        ring

private lemma conjF_neg (g : (V → ℝ) → EReal) (x0 : V → ℝ) :
    ConjF (fun p => - g p) (-x0) = - ConcConjF g x0 := by
  apply le_antisymm
  · unfold ConjF
    apply sSup_le
    rintro v ⟨p, rfl⟩
    rw [EReal.le_neg]
    unfold ConcConjF
    apply sInf_le
    refine ⟨p, ?_⟩
    dsimp only
    rw [neg_dotProduct, dotProduct_comm x0 p, EReal.coe_neg]
    rcases eq_top_or_lt_top (g p) with htop | hlt_top
    · rw [htop]; simp
    · rcases eq_bot_or_bot_lt (g p) with hbot | hgt_bot
      · rw [hbot]; simp
      · lift g p to ℝ using ⟨hlt_top.ne, hgt_bot.ne'⟩ with r hr
        simp only [← EReal.coe_neg, ← EReal.coe_sub]
        congr 1; ring
  · rw [EReal.neg_le]
    unfold ConcConjF
    apply le_sInf
    rintro v ⟨p, rfl⟩
    rw [EReal.neg_le]
    unfold ConjF
    apply le_sSup
    refine ⟨p, ?_⟩
    dsimp only
    rw [neg_dotProduct, dotProduct_comm x0 p, EReal.coe_neg]
    rcases eq_top_or_lt_top (g p) with htop | hlt_top
    · rw [htop]; simp
    · rcases eq_bot_or_bot_lt (g p) with hbot | hgt_bot
      · rw [hbot]; simp
      · lift g p to ℝ using ⟨hlt_top.ne, hgt_bot.ne'⟩ with r hr
        simp only [← EReal.coe_neg, ← EReal.coe_sub]
        congr 1; ring

private lemma biconjugate_le_of_closed_concave {h : (V → ℝ) → EReal}
    (hh : IsProperConcave h) (hcl : IsClosedConcaveF h) (x0 : V → ℝ) :
    ConcConjF (ConcConjF h) x0 ≤ h x0 := by
  have hconv := le_biconjugate_of_closed (isProperConvex_revNeg hh) (isClosedConvexF_revNeg hh hcl) (-x0)
  have h1 : revNeg h (-x0) = - h x0 := by simp [revNeg]
  have hg_eq : ConjF (revNeg h) = fun p => - ConcConjF h p := funext (conjF_revNeg h)
  have h2 : ConjF (ConjF (revNeg h)) (-x0) = - ConcConjF (ConcConjF h) x0 := by
    rw [hg_eq]
    exact conjF_neg (ConcConjF h) x0
  rw [h1, h2, EReal.neg_le_neg_iff] at hconv
  exact hconv

private lemma closed_dual_dichotomy {f h : (V → ℝ) → EReal}
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (hcl : IsClosedConvexF f ∧ IsClosedConcaveF h)
    (hri : (RelInt (DomE (ConjF f)) ∩ RelInt (DomE (ConcConjF h))).Nonempty)
    (delta : ℝ) :
    (∃ x ∈ DomE f ∩ DomE h, f x - h x ≤ (delta : EReal)) ∨
      (∃ p : V → ℝ, (delta : EReal) < ConcConjF h p - ConjF f p) := by
  by_cases h_ex_p : ∃ p : V → ℝ, (delta : EReal) < ConcConjF h p - ConjF f p
  · exact Or.inr h_ex_p
  · left
    push_neg at h_ex_p
    rcases hri with ⟨p0, hp0f, hp0h⟩
    have hf_conj : IsProperConvex (ConjF f) := isProperConvex_conjF hf ⟨p0, hp0f.1⟩
    have hh_conc : IsProperConcave (ConcConjF h) := isProperConcave_concConjF hh ⟨p0, hp0h.1⟩
    have ha_dual : (RelInt (DomE (shiftEReal (ConjF f) delta)) ∩ RelInt (DomE (ConcConjF h))).Nonempty ∨
        (IsPolyhedralConvex (shiftEReal (ConjF f) delta) ∧ IsPolyhedralConcave (ConcConjF h) ∧
          (DomE (shiftEReal (ConjF f) delta) ∩ DomE (ConcConjF h)).Nonempty) := by
      rw [domE_shiftEReal]
      exact Or.inl ⟨p0, hp0f, hp0h⟩
    have hge_dual : ∀ p : V → ℝ, shiftEReal (ConjF f) delta p ≥ ConcConjF h p := by
      intro p
      change ConcConjF h p ≤ ConjF f p + (delta : EReal)
      by_cases hcf_top : ConjF f p = ⊤
      · simp [hcf_top, le_top]
      · by_cases hch_bot : ConcConjF h p = ⊥
        · simp [hch_bot]
        · have hcf_bot : ConjF f p ≠ ⊥ := conjF_ne_bot hf p
          have hch_top : ConcConjF h p ≠ ⊤ := concConjF_ne_top hh p
          lift ConjF f p to ℝ using ⟨hcf_top, hcf_bot⟩ with cf hcf
          lift ConcConjF h p to ℝ using ⟨hch_top, hch_bot⟩ with ch hch
          have hp := h_ex_p p
          rw [← hcf, ← hch, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hp
          rw [← EReal.coe_add, EReal.coe_le_coe_iff]
          linarith
    obtain ⟨astar, xstar, hsep⟩ :=
      theorem_3_5_separation_convex_functions (shiftEReal (ConjF f) delta) (ConcConjF h)
        (isProperConvex_shiftEReal hf_conj delta) hh_conc ha_dual hge_dual
    have hbiconj_f : ConjF (ConjF f) xstar ≤ ((-astar + delta : ℝ) : EReal) := by
      rw [conjF_le_iff hf_conj.2.1]
      intro p y1 hpy1
      have hp_dom : p ∈ DomE (ConjF f) := (mem_domE_iff_epi hf_conj.2.1 p).mpr ⟨y1, hpy1⟩
      rcases hp_dom with ⟨htop, hbot⟩
      lift ConjF f p to ℝ using ⟨htop, hbot⟩ with cf hcf
      have hcf_le : cf ≤ y1 := by
        have hpy1' : ConjF f p ≤ (y1 : EReal) := hpy1
        rw [← hcf] at hpy1'
        exact EReal.coe_le_coe_iff.mp hpy1'
      have h1 : ((astar + dotProduct xstar p : ℝ) : EReal) ≤ ((cf + delta : ℝ) : EReal) := by
        rw [EReal.coe_add, EReal.coe_add, hcf]
        exact (hsep p).1
      rw [EReal.coe_le_coe_iff] at h1
      linarith
    have hbiconj_h : ((-astar : ℝ) : EReal) ≤ ConcConjF (ConcConjF h) xstar := by
      rw [le_concConjF_iff hh_conc.2.1]
      intro p y2 hpy2
      have hp_dom : p ∈ DomE (ConcConjF h) := (mem_domE_iff_hypo hh_conc.2.1 p).mpr ⟨y2, hpy2⟩
      rcases hp_dom with ⟨htop, hbot⟩
      lift ConcConjF h p to ℝ using ⟨htop, hbot⟩ with ch hch
      have hy2_le : y2 ≤ ch := by
        have hpy2' : (y2 : EReal) ≤ ConcConjF h p := hpy2
        rw [← hch] at hpy2'
        exact EReal.coe_le_coe_iff.mp hpy2'
      have h2 : (ch : EReal) ≤ ((astar + dotProduct xstar p : ℝ) : EReal) := by
        rw [EReal.coe_add, hch]
        exact (hsep p).2
      rw [EReal.coe_le_coe_iff] at h2
      linarith
    have hfx_le : f xstar ≤ ((-astar + delta : ℝ) : EReal) :=
      (le_biconjugate_of_closed hf hcl.1 xstar).trans hbiconj_f
    have hhx_ge : ((-astar : ℝ) : EReal) ≤ h xstar :=
      hbiconj_h.trans (biconjugate_le_of_closed_concave hh hcl.2 xstar)
    have hx_dom_f : xstar ∈ DomE f := by
      refine ⟨?_, hf.2.1 xstar⟩
      intro htop
      rw [htop] at hfx_le
      exact EReal.coe_ne_top (-astar + delta) (top_le_iff.mp hfx_le)
    have hx_dom_h : xstar ∈ DomE h := by
      refine ⟨hh.2.1 xstar, ?_⟩
      intro hbot
      rw [hbot] at hhx_ge
      exact EReal.coe_ne_bot (-astar) (le_bot_iff.mp hhx_ge)
    refine ⟨xstar, ⟨hx_dom_f, hx_dom_h⟩, ?_⟩
    have hsub := EReal.sub_le_sub hfx_le hhx_ge
    have hdelta : ((-astar + delta : ℝ) : EReal) - ((-astar : ℝ) : EReal) = (delta : EReal) := by
      rw [← EReal.coe_sub]
      congr 1; ring
    rwa [hdelta] at hsub

/-! ### Part 3: Polyhedral Dual Qualification `(b2)` via Theorem 3.9 -/

private abbrev PolyRow (V : Type*) := V ⊕ (Bool ⊕ Unit)
private abbrev PolyCol (m1 m2 : ℕ) := (Fin m1 ⊕ Fin m2) ⊕ Unit

private def galeMatrix {m1 m2 : ℕ} (w1 : Fin m1 → V → ℝ) (c1 b1 : Fin m1 → ℝ)
    (w2 : Fin m2 → V → ℝ) (c2 b2 : Fin m2 → ℝ) (delta : ℝ) :
    Matrix (PolyRow V) (PolyCol m1 m2) ℝ :=
  fun r col =>
    match r, col with
    | Sum.inl v, Sum.inl (Sum.inl i) => - w1 i v
    | Sum.inr (Sum.inl true), Sum.inl (Sum.inl i) => - c1 i
    | Sum.inr (Sum.inl false), Sum.inl (Sum.inl _) => 0
    | Sum.inr (Sum.inr ()), Sum.inl (Sum.inl i) => b1 i
    | Sum.inl v, Sum.inl (Sum.inr j) => - w2 j v
    | Sum.inr (Sum.inl true), Sum.inl (Sum.inr _) => 0
    | Sum.inr (Sum.inl false), Sum.inl (Sum.inr j) => - c2 j
    | Sum.inr (Sum.inr ()), Sum.inl (Sum.inr j) => b2 j
    | Sum.inl _, Sum.inr () => 0
    | Sum.inr (Sum.inl true), Sum.inr () => -1
    | Sum.inr (Sum.inl false), Sum.inr () => 1
    | Sum.inr (Sum.inr ()), Sum.inr () => delta

private def galeRhs : PolyRow V → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr ()) => -1

private lemma gale_vecMul_inl_inl {m1 m2 : ℕ} (w1 : Fin m1 → V → ℝ) (c1 b1 : Fin m1 → ℝ)
    (w2 : Fin m2 → V → ℝ) (c2 b2 : Fin m2 → ℝ) (delta : ℝ) (y : PolyRow V → ℝ) (i : Fin m1) :
    Matrix.vecMul y (galeMatrix w1 c1 b1 w2 c2 b2 delta) (Sum.inl (Sum.inl i)) =
      - (dotProduct (w1 i) (fun v => y (Sum.inl v)) + c1 i * y (Sum.inr (Sum.inl true))) +
        y (Sum.inr (Sum.inr ())) * b1 i := by
  simp only [Matrix.vecMul, dotProduct, galeMatrix, Fintype.sum_sum_type,
    Fintype.sum_bool, Fintype.sum_unique, mul_neg, mul_zero, add_zero]
  have hsum : ∑ x : V, -(y (Sum.inl x) * w1 i x) = - ∑ x : V, w1 i x * y (Sum.inl x) := by
    rw [Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hd : (default : Unit) = () := rfl
  rw [hsum, hd]
  ring

private lemma gale_vecMul_inl_inr {m1 m2 : ℕ} (w1 : Fin m1 → V → ℝ) (c1 b1 : Fin m1 → ℝ)
    (w2 : Fin m2 → V → ℝ) (c2 b2 : Fin m2 → ℝ) (delta : ℝ) (y : PolyRow V → ℝ) (j : Fin m2) :
    Matrix.vecMul y (galeMatrix w1 c1 b1 w2 c2 b2 delta) (Sum.inl (Sum.inr j)) =
      - (dotProduct (w2 j) (fun v => y (Sum.inl v)) + c2 j * y (Sum.inr (Sum.inl false))) +
        y (Sum.inr (Sum.inr ())) * b2 j := by
  simp only [Matrix.vecMul, dotProduct, galeMatrix, Fintype.sum_sum_type,
    Fintype.sum_bool, Fintype.sum_unique, mul_neg, mul_zero, zero_add]
  have hsum : ∑ x : V, -(y (Sum.inl x) * w2 j x) = - ∑ x : V, w2 j x * y (Sum.inl x) := by
    rw [Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hd : (default : Unit) = () := rfl
  rw [hsum, hd]
  ring

private lemma gale_vecMul_inr {m1 m2 : ℕ} (w1 : Fin m1 → V → ℝ) (c1 b1 : Fin m1 → ℝ)
    (w2 : Fin m2 → V → ℝ) (c2 b2 : Fin m2 → ℝ) (delta : ℝ) (y : PolyRow V → ℝ) :
    Matrix.vecMul y (galeMatrix w1 c1 b1 w2 c2 b2 delta) (Sum.inr ()) =
      - (y (Sum.inr (Sum.inl true)) - y (Sum.inr (Sum.inl false))) +
        y (Sum.inr (Sum.inr ())) * delta := by
  simp only [Matrix.vecMul, dotProduct, galeMatrix, Fintype.sum_sum_type,
    Fintype.sum_bool, Fintype.sum_unique, mul_zero, Finset.sum_const_zero, zero_add, mul_one, mul_neg]
  have hd : (default : Unit) = () := rfl
  rw [hd]
  ring

private lemma gale_dot_rhs (y : PolyRow V → ℝ) :
    dotProduct y (galeRhs (V := V)) = - y (Sum.inr (Sum.inr ())) := by
  simp only [dotProduct, galeRhs, Fintype.sum_sum_type, Fintype.sum_bool, Fintype.sum_unique,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero, mul_one, mul_neg]

private lemma polyhedral_dual_dichotomy {f h : (V → ℝ) → EReal}
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (hf_poly : IsPolyhedralConvex f) (hh_poly : IsPolyhedralConcave h)
    (hdom_dual : (DomE (ConjF f) ∩ DomE (ConcConjF h)).Nonempty)
    (delta : ℝ) :
    (∃ x ∈ DomE f ∩ DomE h, f x - h x ≤ (delta : EReal)) ∨
      (∃ p : V → ℝ, (delta : EReal) < ConcConjF h p - ConjF f p) := by
  rcases hf_poly with ⟨m1, w1, c1, b1, hepi_eq⟩
  rcases hh_poly with ⟨m2, w2, c2, b2, hhypo_eq⟩
  by_cases hfeas : ∃ (x : V → ℝ) (y1 y2 : ℝ),
      (x, y1) ∈ Epi f ∧ (x, y2) ∈ Hypo h ∧ y1 - y2 ≤ delta
  · left
    rcases hfeas with ⟨x, y1, y2, he1, hh2, hdiff⟩
    have hxf : x ∈ DomE f := (mem_domE_iff_epi hf.2.1 x).mpr ⟨y1, he1⟩
    have hxh : x ∈ DomE h := (mem_domE_iff_hypo hh.2.1 x).mpr ⟨y2, hh2⟩
    refine ⟨x, ⟨hxf, hxh⟩, ?_⟩
    have he1' : f x ≤ (y1 : EReal) := he1
    have hh2' : (y2 : EReal) ≤ h x := hh2
    refine (EReal.sub_le_sub he1' hh2').trans ?_
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    exact hdiff
  · right
    push_neg at hfeas
    let B := galeMatrix w1 c1 b1 w2 c2 b2 delta
    have hfarkas_cond : ∀ y : PolyRow V → ℝ,
        (∀ col, 0 ≤ Matrix.vecMul y B col) → 0 ≤ dotProduct y (galeRhs (V := V)) := by
      intro y hy
      rw [gale_dot_rhs]
      let x : V → ℝ := fun v => y (Sum.inl v)
      let y1 : ℝ := y (Sum.inr (Sum.inl true))
      let y2 : ℝ := y (Sum.inr (Sum.inl false))
      let t : ℝ := y (Sum.inr (Sum.inr ()))
      by_contra ht_neg
      have ht_pos : 0 < t := by linarith
      have hi : ∀ i : Fin m1, dotProduct (w1 i) x + c1 i * y1 ≤ t * b1 i := by
        intro i
        have := hy (Sum.inl (Sum.inl i))
        rw [gale_vecMul_inl_inl] at this
        linarith
      have hj : ∀ j : Fin m2, dotProduct (w2 j) x + c2 j * y2 ≤ t * b2 j := by
        intro j
        have := hy (Sum.inl (Sum.inr j))
        rw [gale_vecMul_inl_inr] at this
        linarith
      have hdel : y1 - y2 ≤ t * delta := by
        have := hy (Sum.inr ())
        rw [gale_vecMul_inr] at this
        linarith
      have h1' : (t⁻¹ • x, t⁻¹ * y1) ∈ Epi f := by
        rw [hepi_eq]
        intro i
        dsimp [LinFunc]
        have hle := mul_le_mul_of_nonneg_left (hi i) (inv_nonneg.mpr ht_pos.le)
        rw [inv_mul_cancel_left₀ ht_pos.ne'] at hle
        rw [dotProduct_smul, smul_eq_mul]
        linarith
      have h2' : (t⁻¹ • x, t⁻¹ * y2) ∈ Hypo h := by
        rw [hhypo_eq]
        intro j
        dsimp [LinFunc]
        have hle := mul_le_mul_of_nonneg_left (hj j) (inv_nonneg.mpr ht_pos.le)
        rw [inv_mul_cancel_left₀ ht_pos.ne'] at hle
        rw [dotProduct_smul, smul_eq_mul]
        linarith
      have h3' : t⁻¹ * y1 - t⁻¹ * y2 ≤ delta := by
        have hle := mul_le_mul_of_nonneg_left hdel (inv_nonneg.mpr ht_pos.le)
        rw [inv_mul_cancel_left₀ ht_pos.ne'] at hle
        linarith
      exact not_le_of_gt (hfeas (t⁻¹ • x) (t⁻¹ * y1) (t⁻¹ * y2) h1' h2') h3'
    obtain ⟨lam, hlam_nn, hlam_eq⟩ :=
      (theorem_3_9_farkas_lemma B (galeRhs (V := V))).mpr hfarkas_cond
    let lam1 : Fin m1 → ℝ := fun i => lam (Sum.inl (Sum.inl i))
    let lam2 : Fin m2 → ℝ := fun j => lam (Sum.inl (Sum.inr j))
    let mu : ℝ := lam (Sum.inr ())
    have hlam1_nn : ∀ i, 0 ≤ lam1 i := fun i => hlam_nn (Sum.inl (Sum.inl i))
    have hlam2_nn : ∀ j, 0 ≤ lam2 j := fun j => hlam_nn (Sum.inl (Sum.inr j))
    have hmu_nn : 0 ≤ mu := hlam_nn (Sum.inr ())
    have hrow_v : ∀ v : V, ∑ i : Fin m1, lam1 i * w1 i v + ∑ j : Fin m2, lam2 j * w2 j v = 0 := by
      intro v
      have hv := congrFun hlam_eq (Sum.inl v)
      simp only [Matrix.mulVec, dotProduct, B, galeMatrix, galeRhs,
        Fintype.sum_sum_type, Fintype.sum_unique, zero_mul, add_zero] at hv
      change ∑ i : Fin m1, -w1 i v * lam1 i + ∑ j : Fin m2, -w2 j v * lam2 j = 0 at hv
      linarith [show ∑ i : Fin m1, -w1 i v * lam1 i = - ∑ i : Fin m1, lam1 i * w1 i v by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => by ring,
        show ∑ j : Fin m2, -w2 j v * lam2 j = - ∑ j : Fin m2, lam2 j * w2 j v by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => by ring]
    have hrow_y1 : ∑ i : Fin m1, lam1 i * c1 i = -mu := by
      have hy1 := congrFun hlam_eq (Sum.inr (Sum.inl true))
      simp only [Matrix.mulVec, dotProduct, B, galeMatrix, galeRhs,
        Fintype.sum_sum_type, Fintype.sum_unique, zero_mul, Finset.sum_const_zero, add_zero] at hy1
      change ∑ i : Fin m1, -c1 i * lam1 i + -1 * mu = 0 at hy1
      linarith [show ∑ i : Fin m1, -c1 i * lam1 i = - ∑ i : Fin m1, lam1 i * c1 i by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => by ring]
    have hrow_y2 : ∑ j : Fin m2, lam2 j * c2 j = mu := by
      have hy2 := congrFun hlam_eq (Sum.inr (Sum.inl false))
      simp only [Matrix.mulVec, dotProduct, B, galeMatrix, galeRhs,
        Fintype.sum_sum_type, Fintype.sum_unique, zero_mul, Finset.sum_const_zero, zero_add] at hy2
      change ∑ j : Fin m2, -c2 j * lam2 j + 1 * mu = 0 at hy2
      linarith [show ∑ j : Fin m2, -c2 j * lam2 j = - ∑ j : Fin m2, lam2 j * c2 j by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => by ring]
    have hrow_t : ∑ i : Fin m1, lam1 i * b1 i + ∑ j : Fin m2, lam2 j * b2 j + mu * delta = -1 := by
      have ht := congrFun hlam_eq (Sum.inr (Sum.inr ()))
      simp only [Matrix.mulVec, dotProduct, B, galeMatrix, galeRhs,
        Fintype.sum_sum_type, Fintype.sum_unique] at ht
      change ∑ i : Fin m1, b1 i * lam1 i + ∑ j : Fin m2, b2 j * lam2 j + delta * mu = -1 at ht
      linarith [show ∑ i : Fin m1, b1 i * lam1 i = ∑ i : Fin m1, lam1 i * b1 i by
        refine Finset.sum_congr rfl fun i _ => by ring,
        show ∑ j : Fin m2, b2 j * lam2 j = ∑ j : Fin m2, lam2 j * b2 j by
        refine Finset.sum_congr rfl fun j _ => by ring]
    let dp : V → ℝ := fun v => ∑ i : Fin m1, lam1 i * w1 i v
    have hdp_eq : ∀ v : V, ∑ j : Fin m2, lam2 j * w2 j v = - dp v := by
      intro v; linarith [hrow_v v]
    have hdp_dot1 : ∀ x : V → ℝ, dotProduct dp x = ∑ i : Fin m1, lam1 i * dotProduct (w1 i) x := by
      intro x
      dsimp [dp, dotProduct]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => by ring
    have hdp_dot2 : ∀ x : V → ℝ, ∑ j : Fin m2, lam2 j * dotProduct (w2 j) x = - dotProduct dp x := by
      intro x
      dsimp [dotProduct]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∑ v : V, ∑ j : Fin m2, lam2 j * (w2 j v * x v) = ∑ v : V, (- dp v) * x v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← hdp_eq v, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [this, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun v _ => by ring
    have hepi_sum : ∀ x y1, (x, y1) ∈ Epi f →
        dotProduct dp x - mu * y1 ≤ ∑ i : Fin m1, lam1 i * b1 i := by
      intro x y1 hxy1
      rw [hepi_eq] at hxy1
      have hnn : 0 ≤ ∑ i : Fin m1, lam1 i * (b1 i - (dotProduct (w1 i) x + c1 i * y1)) := by
        refine Finset.sum_nonneg fun i _ => mul_nonneg (hlam1_nn i) ?_
        have := hxy1 i; dsimp [LinFunc] at this; linarith
      have hid : ∑ i : Fin m1, lam1 i * (b1 i - (dotProduct (w1 i) x + c1 i * y1)) =
          ∑ i : Fin m1, lam1 i * b1 i - dotProduct dp x + mu * y1 := by
        calc ∑ i : Fin m1, lam1 i * (b1 i - (dotProduct (w1 i) x + c1 i * y1))
            = ∑ i : Fin m1, lam1 i * b1 i - ∑ i : Fin m1, lam1 i * dotProduct (w1 i) x -
                (∑ i : Fin m1, lam1 i * c1 i) * y1 := by
              rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => by ring
          _ = ∑ i : Fin m1, lam1 i * b1 i - dotProduct dp x + mu * y1 := by
              rw [hdp_dot1 x, hrow_y1]; ring
      linarith
    have hhypo_sum : ∀ x y2, (x, y2) ∈ Hypo h →
        - dotProduct dp x + mu * y2 ≤ ∑ j : Fin m2, lam2 j * b2 j := by
      intro x y2 hxy2
      rw [hhypo_eq] at hxy2
      have hnn : 0 ≤ ∑ j : Fin m2, lam2 j * (b2 j - (dotProduct (w2 j) x + c2 j * y2)) := by
        refine Finset.sum_nonneg fun j _ => mul_nonneg (hlam2_nn j) ?_
        have := hxy2 j; dsimp [LinFunc] at this; linarith
      have hid : ∑ j : Fin m2, lam2 j * (b2 j - (dotProduct (w2 j) x + c2 j * y2)) =
          ∑ j : Fin m2, lam2 j * b2 j + dotProduct dp x - mu * y2 := by
        calc ∑ j : Fin m2, lam2 j * (b2 j - (dotProduct (w2 j) x + c2 j * y2))
            = ∑ j : Fin m2, lam2 j * b2 j - ∑ j : Fin m2, lam2 j * dotProduct (w2 j) x -
                (∑ j : Fin m2, lam2 j * c2 j) * y2 := by
              rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ j : Fin m2, lam2 j * b2 j + dotProduct dp x - mu * y2 := by
              rw [hdp_dot2 x, hrow_y2]; ring
      linarith
    rcases hmu_nn.lt_or_eq with hmu_pos | hmu_zero
    · let pstar : V → ℝ := mu⁻¹ • dp
      let B1 : ℝ := mu⁻¹ * ∑ i : Fin m1, lam1 i * b1 i
      let B2 : ℝ := mu⁻¹ * ∑ j : Fin m2, lam2 j * b2 j
      have hconj_le : ConjF f pstar ≤ (B1 : EReal) := by
        rw [conjF_le_iff hf.2.1]
        intro x y1 hxy1
        have h1 := mul_le_mul_of_nonneg_left (hepi_sum x y1 hxy1) (inv_nonneg.mpr hmu_pos.le)
        have hdot : dotProduct pstar x = mu⁻¹ * dotProduct dp x := by
          dsimp [pstar]; rw [smul_dotProduct, smul_eq_mul]
        rw [hdot]
        have hcalc : mu⁻¹ * (dotProduct dp x - mu * y1) = mu⁻¹ * dotProduct dp x - y1 := by
          calc mu⁻¹ * (dotProduct dp x - mu * y1) = mu⁻¹ * dotProduct dp x - (mu⁻¹ * mu) * y1 := by ring
            _ = mu⁻¹ * dotProduct dp x - y1 := by rw [inv_mul_cancel₀ hmu_pos.ne', one_mul]
        dsimp [B1]
        linarith
      have hconc_ge : ((-B2 : ℝ) : EReal) ≤ ConcConjF h pstar := by
        rw [le_concConjF_iff hh.2.1]
        intro x y2 hxy2
        have h2 := mul_le_mul_of_nonneg_left (hhypo_sum x y2 hxy2) (inv_nonneg.mpr hmu_pos.le)
        have hdot : dotProduct pstar x = mu⁻¹ * dotProduct dp x := by
          dsimp [pstar]; rw [smul_dotProduct, smul_eq_mul]
        rw [hdot]
        have hcalc : mu⁻¹ * (- dotProduct dp x + mu * y2) = - (mu⁻¹ * dotProduct dp x) + y2 := by
          calc mu⁻¹ * (- dotProduct dp x + mu * y2) = - (mu⁻¹ * dotProduct dp x) + (mu⁻¹ * mu) * y2 := by ring
            _ = - (mu⁻¹ * dotProduct dp x) + y2 := by rw [inv_mul_cancel₀ hmu_pos.ne', one_mul]
        dsimp [B2]
        linarith
      refine ⟨pstar, ?_⟩
      have hsub := EReal.sub_le_sub hconc_ge hconj_le
      have hlt : (delta : EReal) < ((-B2 : ℝ) : EReal) - (B1 : EReal) := by
        rw [← EReal.coe_sub, EReal.coe_lt_coe_iff]
        have hB_sum : B1 + B2 + delta = - mu⁻¹ := by
          dsimp [B1, B2]
          calc mu⁻¹ * ∑ i : Fin m1, lam1 i * b1 i + mu⁻¹ * ∑ j : Fin m2, lam2 j * b2 j + delta
              = mu⁻¹ * (∑ i : Fin m1, lam1 i * b1 i + ∑ j : Fin m2, lam2 j * b2 j + mu * delta) := by
                have : mu⁻¹ * (mu * delta) = delta := inv_mul_cancel_left₀ hmu_pos.ne' delta
                linarith
            _ = - mu⁻¹ := by rw [hrow_t]; ring
        have hmu_inv_pos : 0 < mu⁻¹ := inv_pos.mpr hmu_pos
        linarith
      exact hlt.trans_le hsub
    · have hmu0 : mu = 0 := hmu_zero.symm
      rcases hdom_dual with ⟨p0, ⟨hp0f_top, hp0f_bot⟩, ⟨hp0h_top, hp0h_bot⟩⟩
      lift ConjF f p0 to ℝ using ⟨hp0f_top, hp0f_bot⟩ with cf0 hcf0
      lift ConcConjF h p0 to ℝ using ⟨hp0h_top, hp0h_bot⟩ with ch0 hch0
      have hp0_epi : ∀ x y1, (x, y1) ∈ Epi f → dotProduct p0 x - y1 ≤ cf0 :=
        (conjF_le_iff hf.2.1 p0 cf0).mp (by rw [← hcf0])
      have hp0_hypo : ∀ x y2, (x, y2) ∈ Hypo h → ch0 ≤ dotProduct p0 x - y2 :=
        (le_concConjF_iff hh.2.1 p0 ch0).mp (by rw [← hch0])
      let t : ℝ := max 0 (delta + 1 - (ch0 - cf0))
      have ht_nn : 0 ≤ t := le_max_left _ _
      let pt : V → ℝ := p0 + t • dp
      let B1 : ℝ := ∑ i : Fin m1, lam1 i * b1 i
      let B2 : ℝ := ∑ j : Fin m2, lam2 j * b2 j
      have hconj_pt : ConjF f pt ≤ ((cf0 + t * B1 : ℝ) : EReal) := by
        rw [conjF_le_iff hf.2.1]
        intro x y1 hxy1
        have h0 := hp0_epi x y1 hxy1
        have h1 := hepi_sum x y1 hxy1
        rw [hmu0, zero_mul, sub_zero] at h1
        have hdot : dotProduct pt x = dotProduct p0 x + t * dotProduct dp x := by
          dsimp [pt]; rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
        rw [hdot]; dsimp [B1]; nlinarith
      have hconc_pt : ((ch0 - t * B2 : ℝ) : EReal) ≤ ConcConjF h pt := by
        rw [le_concConjF_iff hh.2.1]
        intro x y2 hxy2
        have h0 := hp0_hypo x y2 hxy2
        have h2 := hhypo_sum x y2 hxy2
        rw [hmu0, zero_mul, add_zero] at h2
        have hdot : dotProduct pt x = dotProduct p0 x + t * dotProduct dp x := by
          dsimp [pt]; rw [add_dotProduct, smul_dotProduct, smul_eq_mul]
        rw [hdot]; dsimp [B2]; nlinarith
      refine ⟨pt, ?_⟩
      have hsub := EReal.sub_le_sub hconc_pt hconj_pt
      have hlt : (delta : EReal) < ((ch0 - t * B2 : ℝ) : EReal) - ((cf0 + t * B1 : ℝ) : EReal) := by
        rw [← EReal.coe_sub, EReal.coe_lt_coe_iff]
        have hB12 : B1 + B2 = -1 := by
          dsimp [B1, B2]
          have hrow_t' := hrow_t
          rw [hmu0, zero_mul, add_zero] at hrow_t'
          exact hrow_t'
        have ht_ge : delta + 1 - (ch0 - cf0) ≤ t := le_max_right _ _
        nlinarith
      exact hlt.trans_le hsub

/-! ### Combining Dichotomy for `(b1) ∨ (b2)` and Proving Theorem 3.6 -/

private lemma fenchel_dual_qual {f h : (V → ℝ) → EReal}
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (hb : (IsClosedConvexF f ∧ IsClosedConcaveF h ∧
        (RelInt (DomE (ConjF f)) ∩ RelInt (DomE (ConcConjF h))).Nonempty) ∨
      (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧
        (DomE (ConjF f) ∩ DomE (ConcConjF h)).Nonempty)) :
    (sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} =
        sSup {v : EReal | ∃ p : V → ℝ, v = ConcConjF h p - ConjF f p}) ∧
      (∀ delta : ℝ,
        sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} = (delta : EReal) →
          ∃ x ∈ DomE f ∩ DomE h, f x - h x = (delta : EReal)) := by
  have hdich : ∀ delta : ℝ,
      (∃ x ∈ DomE f ∩ DomE h, f x - h x ≤ (delta : EReal)) ∨
        (∃ p : V → ℝ, (delta : EReal) < ConcConjF h p - ConjF f p) := by
    intro delta
    rcases hb with ⟨hcl1, hcl2, hri⟩ | ⟨hp1, hp2, hdom⟩
    · exact closed_dual_dichotomy hf hh ⟨hcl1, hcl2⟩ hri delta
    · exact polyhedral_dual_dichotomy hf hh hp1 hp2 hdom delta
  have hweak := weak_duality hf hh
  have hatt : ∀ delta : ℝ,
      sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} = (delta : EReal) →
        ∃ x ∈ DomE f ∩ DomE h, f x - h x = (delta : EReal) := by
    intro delta hdelta
    rcases hdich delta with ⟨x, hx_dom, hx_le⟩ | ⟨p, hp_gt⟩
    · refine ⟨x, hx_dom, le_antisymm hx_le ?_⟩
      rw [← hdelta]
      have hmem : f x - h x ∈ {v : EReal | ∃ x' : V → ℝ, v = f x' - h x'} := ⟨x, rfl⟩
      exact sInf_le hmem
    · have hp_le : ConcConjF h p - ConjF f p ≤ (delta : EReal) := by
        rw [← hdelta]
        have hmem : ConcConjF h p - ConjF f p ∈
            {v : EReal | ∃ p' : V → ℝ, v = ConcConjF h p' - ConjF f p'} := ⟨p, rfl⟩
        exact (le_sSup hmem).trans hweak
      exact absurd hp_le (not_le_of_gt hp_gt)
  refine ⟨?_, hatt⟩
  apply le_antisymm _ hweak
  let S_inf := sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x}
  let S_sup := sSup {v : EReal | ∃ p : V → ℝ, v = ConcConjF h p - ConjF f p}
  change S_inf ≤ S_sup
  rcases eq_top_or_lt_top S_sup with htop | hlt_top
  · rw [htop]; exact le_top
  · have hsup_ne_bot : S_sup ≠ ⊥ := by
      have hdom_dual : (DomE (ConjF f) ∩ DomE (ConcConjF h)).Nonempty := by
        rcases hb with ⟨_, _, ⟨p0, hp0f, hp0h⟩⟩ | ⟨_, _, hdom⟩
        · exact ⟨p0, hp0f.1, hp0h.1⟩
        · exact hdom
      rcases hdom_dual with ⟨p0, ⟨hp0f_top, hp0f_bot⟩, ⟨hp0h_top, hp0h_bot⟩⟩
      lift ConjF f p0 to ℝ using ⟨hp0f_top, hp0f_bot⟩ with cf0 hcf0
      lift ConcConjF h p0 to ℝ using ⟨hp0h_top, hp0h_bot⟩ with ch0 hch0
      have hle : ((ch0 - cf0 : ℝ) : EReal) ≤ S_sup := by
        apply le_sSup
        exact ⟨p0, by rw [← hcf0, ← hch0, EReal.coe_sub]⟩
      intro hbot
      rw [hbot] at hle
      exact EReal.coe_ne_bot (ch0 - cf0) (le_bot_iff.mp hle)
    lift S_sup to ℝ using ⟨hlt_top.ne, hsup_ne_bot⟩ with r_sup hr_sup
    have h_eps : ∀ n : ℕ, S_inf ≤ ((r_sup + 1 / (n + 1 : ℝ) : ℝ) : EReal) := by
      intro n
      let d_n : ℝ := r_sup + 1 / (n + 1 : ℝ)
      have hlt_dn : (r_sup : EReal) < (d_n : EReal) := by
        rw [EReal.coe_lt_coe_iff]
        dsimp [d_n]
        have : 0 < 1 / (n + 1 : ℝ) := by positivity
        linarith
      rcases hdich d_n with ⟨x, _, hx_le⟩ | ⟨p, hp_gt⟩
      · have hmem : f x - h x ∈ {v : EReal | ∃ x' : V → ℝ, v = f x' - h x'} := ⟨x, rfl⟩
        exact (sInf_le hmem).trans hx_le
      · have hp_le : ConcConjF h p - ConjF f p ≤ (r_sup : EReal) := by
          rw [hr_sup]
          have hmem : ConcConjF h p - ConjF f p ∈
              {v : EReal | ∃ p' : V → ℝ, v = ConcConjF h p' - ConjF f p'} := ⟨p, rfl⟩
          exact le_sSup hmem
        exact False.elim (not_le_of_gt hlt_dn (hp_gt.trans_le hp_le).le)
    rcases eq_top_or_lt_top S_inf with hinf_top | hinf_lt
    · have h0 := h_eps 0
      rw [hinf_top] at h0
      exact absurd (top_le_iff.mp h0) (EReal.coe_ne_top _)
    · rcases eq_bot_or_bot_lt S_inf with hinf_bot | hinf_gt
      · rw [hinf_bot]; exact bot_le
      · lift S_inf to ℝ using ⟨hinf_lt.ne, hinf_gt.ne'⟩ with r_inf hr_inf
        rw [EReal.coe_le_coe_iff]
        by_contra hgt
        push_neg at hgt
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (r_inf - r_sup))
        have hpos : 0 < r_inf - r_sup := by linarith
        have hn_pos : 0 < (n + 1 : ℝ) := by positivity
        have hlt_inv : 1 / (n + 1 : ℝ) < r_inf - r_sup := by
          rw [div_lt_iff₀ hn_pos]
          have : 1 < (n : ℝ) * (r_inf - r_sup) := (div_lt_iff₀ hpos).mp hn
          linarith
        have hle_n := EReal.coe_le_coe_iff.mp (h_eps n)
        linarith

theorem solution {V : Type*} [Fintype V] (f h : (V → ℝ) → EReal)
    (hf : IsProperConvex f) (hh : IsProperConcave h)
    (hyp : (RelInt (DomE f) ∩ RelInt (DomE h)).Nonempty ∨
      (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧ (DomE f ∩ DomE h).Nonempty) ∨
      (IsClosedConvexF f ∧ IsClosedConcaveF h ∧
        (RelInt (DomE (ConjF f)) ∩ RelInt (DomE (ConcConjF h))).Nonempty) ∨
      (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧
        (DomE (ConjF f) ∩ DomE (ConcConjF h)).Nonempty)) :
    (sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} =
        sSup {v : EReal | ∃ p : V → ℝ, v = ConcConjF h p - ConjF f p}) ∧
      (∀ delta : ℝ,
        sInf {v : EReal | ∃ x : V → ℝ, v = f x - h x} = (delta : EReal) →
          ((RelInt (DomE f) ∩ RelInt (DomE h)).Nonempty ∨
              (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧ (DomE f ∩ DomE h).Nonempty) →
            ∃ p ∈ DomE (ConjF f) ∩ DomE (ConcConjF h),
              ConcConjF h p - ConjF f p = (delta : EReal)) ∧
          ((IsClosedConvexF f ∧ IsClosedConcaveF h ∧
                (RelInt (DomE (ConjF f)) ∩ RelInt (DomE (ConcConjF h))).Nonempty) ∨
              (IsPolyhedralConvex f ∧ IsPolyhedralConcave h ∧
                (DomE (ConjF f) ∩ DomE (ConcConjF h)).Nonempty) →
            ∃ x ∈ DomE f ∩ DomE h, f x - h x = (delta : EReal))) := by
  refine ⟨?_, fun delta hdelta => ⟨fun ha => (fenchel_primal_qual hf hh ha).2 delta hdelta,
    fun hb => (fenchel_dual_qual hf hh hb).2 delta hdelta⟩⟩
  rcases hyp with ha1 | ha2 | hb1 | hb2
  · exact (fenchel_primal_qual hf hh (Or.inl ha1)).1
  · exact (fenchel_primal_qual hf hh (Or.inr ha2)).1
  · exact (fenchel_dual_qual hf hh (Or.inl hb1)).1
  · exact (fenchel_dual_qual hf hh (Or.inr hb2)).1
