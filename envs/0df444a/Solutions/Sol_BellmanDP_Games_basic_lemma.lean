-- Prove2me | solution 1 for BellmanDP.Games.basic_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:57:44.748987+00:00
-- url     : https://prove2.me/submissions/2823cd82-039f-4009-9e8f-e1af03e737ee

import Mathlib
import Definitions.Def_BellmanDP_Games_MultiStage



namespace BellmanDP.Games

open MeasureTheory

lemma bl_value_cmp {α β : Type*} (E E₁ : α → β → ℝ) (X : Set α) (Y : Set β) (L L₁ M : ℝ)
    (hL : IsMaxMinMinMaxValue E X Y L) (hL₁ : IsMaxMinMinMaxValue E₁ X Y L₁)
    (hM : ∀ x ∈ X, ∀ y ∈ Y, |E x y - E₁ x y| ≤ M) : |L - L₁| ≤ M := by
  obtain ⟨⟨x0, hx0, hx0l⟩, -⟩ := hL.1
  obtain ⟨⟨y0, hy0, hy0g⟩, -⟩ := hL.2
  obtain ⟨⟨x1, hx1, hx1l⟩, -⟩ := hL₁.1
  obtain ⟨⟨y1, hy1, hy1g⟩, -⟩ := hL₁.2
  have a1 : L ≤ E x0 y1 := hx0l.2 ⟨y1, hy1, rfl⟩
  have a2 : E₁ x0 y1 ≤ L₁ := hy1g.2 ⟨x0, hx0, rfl⟩
  have a3 : L₁ ≤ E₁ x1 y0 := hx1l.2 ⟨y0, hy0, rfl⟩
  have a4 : E x1 y0 ≤ L := hy0g.2 ⟨x1, hx1, rfl⟩
  have b1 := abs_le.1 (hM x0 hx0 y1 hy1)
  have b2 := abs_le.1 (hM x1 hx1 y0 hy0)
  rw [abs_le]; constructor <;> linarith

lemma bl_payoff_eq {m m' : ℕ} (S : Set (Vec m)) (S' : Set (Vec m')) (K : Vec m → Vec m' → ℝ)
    (G : Measure (Vec m)) (G' : Measure (Vec m')) [IsProbabilityMeasure G]
    [IsProbabilityMeasure G'] (hG : G Sᶜ = 0) (hG' : G' S'ᶜ = 0)
    (hK : AEStronglyMeasurable (fun z : Vec m × Vec m' => K z.1 z.2) (G.prod G'))
    (C : ℝ) (hC : ∀ u ∈ S, ∀ v ∈ S', |K u v| ≤ C) :
    Integrable (fun z : Vec m × Vec m' => K z.1 z.2) (G.prod G') ∧
      expectedPayoff K G G' = ∫ z, K z.1 z.2 ∂(G.prod G') ∧
      ∀ᵐ z ∂(G.prod G'), z ∈ S ×ˢ S' := by
  have hae : ∀ᵐ z ∂(G.prod G'), z ∈ S ×ˢ S' := by
    rw [ae_iff]
    have : {a : Vec m × Vec m' | ¬ a ∈ S ×ˢ S'} = (S ×ˢ S')ᶜ := rfl
    rw [this, Set.compl_prod_eq_union]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, hG, zero_mul]
    · rw [Measure.prod_prod, hG', mul_zero]
  have hint : Integrable (fun z : Vec m × Vec m' => K z.1 z.2) (G.prod G') := by
    refine Integrable.mono' (integrable_const C) hK ?_
    filter_upwards [hae] with z hz
    exact hC z.1 hz.1 z.2 hz.2
  refine ⟨hint, ?_, hae⟩
  unfold expectedPayoff
  exact (integral_prod (fun z : Vec m × Vec m' => K z.1 z.2) hint).symm

lemma bl_payoff_cmp {m m' : ℕ} (S : Set (Vec m)) (S' : Set (Vec m')) (K K₁ : Vec m → Vec m' → ℝ)
    (G : Measure (Vec m)) (G' : Measure (Vec m')) (hG : G ∈ MixedStrategies S)
    (hG' : G' ∈ MixedStrategies S')
    (hK : AEStronglyMeasurable (fun z : Vec m × Vec m' => K z.1 z.2) (G.prod G'))
    (hK₁ : AEStronglyMeasurable (fun z : Vec m × Vec m' => K₁ z.1 z.2) (G.prod G'))
    (C : ℝ) (hC : ∀ u ∈ S, ∀ v ∈ S', |K u v| ≤ C)
    (C₁ : ℝ) (hC₁ : ∀ u ∈ S, ∀ v ∈ S', |K₁ u v| ≤ C₁)
    (M : ℝ) (hM : ∀ u ∈ S, ∀ v ∈ S', |K u v - K₁ u v| ≤ M) :
    |expectedPayoff K G G' - expectedPayoff K₁ G G'| ≤ M := by
  haveI := hG.1
  haveI := hG'.1
  obtain ⟨hi, he, hae⟩ := bl_payoff_eq S S' K G G' hG.2 hG'.2 hK C hC
  obtain ⟨hi₁, he₁, -⟩ := bl_payoff_eq S S' K₁ G G' hG.2 hG'.2 hK₁ C₁ hC₁
  rw [he, he₁, ← integral_sub hi hi₁]
  have := norm_integral_le_of_norm_le_const (μ := G.prod G')
    (f := fun z : Vec m × Vec m' => K z.1 z.2 - K₁ z.1 z.2) (C := M) (by
      filter_upwards [hae] with z hz
      exact hM z.1 hz.1 z.2 hz.2)
  simpa using this

theorem bl_core {n n' m m' : ℕ} (g : GameData n n' m m') (R₁ : Vec m → Vec m' → ℝ)
    (f F : Vec n → Vec n' → ℝ) (P : Vec n) (P' : Vec n') (L L₁ : ℝ)
    (hmeas : Measurable (fun z : Vec m × Vec m' => stageKernel g f P P' z.1 z.2))
    (hmeas₁ : Measurable (fun z : Vec m × Vec m' => stageKernel { g with R := R₁ } F P P' z.1 z.2))
    (hbdd : ∃ C : ℝ, ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |stageKernel g f P P' u v| ≤ C)
    (hbdd₁ : ∃ C : ℝ, ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |stageKernel { g with R := R₁ } F P P' u v| ≤ C)
    (hL : ValueAt g (stageKernel g f P P') P P' L)
    (hL₁ : ValueAt g (stageKernel { g with R := R₁ } F P P') P P' L₁)
    (M : ℝ)
    (hM : ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |g.R u v - R₁ u v| + |g.h P P' u v| *
        |f (g.T P P' u v) (g.T' P P' u v) - F (g.T P P' u v) (g.T' P P' u v)| ≤ M) :
    |L - L₁| ≤ M := by
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨C₁, hC₁⟩ := hbdd₁
  refine bl_value_cmp _ _ _ _ L L₁ M hL hL₁ ?_
  intro G hG G' hG'
  refine bl_payoff_cmp _ _ _ _ G G' hG hG' hmeas.aestronglyMeasurable
    hmeas₁.aestronglyMeasurable C hC C₁ hC₁ M ?_
  intro u hu v hv
  refine le_trans ?_ (hM u hu v hv)
  simp only [stageKernel]
  rw [show g.R u v + g.h P P' u v * f (g.T P P' u v) (g.T' P P' u v) -
      (R₁ u v + g.h P P' u v * F (g.T P P' u v) (g.T' P P' u v)) =
      (g.R u v - R₁ u v) + g.h P P' u v * (f (g.T P P' u v) (g.T' P P' u v) -
        F (g.T P P' u v) (g.T' P P' u v)) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]

end BellmanDP.Games

open BellmanDP.Games


theorem solution {n n' m m' : ℕ} (g : GameData n n' m m') (R₁ : Vec m → Vec m' → ℝ)
    (f F : Vec n → Vec n' → ℝ) (P : Vec n) (P' : Vec n') (L L₁ : ℝ)
    (hmeas : Measurable (fun z : Vec m × Vec m' => stageKernel g f P P' z.1 z.2))
    (hmeas₁ : Measurable (fun z : Vec m × Vec m' => stageKernel { g with R := R₁ } F P P' z.1 z.2))
    (hbdd : ∃ C : ℝ, ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |stageKernel g f P P' u v| ≤ C)
    (hbdd₁ : ∃ C : ℝ, ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |stageKernel { g with R := R₁ } F P P' u v| ≤ C)
    (hL : ValueAt g (stageKernel g f P P') P P' L)
    (hL₁ : ValueAt g (stageKernel { g with R := R₁ } F P P') P P' L₁)
    (M : ℝ)
    (hM : ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |g.R u v - R₁ u v| + |g.h P P' u v| *
        |f (g.T P P' u v) (g.T' P P' u v) - F (g.T P P' u v) (g.T' P P' u v)| ≤ M) :
    |L - L₁| ≤ M := by
  exact bl_core g R₁ f F P P' L L₁ hmeas hmeas₁ hbdd hbdd₁ hL hL₁ M hM
