-- Prove2me | solution 1 for BellmanDP.Games.stability_estimate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:59:46.919145+00:00
-- url     : https://prove2.me/submissions/0d970dfa-0d36-43c5-b767-19fae1c04a93

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

lemma st_ae {m m' : ℕ} (S : Set (Vec m)) (S' : Set (Vec m'))
    (G : Measure (Vec m)) (G' : Measure (Vec m')) [IsProbabilityMeasure G']
    (hG : G Sᶜ = 0) (hG' : G' S'ᶜ = 0) :
    ∀ᵐ z ∂(G.prod G'), z ∈ S ×ˢ S' := by
  rw [ae_iff]
  have : {a : Vec m × Vec m' | ¬ a ∈ S ×ˢ S'} = (S ×ˢ S')ᶜ := rfl
  rw [this, Set.compl_prod_eq_union]
  refine measure_union_null ?_ ?_
  · rw [Measure.prod_prod, hG, zero_mul]
  · rw [Measure.prod_prod, hG', mul_zero]

lemma st_kernel_cont {n n' m m' : ℕ} (g : GameData n n' m m') (k : ℝ) (hg : GameHyp g k)
    (f : Vec n → Vec n' → ℝ) (hf : InSolutionClass g f) (P : Vec n) (hP : P ∈ g.D)
    (P' : Vec n') (hP' : P' ∈ g.D') :
    ContinuousOn (fun z : Vec m × Vec m' => stageKernel g f P P' z.1 z.2)
      ((g.S P P' : Set (Vec m)) ×ˢ (g.S' P P' : Set (Vec m'))) := by
  have hR : ContinuousOn (fun z : Vec m × Vec m' => g.R z.1 z.2)
      ((g.S P P' : Set (Vec m)) ×ˢ (g.S' P P' : Set (Vec m'))) := hg.cont_R.continuousOn
  have hemb : Continuous (fun z : Vec m × Vec m' => ((P, P'), z)) := by fun_prop
  have hmaps : Set.MapsTo (fun z : Vec m × Vec m' => ((P, P'), z))
      ((g.S P P' : Set (Vec m)) ×ˢ (g.S' P P' : Set (Vec m'))) ((g.D ×ˢ g.D') ×ˢ Set.univ) :=
    fun z _ => ⟨⟨hP, hP'⟩, Set.mem_univ _⟩
  have hh := hg.cont_h.comp hemb.continuousOn hmaps
  have hT := hg.cont_T.comp hemb.continuousOn hmaps
  have hT' := hg.cont_T'.comp hemb.continuousOn hmaps
  have hTT : ContinuousOn (fun z : Vec m × Vec m' => (g.T P P' z.1 z.2, g.T' P P' z.1 z.2))
      ((g.S P P' : Set (Vec m)) ×ˢ (g.S' P P' : Set (Vec m'))) := hT.prodMk hT'
  have hmaps2 : Set.MapsTo (fun z : Vec m × Vec m' => (g.T P P' z.1 z.2, g.T' P P' z.1 z.2))
      ((g.S P P' : Set (Vec m)) ×ˢ (g.S' P P' : Set (Vec m'))) (g.D ×ˢ g.D') :=
    fun z hz => ⟨hg.T_mem P hP P' hP' z.1 hz.1 z.2 hz.2, hg.T'_mem P hP P' hP' z.1 hz.1 z.2 hz.2⟩
  have hfT := hf.1.comp hTT hmaps2
  exact hR.add (hh.mul hfT)

lemma st_payoff_cmp {n n' m m' : ℕ} (g : GameData n n' m m') (k : ℝ) (hg : GameHyp g k)
    (g' : GameData n n' m m') (hg' : GameHyp g' k) (hS : g'.S = g.S) (hS' : g'.S' = g.S')
    (f F : Vec n → Vec n' → ℝ) (hf : InSolutionClass g f) (hF : InSolutionClass g' F)
    (P : Vec n) (hP : P ∈ g.D) (P' : Vec n') (hP' : P' ∈ g.D') (hPg : P ∈ g'.D) (hPg' : P' ∈ g'.D')
    (M : ℝ) (hM : ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |stageKernel g f P P' u v - stageKernel g' F P P' u v| ≤ M)
    (G : Measure (Vec m)) (G' : Measure (Vec m'))
    (hG : G ∈ MixedStrategies (g.S P P' : Set (Vec m)))
    (hG' : G' ∈ MixedStrategies (g.S' P P' : Set (Vec m'))) :
    |expectedPayoff (stageKernel g f P P') G G' - expectedPayoff (stageKernel g' F P P') G G'| ≤ M := by
  have hc := st_kernel_cont g k hg f hf P hP P' hP'
  have hc' := st_kernel_cont g' k hg' F hF P hPg P' hPg'
  rw [hS, hS'] at hc'
  have hcomp : IsCompact ((g.S P P' : Set (Vec m)) ×ˢ (g.S' P P' : Set (Vec m'))) :=
    (g.S P P').isCompact.prod (g.S' P P').isCompact
  have hmeas : MeasurableSet ((g.S P P' : Set (Vec m)) ×ˢ (g.S' P P' : Set (Vec m'))) :=
    hcomp.isClosed.measurableSet
  haveI := hG'.1
  have hae := st_ae _ _ G G' hG.2 hG'.2
  have hrestr : (G.prod G').restrict ((g.S P P' : Set (Vec m)) ×ˢ (g.S' P P' : Set (Vec m'))) =
      G.prod G' := Measure.restrict_eq_self_of_ae_mem hae
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hc
  obtain ⟨C₁, hC₁⟩ := hcomp.exists_bound_of_continuousOn hc'
  refine bl_payoff_cmp _ _ _ _ G G' hG hG' ?_ ?_ C (fun u hu v hv => hC (u, v) ⟨hu, hv⟩)
    C₁ (fun u hu v hv => hC₁ (u, v) ⟨hu, hv⟩) M hM
  · rw [← hrestr]; exact hc.aestronglyMeasurable hmeas
  · rw [← hrestr]; exact hc'.aestronglyMeasurable hmeas

lemma st_norm_le {n : ℕ} (P : Vec n) : ‖P‖ ≤ l1norm P := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (P i))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |P j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

lemma st_l1_nonneg {n : ℕ} (P : Vec n) : 0 ≤ l1norm P :=
  Finset.sum_nonneg fun i _ => abs_nonneg (P i)

theorem st_core {n n' m m' : ℕ} (g : GameData n n' m m') (R' : Vec m → Vec m' → ℝ)
    (k : ℝ) (hg : GameHyp g k) (hg' : GameHyp { g with R := R' } k)
    (f F : Vec n → Vec n' → ℝ) (hf : InSolutionClass g f) (hfs : IsGameSolution g f)
    (hF : InSolutionClass { g with R := R' } F) (hFs : IsGameSolution { g with R := R' } F)
    (Δ : ℝ → ℝ)
    (hΔ : ∀ c : ℝ, ∀ P ∈ g.D, ∀ P' ∈ g.D', l1norm P + l1norm P' ≤ c →
      ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')), |g.R u v - R' u v| ≤ Δ c)
    (P : Vec n) (hP : P ∈ g.D) (P' : Vec n') (hP' : P' ∈ g.D') (c : ℝ)
    (hc : l1norm P + l1norm P' ≤ c) (hsum : Summable (fun j : ℕ => Δ (k ^ j * c))) :
    |f P P' - F P P'| ≤ ∑' j : ℕ, Δ (k ^ j * c) := by
  set g' : GameData n n' m m' := { g with R := R' } with hg'def
  -- one step
  have step : ∀ P ∈ g.D, ∀ P' ∈ g.D', ∀ M : ℝ, (∀ u ∈ (g.S P P' : Set (Vec m)),
      ∀ v ∈ (g.S' P P' : Set (Vec m')),
      |g.R u v - R' u v| + |g.h P P' u v| *
        |f (g.T P P' u v) (g.T' P P' u v) - F (g.T P P' u v) (g.T' P P' u v)| ≤ M) →
      |f P P' - F P P'| ≤ M := by
    intro P hP P' hP' M hM
    refine bl_value_cmp _ _ _ _ _ _ M (hfs P hP P' hP') (hFs P hP P' hP') ?_
    intro G hG G' hG'
    refine st_payoff_cmp g k hg g' hg' rfl rfl f F hf hF P hP P' hP' hP hP' M ?_ G G' hG hG'
    intro u hu v hv
    refine le_trans ?_ (hM u hu v hv)
    simp only [stageKernel, g']
    rw [show g.R u v + g.h P P' u v * f (g.T P P' u v) (g.T' P P' u v) -
        (R' u v + g.h P P' u v * F (g.T P P' u v) (g.T' P P' u v)) =
        (g.R u v - R' u v) + g.h P P' u v * (f (g.T P P' u v) (g.T' P P' u v) -
          F (g.T P P' u v) (g.T' P P' u v)) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
  -- nonnegativity of Δ at nonneg arguments
  have hΔnn : ∀ r, 0 ≤ r → 0 ≤ Δ r := by
    intro r hr
    obtain ⟨u, hu⟩ := (g.S 0 0).nonempty
    obtain ⟨v, hv⟩ := (g.S' 0 0).nonempty
    refine le_trans (abs_nonneg _) (hΔ r 0 hg.zero_mem_D 0 hg.zero_mem_D' ?_ u hu v hv)
    simp [l1norm, hr]
  have hc0 : 0 ≤ c := le_trans (add_nonneg (st_l1_nonneg P) (st_l1_nonneg P')) hc
  -- continuity at 0
  have hcont : ContinuousWithinAt (fun z : Vec n × Vec n' => f z.1 z.2 - F z.1 z.2)
      (g.D ×ˢ g.D') (0, 0) :=
    (hf.1.sub hF.1) _ ⟨hg.zero_mem_D, hg.zero_mem_D'⟩
  rw [Metric.continuousWithinAt_iff] at hcont
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hδε⟩ := hcont ε hε
  have h00 : f 0 0 - F 0 0 = 0 := by rw [hf.2]; exact sub_eq_zero.2 hF.2.symm
  have base : ∀ Q ∈ g.D, ∀ Q' ∈ g.D', l1norm Q + l1norm Q' < δ → |f Q Q' - F Q Q'| ≤ ε := by
    intro Q hQ Q' hQ' hlt
    have hd : dist (Q, Q') ((0 : Vec n), (0 : Vec n')) < δ := by
      rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
      refine max_lt ?_ ?_
      · linarith [st_norm_le Q, st_l1_nonneg Q']
      · linarith [st_norm_le Q', st_l1_nonneg Q]
    have := hδε (x := (Q, Q')) ⟨hQ, hQ'⟩ hd
    rw [Real.dist_eq] at this
    simp only [h00, sub_zero] at this
    exact this.le
  have claim : ∀ N : ℕ, ∀ c : ℝ, 0 ≤ c → k ^ N * c < δ → ∀ Q ∈ g.D, ∀ Q' ∈ g.D',
      l1norm Q + l1norm Q' ≤ c →
      |f Q Q' - F Q Q'| ≤ (∑ j ∈ Finset.range N, Δ (k ^ j * c)) + ε := by
    intro N
    induction N with
    | zero =>
      intro c hc0 hlt Q hQ Q' hQ' hQc
      simp only [pow_zero, one_mul] at hlt
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      exact base Q hQ Q' hQ' (lt_of_le_of_lt hQc hlt)
    | succ N ih =>
      intro c hc0 hlt Q hQ Q' hQ' hQc
      have hkc : 0 ≤ k * c := mul_nonneg hg.k_nonneg hc0
      have hlt' : k ^ N * (k * c) < δ := by
        rw [← mul_assoc, ← pow_succ]; exact hlt
      rw [Finset.sum_range_succ']
      have hre : (∑ j ∈ Finset.range N, Δ (k ^ (j + 1) * c)) =
          ∑ j ∈ Finset.range N, Δ (k ^ j * (k * c)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ, mul_assoc]
      rw [hre, pow_zero, one_mul]
      refine step Q hQ Q' hQ' _ fun u hu v hv => ?_
      have h1 := hΔ c Q hQ Q' hQ' hQc u hu v hv
      have hTr : l1norm (g.T Q Q' u v) + l1norm (g.T' Q Q' u v) ≤ k * c :=
        (hg.shrinking Q hQ Q' hQ' u hu v hv).trans
          (mul_le_mul_of_nonneg_left hQc hg.k_nonneg)
      have h2 := ih (k * c) hkc hlt' _ (hg.T_mem Q hQ Q' hQ' u hu v hv) _
        (hg.T'_mem Q hQ Q' hQ' u hu v hv) hTr
      have h3 : |g.h Q Q' u v| * |f (g.T Q Q' u v) (g.T' Q Q' u v) - F (g.T Q Q' u v) (g.T' Q Q' u v)|
          ≤ |f (g.T Q Q' u v) (g.T' Q Q' u v) - F (g.T Q Q' u v) (g.T' Q Q' u v)| :=
        mul_le_of_le_one_left (abs_nonneg _) (hg.h_le_one Q hQ Q' hQ' u hu v hv)
      linarith
  -- choose N
  have htend : Filter.Tendsto (fun N : ℕ => k ^ N * c) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hg.k_nonneg hg.k_lt_one).mul_const c
    simpa using this
  obtain ⟨N, hN⟩ := (htend.eventually (gt_mem_nhds hδ)).exists
  have := claim N c hc0 hN P hP P' hP' hc
  have hle : (∑ j ∈ Finset.range N, Δ (k ^ j * c)) ≤ ∑' j : ℕ, Δ (k ^ j * c) :=
    hsum.sum_le_tsum _ fun j _ => hΔnn _ (mul_nonneg (pow_nonneg hg.k_nonneg j) hc0)
  linarith

end BellmanDP.Games

open BellmanDP.Games


theorem solution {n n' m m' : ℕ} (g : GameData n n' m m') (R' : Vec m → Vec m' → ℝ)
    (k : ℝ) (hg : GameHyp g k) (hg' : GameHyp { g with R := R' } k)
    (f F : Vec n → Vec n' → ℝ) (hf : InSolutionClass g f) (hfs : IsGameSolution g f)
    (hF : InSolutionClass { g with R := R' } F) (hFs : IsGameSolution { g with R := R' } F)
    (Δ : ℝ → ℝ)
    (hΔ : ∀ c : ℝ, ∀ P ∈ g.D, ∀ P' ∈ g.D', l1norm P + l1norm P' ≤ c →
      ∀ u ∈ (g.S P P' : Set (Vec m)), ∀ v ∈ (g.S' P P' : Set (Vec m')), |g.R u v - R' u v| ≤ Δ c)
    (P : Vec n) (hP : P ∈ g.D) (P' : Vec n') (hP' : P' ∈ g.D') (c : ℝ)
    (hc : l1norm P + l1norm P' ≤ c) (hsum : Summable (fun j : ℕ => Δ (k ^ j * c))) :
    |f P P' - F P P'| ≤ ∑' j : ℕ, Δ (k ^ j * c) := by
  exact st_core g R' k hg hg' f F hf hfs hF hFs Δ hΔ P hP P' hP' c hc hsum
