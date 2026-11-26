-- Prove2me | solution 1 for FullBallLem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:31.364913+00:00
-- url     : https://prove2.me/submissions/7c005238-ed40-4c07-bbd9-99c751ac1981

import Definitions.Def_Tablet_LargeBallLem
import Definitions.Def_Tablet_DGammaBallMeasure
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_C1SmallBall
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_BigEdgeWindowPacking
import Definitions.Def_Tablet_StraddleAtMostOneEdge
import Definitions.Def_Tablet_ResolutionCoverBallMeasure
import Definitions.Def_Tablet_ArcLocalization
import Definitions.Def_Tablet_FullBallLem
import Theorems.Thm_ArcLocalization
import Theorems.Thm_BigEdgeWindowPacking
import Theorems.Thm_C1SmallBall
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_DGammaBallMeasure
import Theorems.Thm_LargeBallLem
import Theorems.Thm_ResolutionCoverBallMeasure
import Theorems.Thm_StraddleAtMostOneEdge


set_option autoImplicit false
open MeasureTheory Set ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Curve E) (δ ε : ℝ) (n : ℕ) (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε < 1)
    (hden : IsDeltaEpsN γ δ ε n) (hlsi : IsLSI γ δ ε) :
    morreyNorm (curveMeasure γ) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 4) := by
-- BODY
  obtain ⟨k₀, s₀, hres, hsmall, hsmallc⟩ := hden
  have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hcase : γ.len ≤ 2 * ε⁻¹ * δ
  · -- Case A: the whole curve is short, and `C1SmallBall` bounds the Morrey norm directly.
    have hm : ∀ p q : ℕ, p ≤ q → q ≤ k₀ → s₀ p ≤ s₀ q := by
      intro p q hpq hq
      exact hres.1 (Set.mem_Icc.mpr ⟨Nat.zero_le _, hpq.trans hq⟩)
        (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) hpq
    have hcont : ∀ j ∈ Finset.Icc 1 k₀, 0 ≤ s₀ (j - 1) ∧ s₀ j ≤ γ.len := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      refine ⟨?_, ?_⟩
      · have h := hm 0 (j - 1) (Nat.zero_le _) (by omega)
        rw [hres.2.1] at h; exact h
      · have h := hm j k₀ hj.2 le_rfl
        rw [hres.2.2.1] at h; exact h
    -- big edges: at most `2ε⁻¹` of them fit in `[0, γ.len]`
    have hbig := BigEdgeWindowPacking k₀ s₀ δ 0 γ.len hδ hres.1 γ.len_nonneg
    have heqbig : (Finset.Icc 1 k₀).filter
        (fun j => (0:ℝ) ≤ s₀ (j - 1) ∧ s₀ j ≤ γ.len ∧ δ ≤ s₀ j - s₀ (j - 1))
        = (Finset.Icc 1 k₀).filter (fun j => δ ≤ s₀ j - s₀ (j - 1)) := by
      apply Finset.filter_congr
      intro j hj
      obtain ⟨h1, h2⟩ := hcont j hj
      simp [h1, h2]
    rw [heqbig] at hbig
    -- small edges: clause (i) of `IsDeltaEpsN` at the full window `[0, γ.len]`
    have hsm := hsmall 0 γ.len le_rfl γ.len_nonneg le_rfl (by linarith)
    have heqsmall : (Finset.Icc 1 k₀).filter
        (fun j => (0:ℝ) ≤ s₀ (j - 1) ∧ s₀ j ≤ γ.len ∧ s₀ j - s₀ (j - 1) < δ)
        = (Finset.Icc 1 k₀).filter (fun j => ¬ (δ ≤ s₀ j - s₀ (j - 1))) := by
      apply Finset.filter_congr
      intro j hj
      obtain ⟨h1, h2⟩ := hcont j hj
      simp [h1, h2, not_le]
    rw [heqsmall] at hsm
    -- the two families exhaust the resolution
    have hcards : ((Finset.Icc 1 k₀).filter (fun j => δ ≤ s₀ j - s₀ (j - 1))).card
        + ((Finset.Icc 1 k₀).filter (fun j => ¬ (δ ≤ s₀ j - s₀ (j - 1)))).card = k₀ := by
      rw [Finset.card_filter_add_card_filter_not, Nat.card_Icc]
      omega
    have hbig' : (((Finset.Icc 1 k₀).filter (fun j => δ ≤ s₀ j - s₀ (j - 1))).card : ℝ)
        ≤ 2 * ε⁻¹ := by
      have h1 : (((Finset.Icc 1 k₀).filter (fun j => δ ≤ s₀ j - s₀ (j - 1))).card : ℝ) * δ
          ≤ (2 * ε⁻¹) * δ := by nlinarith
      exact le_of_mul_le_mul_right (by linarith [h1]) hδ
    have hsm' : (((Finset.Icc 1 k₀).filter (fun j => ¬ (δ ≤ s₀ j - s₀ (j - 1)))).card : ℝ)
        ≤ (n : ℝ) := by exact_mod_cast hsm
    have hk0 : (k₀ : ℝ) ≤ 2 * ε⁻¹ + (n : ℝ) := by
      have : ((((Finset.Icc 1 k₀).filter (fun j => δ ≤ s₀ j - s₀ (j - 1))).card : ℝ)
          + (((Finset.Icc 1 k₀).filter (fun j => ¬ (δ ≤ s₀ j - s₀ (j - 1)))).card : ℝ))
          = (k₀ : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hcards
      linarith
    refine (C1SmallBall γ k₀ ⟨s₀, hres⟩).trans ?_
    have hrw : (2 : ℝ≥0∞) * (k₀ : ℝ≥0∞) = ENNReal.ofReal (2 * (k₀ : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_natCast]
      norm_num
    rw [hrw]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · -- Case B: the curve is long; bound each ball individually.
    push_neg at hcase
    have hA : (0:ℝ) ≤ 4 * ε⁻¹ + 2 * (n : ℝ) + 4 := by linarith
    simp only [morreyNorm]
    refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
    refine ENNReal.div_le_of_le_mul ?_
    rw [← ENNReal.ofReal_mul hA]
    rcases lt_or_ge r (δ / 2) with hrs | hrb
    · -- Sub-case `0 < r < δ/2`: Steps 1--5 of the .tex proof.
      have hmeasγ : Measurable γ.toFun := (CurveLipschitz γ).continuous.measurable
      have heq : curveMeasure γ (Metric.closedBall x r) =
          volume {t ∈ Set.Icc (0:ℝ) γ.len | γ.toFun t ∈ Metric.closedBall x r} := by
        rw [curveMeasure, Measure.map_apply hmeasγ measurableSet_closedBall,
          Measure.restrict_apply (hmeasγ measurableSet_closedBall)]
        congr 1
        ext t
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
        tauto
      by_cases hne : ∃ u ∈ Set.Icc (0:ℝ) γ.len, γ.toFun u ∈ Metric.closedBall x r
      · obtain ⟨u, hu, hux⟩ := hne
        -- `ρ := ε⁻¹δ`; note `δ < ρ` because `ε < 1`.
        have hee : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
        have hinv1 : (1:ℝ) < ε⁻¹ := by nlinarith
        have hδρ : δ < ε⁻¹ * δ := by nlinarith
        -- Step 1: the part of `γ` in `B̄_r(x)` has parameters inside the arc
        -- `I = {t : d_γ(u,t) < ρ}`.
        have hstep1 : {t ∈ Set.Icc (0:ℝ) γ.len | γ.toFun t ∈ Metric.closedBall x r} ⊆
            {t ∈ Set.Icc (0:ℝ) γ.len | dGamma γ u t < ε⁻¹ * δ} := by
          rintro t ⟨ht, htx⟩
          refine ⟨ht, ?_⟩
          have hdist : dist (γ.toFun u) (γ.toFun t) ≤ 2 * r := by
            calc dist (γ.toFun u) (γ.toFun t)
                ≤ dist (γ.toFun u) x + dist x (γ.toFun t) := dist_triangle _ _ _
              _ ≤ r + r := add_le_add hux (by rw [dist_comm]; exact htx)
              _ = 2 * r := by ring
          rcases lt_or_ge (dGamma γ u t) δ with hlt | hge
          · linarith
          · have hls := hlsi.2 u hu t ht hge
            have h2 : ε * dGamma γ u t < δ := by linarith
            have h3 : ε * dGamma γ u t < ε * (ε⁻¹ * δ) := by
              rw [← mul_assoc, hee, one_mul]; exact h2
            exact lt_of_mul_lt_mul_left h3 hε.le
        -- Steps 2--4: the arc `I` is covered by at most `2ε⁻¹+n+2` edges of `(k₀,s₀)`.
        have hsteps234 : ∃ J : Finset ℕ, J ⊆ Finset.Icc 1 k₀ ∧
            (J.card : ℝ) ≤ 2 * ε⁻¹ + (n : ℝ) + 2 ∧
            {t ∈ Set.Icc (0:ℝ) γ.len | dGamma γ u t < ε⁻¹ * δ} ⊆
              ⋃ j ∈ J, Set.Icc (s₀ (j - 1)) (s₀ j) := by
          have hρ : 0 < ε⁻¹ * δ := mul_pos hεinv hδ
          have hm : ∀ p q : ℕ, p ≤ q → q ≤ k₀ → s₀ p ≤ s₀ q := by
            intro p q hpq hq
            exact hres.1 (Set.mem_Icc.mpr ⟨Nat.zero_le _, hpq.trans hq⟩)
              (Set.mem_Icc.mpr ⟨Nat.zero_le _, hq⟩) hpq
          have hs0 : s₀ 0 = 0 := hres.2.1
          have hsk : s₀ k₀ = γ.len := hres.2.2.1
          have hk1 : 1 ≤ k₀ := by
            rcases Nat.eq_zero_or_pos k₀ with h | h
            · exfalso; rw [h, hs0] at hsk; nlinarith
            · exact h
          -- generic four- and five-fold union card bounds
          have hcard4 : ∀ A B C D : Finset ℕ,
              (A ∪ B ∪ C ∪ D).card ≤ A.card + B.card + C.card + D.card := by
            intro A B C D
            calc (A ∪ B ∪ C ∪ D).card ≤ (A ∪ B ∪ C).card + D.card := Finset.card_union_le _ _
              _ ≤ ((A ∪ B).card + C.card) + D.card :=
                  Nat.add_le_add_right (Finset.card_union_le _ _) _
              _ ≤ ((A.card + B.card) + C.card) + D.card :=
                  Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
          have hcard5 : ∀ A B C D F : Finset ℕ,
              (A ∪ B ∪ C ∪ D ∪ F).card ≤ A.card + B.card + C.card + D.card + F.card := by
            intro A B C D F
            calc (A ∪ B ∪ C ∪ D ∪ F).card ≤ (A ∪ B ∪ C ∪ D).card + F.card :=
                  Finset.card_union_le _ _
              _ ≤ (A.card + B.card + C.card + D.card) + F.card :=
                  Nat.add_le_add_right (hcard4 _ _ _ _) _
          -- every parameter in `[0,γ.len]` lies on some edge of the resolution
          have hfind : ∀ K : ℕ, ∀ v : ℝ, s₀ 0 ≤ v → v ≤ s₀ K →
              (v = s₀ 0 ∧ K = 0) ∨ ∃ j, 1 ≤ j ∧ j ≤ K ∧ s₀ (j - 1) ≤ v ∧ v ≤ s₀ j := by
            intro K
            induction K with
            | zero => intro v h1 h2; exact Or.inl ⟨le_antisymm h2 h1, rfl⟩
            | succ m ih =>
              intro v h1 h2
              rcases lt_or_ge (s₀ m) v with h | h
              · exact Or.inr ⟨m + 1, by omega, le_rfl, by simpa using h.le, h2⟩
              · rcases ih v h1 h with ⟨hv, hm0⟩ | ⟨j, hj1, hjm, hja, hjb⟩
                · subst hm0
                  exact Or.inr ⟨1, le_rfl, le_rfl, by simpa using hv.ge, by simpa using h2⟩
                · exact Or.inr ⟨j, hj1, by omega, hja, hjb⟩
          have hedge : ∀ v : ℝ, 0 ≤ v → v ≤ γ.len →
              ∃ j, 1 ≤ j ∧ j ≤ k₀ ∧ s₀ (j - 1) ≤ v ∧ v ≤ s₀ j := by
            intro v hv0 hvl
            rcases hfind k₀ v (by rw [hs0]; exact hv0) (by rw [hsk]; exact hvl) with ⟨_, h⟩ | h
            · exfalso; omega
            · exact h
          rcases ArcLocalization γ u (ε⁻¹ * δ) hu hρ (by rw [← mul_assoc]; exact hcase) with
            ⟨t, t', ht0, htt, htl, htlen, hIsub, hep, hep'⟩ |
            ⟨hcl, t, t', ht0, htt, htl, htlen, hIsub, hep, hep'⟩
          · -- Branch A: the arc sits inside the genuine subinterval `[t,t']`.
            have hb := BigEdgeWindowPacking k₀ s₀ δ t t' hδ hres.1 htt
            have hsm := hsmall t t' ht0 htt htl (by rw [mul_assoc]; exact htlen)
            have hst := StraddleAtMostOneEdge k₀ s₀ t hres.1
            have hst' := StraddleAtMostOneEdge k₀ s₀ t' hres.1
            have hcA : ((((Finset.Icc 1 k₀).filter
                (fun j => t ≤ s₀ (j - 1) ∧ s₀ j ≤ t' ∧ δ ≤ s₀ j - s₀ (j - 1))).card : ℕ) : ℝ)
                ≤ 2 * ε⁻¹ := by
              refine le_of_mul_le_mul_right (hb.trans ?_) hδ
              rw [mul_assoc]; linarith
            have hcB : ((((Finset.Icc 1 k₀).filter
                (fun j => t ≤ s₀ (j - 1) ∧ s₀ j ≤ t' ∧ s₀ j - s₀ (j - 1) < δ)).card : ℕ) : ℝ)
                ≤ (n : ℝ) := by exact_mod_cast hsm
            have hcC : ((((Finset.Icc 1 k₀).filter
                (fun j => s₀ (j - 1) < t ∧ t < s₀ j)).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hst
            have hcD : ((((Finset.Icc 1 k₀).filter
                (fun j => s₀ (j - 1) < t' ∧ t' < s₀ j)).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hst'
            refine ⟨(Finset.Icc 1 k₀).filter
                  (fun j => t ≤ s₀ (j - 1) ∧ s₀ j ≤ t' ∧ δ ≤ s₀ j - s₀ (j - 1)) ∪
                (Finset.Icc 1 k₀).filter
                  (fun j => t ≤ s₀ (j - 1) ∧ s₀ j ≤ t' ∧ s₀ j - s₀ (j - 1) < δ) ∪
                (Finset.Icc 1 k₀).filter (fun j => s₀ (j - 1) < t ∧ t < s₀ j) ∪
                (Finset.Icc 1 k₀).filter (fun j => s₀ (j - 1) < t' ∧ t' < s₀ j), ?_, ?_, ?_⟩
            · intro j hj
              simp only [Finset.mem_union, Finset.mem_filter] at hj
              tauto
            · refine le_trans (Nat.cast_le.mpr (hcard4 _ _ _ _)) ?_
              push_cast
              linarith
            · rintro v ⟨⟨hv0, hvl⟩, hvI⟩
              obtain ⟨j, hj1, hjk, hja, hjb⟩ := hedge v hv0 hvl
              obtain ⟨hvt, hvt'⟩ := Set.mem_Icc.mp (hIsub ⟨⟨hv0, hvl⟩, hvI⟩)
              simp only [Set.mem_iUnion, Set.mem_Icc, exists_prop]
              refine ⟨j, ?_, hja, hjb⟩
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
              by_cases h1 : t ≤ s₀ (j - 1)
              · by_cases h2 : s₀ j ≤ t'
                · rcases lt_or_ge (s₀ j - s₀ (j - 1)) δ with hlt | hge
                  · exact Or.inl (Or.inl (Or.inr ⟨⟨hj1, hjk⟩, h1, h2, hlt⟩))
                  · exact Or.inl (Or.inl (Or.inl ⟨⟨hj1, hjk⟩, h1, h2, hge⟩))
                · replace h2 := not_le.mp h2
                  refine Or.inr ⟨⟨hj1, hjk⟩, ?_, h2⟩
                  rcases lt_or_ge (s₀ (j - 1)) t' with h | h
                  · exact h
                  · exfalso
                    have hveq : v = t' := le_antisymm hvt' (h.trans hja)
                    rcases hep' with he | he
                    · have hle : s₀ j ≤ γ.len := by rw [← hsk]; exact hm j k₀ hjk le_rfl
                      rw [he] at h2; linarith
                    · rw [hveq, he] at hvI; linarith
              · replace h1 := not_le.mp h1
                refine Or.inl (Or.inr ⟨⟨hj1, hjk⟩, h1, ?_⟩)
                rcases lt_or_ge t (s₀ j) with h | h
                · exact h
                · exfalso
                  have hveq : v = t := le_antisymm (hjb.trans h) hvt
                  rcases hep with he | he
                  · have hge : (0:ℝ) ≤ s₀ (j - 1) := by
                      rw [← hs0]; exact hm 0 (j - 1) (Nat.zero_le _) (by omega)
                    rw [he] at h1; linarith
                  · rw [hveq, he] at hvI; linarith
          · -- Branch B: the arc wraps around the basepoint of the closed curve.
            have hb1 := BigEdgeWindowPacking k₀ s₀ δ t γ.len hδ hres.1 htl
            have hb2 := BigEdgeWindowPacking k₀ s₀ δ 0 t' hδ hres.1 ht0
            have hsm := hsmallc hcl t t' ht0 htt htl (by rw [mul_assoc]; exact htlen)
            have hst := StraddleAtMostOneEdge k₀ s₀ t hres.1
            have hst' := StraddleAtMostOneEdge k₀ s₀ t' hres.1
            have hcA : ((((Finset.Icc 1 k₀).filter
                  (fun j => t ≤ s₀ (j - 1) ∧ s₀ j ≤ γ.len ∧ δ ≤ s₀ j - s₀ (j - 1))).card : ℕ) : ℝ)
                + ((((Finset.Icc 1 k₀).filter
                  (fun j => (0:ℝ) ≤ s₀ (j - 1) ∧ s₀ j ≤ t' ∧ δ ≤ s₀ j - s₀ (j - 1))).card : ℕ) : ℝ)
                ≤ 2 * ε⁻¹ := by
              refine le_of_mul_le_mul_right ?_ hδ
              rw [add_mul, mul_assoc]
              linarith
            have hcB : ((((Finset.Icc 1 k₀).filter
                (fun j => (t ≤ s₀ (j - 1) ∨ s₀ j ≤ t') ∧ s₀ j - s₀ (j - 1) < δ)).card : ℕ) : ℝ)
                ≤ (n : ℝ) := by exact_mod_cast hsm
            have hcC : ((((Finset.Icc 1 k₀).filter
                (fun j => s₀ (j - 1) < t ∧ t < s₀ j)).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hst
            have hcD : ((((Finset.Icc 1 k₀).filter
                (fun j => s₀ (j - 1) < t' ∧ t' < s₀ j)).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hst'
            refine ⟨(Finset.Icc 1 k₀).filter
                  (fun j => t ≤ s₀ (j - 1) ∧ s₀ j ≤ γ.len ∧ δ ≤ s₀ j - s₀ (j - 1)) ∪
                (Finset.Icc 1 k₀).filter
                  (fun j => (0:ℝ) ≤ s₀ (j - 1) ∧ s₀ j ≤ t' ∧ δ ≤ s₀ j - s₀ (j - 1)) ∪
                (Finset.Icc 1 k₀).filter
                  (fun j => (t ≤ s₀ (j - 1) ∨ s₀ j ≤ t') ∧ s₀ j - s₀ (j - 1) < δ) ∪
                (Finset.Icc 1 k₀).filter (fun j => s₀ (j - 1) < t ∧ t < s₀ j) ∪
                (Finset.Icc 1 k₀).filter (fun j => s₀ (j - 1) < t' ∧ t' < s₀ j), ?_, ?_, ?_⟩
            · intro j hj
              simp only [Finset.mem_union, Finset.mem_filter] at hj
              tauto
            · refine le_trans (Nat.cast_le.mpr (hcard5 _ _ _ _ _)) ?_
              push_cast
              linarith
            · rintro v ⟨⟨hv0, hvl⟩, hvI⟩
              obtain ⟨j, hj1, hjk, hja, hjb⟩ := hedge v hv0 hvl
              have hvmem := hIsub ⟨⟨hv0, hvl⟩, hvI⟩
              simp only [Set.mem_iUnion, Set.mem_Icc, exists_prop]
              refine ⟨j, ?_, hja, hjb⟩
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
              have hjle : s₀ j ≤ γ.len := by rw [← hsk]; exact hm j k₀ hjk le_rfl
              have hjge : (0:ℝ) ≤ s₀ (j - 1) := by
                rw [← hs0]; exact hm 0 (j - 1) (Nat.zero_le _) (by omega)
              rcases hvmem with hv | hv
              · -- `v ∈ [t, γ.len]`
                obtain ⟨hvt, -⟩ := Set.mem_Icc.mp hv
                by_cases h1 : t ≤ s₀ (j - 1)
                · rcases lt_or_ge (s₀ j - s₀ (j - 1)) δ with hlt | hge
                  · exact Or.inl (Or.inl (Or.inr ⟨⟨hj1, hjk⟩, Or.inl h1, hlt⟩))
                  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨hj1, hjk⟩, h1, hjle, hge⟩)))
                · replace h1 := not_le.mp h1
                  refine Or.inl (Or.inr ⟨⟨hj1, hjk⟩, h1, ?_⟩)
                  rcases lt_or_ge t (s₀ j) with h | h
                  · exact h
                  · exfalso
                    have hveq : v = t := le_antisymm (hjb.trans h) hvt
                    rw [hveq, hep] at hvI; linarith
              · -- `v ∈ [0, t']`
                obtain ⟨-, hvt'⟩ := Set.mem_Icc.mp hv
                by_cases h2 : s₀ j ≤ t'
                · rcases lt_or_ge (s₀ j - s₀ (j - 1)) δ with hlt | hge
                  · exact Or.inl (Or.inl (Or.inr ⟨⟨hj1, hjk⟩, Or.inr h2, hlt⟩))
                  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨hj1, hjk⟩, hjge, h2, hge⟩)))
                · replace h2 := not_le.mp h2
                  refine Or.inr ⟨⟨hj1, hjk⟩, ?_, h2⟩
                  rcases lt_or_ge (s₀ (j - 1)) t' with h | h
                  · exact h
                  · exfalso
                    have hveq : v = t' := le_antisymm hvt' (h.trans hja)
                    rw [hveq, hep'] at hvI; linarith
        obtain ⟨J, hJsub, hJcard, hJcov⟩ := hsteps234
        -- Step 5: convert the edge count into a measure bound.
        refine (ResolutionCoverBallMeasure γ k₀ s₀ hres J hJsub x r hr
          (hstep1.trans hJcov)).trans ?_
        exact ENNReal.ofReal_le_ofReal (by nlinarith)
      · -- no parameter of `γ` is mapped into the ball, so the ball is `μ_γ`-null
        rw [heq]
        have hempty : {t ∈ Set.Icc (0:ℝ) γ.len | γ.toFun t ∈ Metric.closedBall x r} = ∅ := by
          ext t
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨ht, htx⟩
          exact hne ⟨t, ht, htx⟩
        rw [hempty]
        simp
    · -- Sub-case `r ≥ δ/2`: `LargeBallLem` applies verbatim.
      refine (LargeBallLem γ δ ε hδ hε hlsi x r hrb).trans ?_
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
