-- Prove2me | solution 1 for BilevelSOC.SecondOrder.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:39:13.0589+00:00
-- url     : https://prove2.me/submissions/80a6d7d3-1b30-43f1-825e-0f2bcdcbef8c

import Theorems.Thm_BilevelSOC_SecondOrder_c2_secondOrder
import Theorems.Thm_BilevelSOC_SecondOrder_lemma_2_2
import Theorems.Thm_BilevelSOC_SecondOrder_lemma_2_4
import Theorems.Thm_BilevelSOC_SecondOrder_proposition_2_10
import Theorems.Thm_BilevelSOC_SecondOrder_remark_5_1
open scoped Topology
open BilevelSOC.SecondOrder Filter Set

theorem bs_sdd_sub_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (x : V) (θ' : V → ℝ) (θ'' : V → V → ℝ) (c : ℝ)
    (h : SecondOrderDirDiff θ x θ' θ'') :
    SecondOrderDirDiff (fun z => θ z - c) x θ' θ'' := by
  intro d
  refine ⟨?_, fun w => ?_⟩
  · have := (h d).1
    unfold HasDirDerivAt at this ⊢
    simpa only [sub_sub_sub_cancel_right] using this
  · have := (h d).2 w
    simpa only [sub_sub_sub_cancel_right] using this

theorem bs_epi_sub_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : V → ℝ) (x : V) (θ' : V → ℝ) (θ'' : V → V → ℝ) (c : ℝ)
    (h : SecondOrderEpiRegular θ x θ' θ'') :
    SecondOrderEpiRegular (fun z => θ z - c) x θ' θ'' := by
  intro d w hw ε hε
  filter_upwards [h d w hw ε hε] with t ht
  linarith

theorem bs_sdd_fst {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : E → ℝ) (x : E) (y : F) (φ' : E → ℝ) (φ'' : E → E → ℝ)
    (h : SecondOrderDirDiff φ x φ' φ'') :
    SecondOrderDirDiff (fun z : E × F => φ z.1) (x, y) (fun d => φ' d.1)
      (fun d w => φ'' d.1 w.1) := by
  intro d
  refine ⟨?_, fun w => ?_⟩
  · have := (h d.1).1
    unfold HasDirDerivAt at this ⊢
    simpa using this
  · have := (h d.1).2 w.1
    simpa using this

theorem bs_sdd_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ₁ θ₂ : V → ℝ) (x : V) (a₁ a₂ : V → ℝ) (b₁ b₂ : V → V → ℝ)
    (h₁ : SecondOrderDirDiff θ₁ x a₁ b₁) (h₂ : SecondOrderDirDiff θ₂ x a₂ b₂) :
    SecondOrderDirDiff (fun z => θ₁ z - θ₂ z) x (fun d => a₁ d - a₂ d)
      (fun d w => b₁ d w - b₂ d w) := by
  intro d
  refine ⟨?_, fun w => ?_⟩
  · have := ((h₁ d).1).sub ((h₂ d).1)
    unfold HasDirDerivAt at this ⊢
    refine this.congr (fun t => ?_)
    ring
  · have := ((h₁ d).2 w).sub ((h₂ d).2 w)
    refine this.congr (fun t => ?_)
    ring

theorem bs_epi_sub_fst {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E × F → ℝ) (φ : E → ℝ) (x : E) (y : F) (f' : E × F → ℝ)
    (f'' : E × F → E × F → ℝ) (φ' : E → ℝ) (φ'' : E → E → ℝ)
    (hf : SecondOrderEpiRegular f (x, y) f' f'')
    (hφ : SecondOrderEpiRegular (fun u => -φ u) x (fun d => -φ' d) (fun d w => -φ'' d w)) :
    SecondOrderEpiRegular (fun z => f z - φ z.1) (x, y) (fun d => f' d - φ' d.1)
      (fun d w => f'' d w - φ'' d.1 w.1) := by
  intro d w hw ε hε
  have hw1 : Tendsto (fun t : ℝ => t • (w t).1) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((continuous_fst (X := E) (Y := F)).tendsto 0).comp hw
    simpa [Function.comp_def] using this
  filter_upwards [hf d w hw (ε / 2) (by positivity),
    hφ d.1 (fun t => (w t).1) hw1 (ε / 2) (by positivity)] with t h1 h2
  simp only [Prod.fst_add, Prod.smul_fst] at h2 ⊢
  linarith

/-- The finitely many pieces of the max-function `ψ` of the paper. -/
def bTh {n m p q : ℕ} (D : Data n m p q) (φr : E n → ℝ) (z0 : E n × Y m) :
    Option (Option (Fin p ⊕ Fin q)) → E n × Y m → ℝ
  | none => fun z => D.F z - D.F z0
  | some none => fun z => D.f z - φr z.1
  | some (some (Sum.inl i)) => D.G i
  | some (some (Sum.inr j)) => D.g j

noncomputable def bTh1 {n m p q : ℕ} (D : Data n m p q) (φ' : E n → ℝ) (z0 : E n × Y m) :
    Option (Option (Fin p ⊕ Fin q)) → E n × Y m → ℝ
  | none => fun d => fderiv ℝ D.F z0 d
  | some none => fun d => fderiv ℝ D.f z0 d - φ' d.1
  | some (some (Sum.inl i)) => fun d => fderiv ℝ (D.G i) z0 d
  | some (some (Sum.inr j)) => fun d => fderiv ℝ (D.g j) z0 d

noncomputable def bTh2 {n m p q : ℕ} (D : Data n m p q) (φ'' : E n → E n → ℝ) (z0 : E n × Y m) :
    Option (Option (Fin p ⊕ Fin q)) → E n × Y m → E n × Y m → ℝ
  | none => fun d w => fderiv ℝ D.F z0 w + fderiv ℝ (fderiv ℝ D.F) z0 d d
  | some none => fun d w =>
      fderiv ℝ D.f z0 w + fderiv ℝ (fderiv ℝ D.f) z0 d d - φ'' d.1 w.1
  | some (some (Sum.inl i)) => fun d w =>
      fderiv ℝ (D.G i) z0 w + fderiv ℝ (fderiv ℝ (D.G i)) z0 d d
  | some (some (Sum.inr j)) => fun d w =>
      fderiv ℝ (D.g j) z0 w + fderiv ℝ (fderiv ℝ (D.g j)) z0 d d

theorem solution {n m p q : ℕ} (D : Data n m p q) (hD : Standing D)
    (xbar : E n) (ybar : Y m) (hfeas : (xbar, ybar) ∈ feasSet D)
    (hACQ : ACQ52 D (xbar, ybar))
    (φr : E n → ℝ) (U : Set (E n)) (hU : U ∈ 𝓝 xbar)
    (hφU : ∀ x ∈ U, valueFn D x = (φr x : EReal))
    (L : NNReal) (hLip : LipschitzOnWith L φr U)
    (φ' : E n → ℝ) (φ'' : E n → E n → ℝ)
    (hφ2 : SecondOrderDirDiff φr xbar φ' φ'')
    (hepi : SecondOrderEpiRegular (fun x => -φr x) xbar
      (fun d => -φ' d) (fun d w => -φ'' d w))
    (h54 : ∀ d ∈ linConeVF D (xbar, ybar) φ',
      0 ≤ fderiv ℝ D.F (xbar, ybar) d)
    (h55 : ∀ d ∈ critConeVF D (xbar, ybar) φ',
      d ≠ 0 → Prog55Pos D (xbar, ybar) φ'' d) :
    (∃ W : Set (E n × Y m), W ∈ 𝓝 (xbar, ybar) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ z ∈ feasSet D ∩ W,
        D.F (xbar, ybar) +
          C * (‖z.1 - xbar‖ ^ 2 + ‖z.2 - ybar‖ ^ 2) ≤ D.F z) ∧
    (∃ W : Set (E n × Y m), W ∈ 𝓝 (xbar, ybar) ∧
      ∀ z ∈ feasSet D ∩ W, z ≠ (xbar, ybar) → D.F (xbar, ybar) < D.F z) := by
  classical
  -- the value function coincides with `f` along bilevel-feasible points
  have hval : ∀ z : E n × Y m, z.1 ∈ U → z.2 ∈ solMap D z.1 → φr z.1 = D.f z := by
    intro z hzU hz
    have h1 := hφU z.1 hzU
    have h2 : valueFn D z.1 = (D.f z : EReal) := by
      unfold valueFn
      apply le_antisymm
      · exact iInf₂_le z.2 hz.1
      · exact le_iInf₂ fun y hy => EReal.coe_le_coe_iff.2 (hz.2 y hy)
    rw [h1] at h2
    exact_mod_cast h2
  have hxU : xbar ∈ U := mem_of_mem_nhds hU
  have hf0 : D.f (xbar, ybar) - φr xbar = 0 := by
    rw [hval (xbar, ybar) hxU hfeas.2]; ring
  set z0 : E n × Y m := (xbar, ybar) with hz0
  set θ := bTh D φr z0 with hθ
  set θ' := bTh1 D φ' z0 with hθ'
  set θ'' := bTh2 D φ'' z0 with hθ''
  -- second-order directional differentiability of the pieces
  have hDiff : ∀ i, SecondOrderDirDiff (θ i) z0 (θ' i) (θ'' i) := by
    rintro (_ | _ | i | j)
    · exact bs_sdd_sub_const _ _ _ _ _ (c2_secondOrder D.F hD.1 z0).1
    · exact bs_sdd_sub _ _ _ _ _ _ _ (c2_secondOrder D.f hD.2.1 z0).1
        (bs_sdd_fst φr xbar ybar φ' φ'' hφ2)
    · exact (c2_secondOrder (D.G i) (hD.2.2.1 i) z0).1
    · exact (c2_secondOrder (D.g j) (hD.2.2.2 j) z0).1
  have hEpi : ∀ i, SecondOrderEpiRegular (θ i) z0 (θ' i) (θ'' i) := by
    rintro (_ | _ | i | j)
    · exact bs_epi_sub_const _ _ _ _ _ (c2_secondOrder D.F hD.1 z0).2
    · exact bs_epi_sub_fst D.f φr xbar ybar _ _ φ' φ'' (c2_secondOrder D.f hD.2.1 z0).2 hepi
    · exact (c2_secondOrder (D.G i) (hD.2.2.1 i) z0).2
    · exact (c2_secondOrder (D.g j) (hD.2.2.2 j) z0).2
  -- local Lipschitz continuity of the pieces, with a common constant and neighbourhood
  have hloc : ∀ i, ∃ K : NNReal, ∃ T ∈ 𝓝 z0, LipschitzOnWith K (θ i) T := by
    rintro (_ | _ | i | j)
    · exact ((hD.1.sub contDiff_const).contDiffAt.of_le one_le_two).exists_lipschitzOnWith
    · obtain ⟨K, T, hT, hK⟩ := (hD.2.1.contDiffAt (x := z0).of_le one_le_two).exists_lipschitzOnWith
      refine ⟨K + L, T ∩ Prod.fst ⁻¹' U,
        inter_mem hT (continuous_fst.continuousAt.preimage_mem_nhds hU),
        LipschitzOnWith.of_le_add_mul _ fun a ha b hb => ?_⟩
      have h1 := hK.le_add_mul ha.1 hb.1
      have h2 := hLip.le_add_mul hb.2 ha.2
      have h3 : dist b.1 a.1 ≤ dist a b := by
        rw [dist_comm, Prod.dist_eq]; exact le_max_left _ _
      have h4 : (L : ℝ) * dist b.1 a.1 ≤ L * dist a b :=
        mul_le_mul_of_nonneg_left h3 L.coe_nonneg
      show D.f a - φr a.1 ≤ D.f b - φr b.1 + ((K + L : NNReal) : ℝ) * dist a b
      push_cast
      linarith
    · exact ((hD.2.2.1 i).contDiffAt.of_le one_le_two).exists_lipschitzOnWith
    · exact ((hD.2.2.2 j).contDiffAt.of_le one_le_two).exists_lipschitzOnWith
  choose K T hT hK using hloc
  set U' : Set (E n × Y m) := ⋂ i, T i with hU'def
  have hU' : U' ∈ 𝓝 z0 := iInter_mem.2 hT
  set L' : NNReal := ∑ i, K i with hL'
  have hLip' : ∀ i, LipschitzOnWith L' (θ i) U' := fun i =>
    ((hK i).mono (iInter_subset _ i)).weaken
      (Finset.single_le_sum (f := K) (fun j _ => by positivity) (Finset.mem_univ i))
  -- Lemmas 2.2 and 2.4 for ψ = max of the pieces
  obtain ⟨Θ', Θ'', hΘ, hG', hG''⟩ := lemma_2_2 θ θ' θ'' z0 U' hU' L' hLip' hDiff
  have hΘepi := lemma_2_4 θ θ' θ'' z0 U' hU' L' hLip' hDiff hEpi Θ' Θ'' hΘ
  have hmax0 : maxFn θ z0 = 0 := by
    apply le_antisymm
    · refine Finset.sup'_le _ _ ?_
      rintro (_ | _ | i | j) _
      · show D.F z0 - D.F z0 ≤ 0
        simp
      · show D.f z0 - φr z0.1 ≤ 0
        rw [hf0]
      · exact hfeas.1 i
      · exact hfeas.2.1 j
    · have : θ none z0 = 0 := by show D.F z0 - D.F z0 = 0; simp
      rw [← this]
      exact Finset.le_sup' (fun i => θ i z0) (Finset.mem_univ none)
  have hbd : ∀ d i, θ i z0 = 0 → θ' i d ≤ Θ' d := fun d i hi =>
    (hG' d).2 ⟨i, by rw [hmax0]; exact hi, rfl⟩
  have hlin : ∀ d, (∀ i, θ i z0 = 0 → θ' i d ≤ 0) → d ∈ linConeVF D z0 φ' := by
    intro d h
    exact ⟨fun i hi => h (some (some (Sum.inl i))) hi, h (some none) hf0,
      fun j hj => h (some (some (Sum.inr j))) hj⟩
  have hF0 : θ none z0 = 0 := by show D.F z0 - D.F z0 = 0; simp
  have hFirst : ∀ d, 0 ≤ Θ' d := by
    intro d
    by_contra hneg
    push_neg at hneg
    have hl := hlin d (fun i hi => (hbd d i hi).trans hneg.le)
    have h1 := h54 d hl
    have h2 := hbd d none hF0
    have : θ' none d = fderiv ℝ D.F z0 d := rfl
    linarith
  have hSecond : ∀ d, Θ' d = 0 → d ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ w, c ≤ Θ'' d w := by
    intro d hd0 hdne
    have hl := hlin d (fun i hi => (hbd d i hi).trans hd0.le)
    have hF : fderiv ℝ D.F z0 d = 0 :=
      le_antisymm ((hbd d none hF0).trans hd0.le) (h54 d hl)
    have hcrit : d ∈ critConeVF D z0 φ' := ⟨hl, le_of_eq hF⟩
    obtain ⟨c, hc, hcw⟩ := h55 d hcrit hdne
    refine ⟨c, hc, fun w => ?_⟩
    have mem : ∀ i, θ i z0 = 0 → θ' i d = 0 → θ'' i d w ≤ Θ'' d w := fun i hi hi' =>
      (hG'' d w).2 ⟨i, by rw [hmax0]; exact hi, by rw [hi', hd0], rfl⟩
    rcases hcw w with h | ⟨i, hi, h⟩ | h | ⟨j, hj, h⟩
    · exact h.trans (mem none hF0 hF)
    · exact h.trans (mem (some (some (Sum.inl i))) hi.1 hi.2)
    · have hr := (remark_5_1 D hD xbar ybar hfeas φr U hU hφU L hLip φ'
        (fun d => (hφ2 d).1) hACQ).1 d hl.2.2
      have hf' : θ' (some none) d = 0 :=
        le_antisymm ((hbd d (some none) hf0).trans hd0.le) hr
      exact h.trans (mem (some none) hf0 hf')
    · exact h.trans (mem (some (some (Sum.inr j))) hj.1 hj.2)
  have hLipMax : LipschitzOnWith L' (maxFn θ) U' := by
    refine LipschitzOnWith.of_le_add_mul _ fun a ha b hb => ?_
    unfold maxFn
    refine Finset.sup'_le _ _ fun i _ => ?_
    refine ((hLip' i).le_add_mul ha hb).trans ?_
    gcongr
    exact Finset.le_sup' (fun i => θ i b) (Finset.mem_univ i)
  -- Proposition 2.10: quadratic growth of ψ
  obtain ⟨-, W, hW, C, hC, hWC⟩ :=
    proposition_2_10 (maxFn θ) z0 Θ' Θ'' hΘ hΘepi U' hU' L' hLipMax hFirst hSecond
  have hW' : W ∩ Prod.fst ⁻¹' U ∈ 𝓝 z0 :=
    inter_mem hW (continuous_fst.continuousAt.preimage_mem_nhds hU)
  have key : ∀ z ∈ feasSet D ∩ (W ∩ Prod.fst ⁻¹' U),
      C * ‖z - z0‖ ^ 2 ≤ max (D.F z - D.F z0) 0 := by
    rintro z ⟨hzf, hzW, hzU⟩
    have h1 := hWC z ⟨mem_univ _, hzW⟩
    rw [hmax0, Real.rpow_two, zero_add] at h1
    refine h1.trans ?_
    unfold maxFn
    refine Finset.sup'_le _ _ ?_
    rintro (_ | _ | i | j) _
    · exact le_max_left _ _
    · show D.f z - φr z.1 ≤ _
      rw [hval z hzU hzf.2, sub_self]
      exact le_max_right _ _
    · exact (hzf.1 i).trans (le_max_right _ _)
    · exact (hzf.2.1 j).trans (le_max_right _ _)
  have hnorm : ∀ z : E n × Y m, ‖z - z0‖ ^ 2 ≤ ‖z.1 - xbar‖ ^ 2 + ‖z.2 - ybar‖ ^ 2 ∧
      ‖z.1 - xbar‖ ^ 2 + ‖z.2 - ybar‖ ^ 2 ≤ 2 * ‖z - z0‖ ^ 2 := by
    intro z
    have e : ‖z - z0‖ = max ‖z.1 - xbar‖ ‖z.2 - ybar‖ := by
      rw [Prod.norm_def]; rfl
    have n1 := norm_nonneg (z.1 - xbar)
    have n2 := norm_nonneg (z.2 - ybar)
    rcases le_total ‖z.1 - xbar‖ ‖z.2 - ybar‖ with h | h
    · rw [e, max_eq_right h]
      constructor <;> nlinarith
    · rw [e, max_eq_left h]
      constructor <;> nlinarith
  have hFz : ∀ z ∈ feasSet D ∩ (W ∩ Prod.fst ⁻¹' U), C * ‖z - z0‖ ^ 2 ≤ D.F z - D.F z0 := by
    intro z hz
    have hk := key z hz
    rcases le_total 0 (D.F z - D.F z0) with h | h
    · rwa [max_eq_left h] at hk
    · rw [max_eq_right h] at hk
      have hsq : ‖z - z0‖ ^ 2 ≤ 0 := by
        by_contra hh
        push_neg at hh
        have := mul_pos hC hh
        linarith
      have hsq0 : ‖z - z0‖ ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
      have hn : ‖z - z0‖ = 0 := pow_eq_zero_iff two_ne_zero |>.1 hsq0
      rw [norm_eq_zero, sub_eq_zero] at hn
      rw [hn, sub_self]
      simp
  refine ⟨⟨W ∩ Prod.fst ⁻¹' U, hW', C / 2, by positivity, fun z hz => ?_⟩,
    ⟨W ∩ Prod.fst ⁻¹' U, hW', fun z hz hne => ?_⟩⟩
  · have h1 := hFz z hz
    have h2 := (hnorm z).2
    nlinarith
  · have h1 := hFz z hz
    have hpos : 0 < ‖z - z0‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have := mul_pos hC (pow_pos hpos 2)
    linarith
