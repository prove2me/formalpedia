-- Prove2me | solution 1 for CondPortOT.SingUninf.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-15T17:37:14.943435+00:00
-- url     : https://prove2.me/submissions/b6885640-3e18-4b9a-a45c-89863e83cf66

import Definitions.Def_CondPortOT_SingUninf_Setting

open MeasureTheory

namespace CondPortOT.SingUninf

lemma condExp_le_of_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure (X × Y)) (S : Set (X × Y)) (L : Y → ℝ) (M : ℝ) (hM : ∀ y, L y ≤ M)
    (hpos : 0 < Q S) (hfin : Q S < ⊤) :
    condExp Q S L ≤ (M : EReal) := by
  unfold condExp ModelRiskOT.Duality.extIntegral
  set ν := Q.restrict S
  have hν : ν Set.univ = Q S := by simp [ν]
  set A := ∫⁻ x, ((L x.2 : EReal)).toENNReal ∂ν
  set B := ∫⁻ x, (-(L x.2 : EReal)).toENNReal ∂ν
  have hA : A ≤ ENNReal.ofReal M * Q S := by
    rw [← hν, ← lintegral_const]
    apply lintegral_mono
    intro x
    simp only [EReal.real_coe_toENNReal]
    exact ENNReal.ofReal_le_ofReal (hM _)
  have hB : ENNReal.ofReal (-M) * Q S ≤ B := by
    rw [← hν, ← lintegral_const]
    apply lintegral_mono
    intro x
    show ENNReal.ofReal (-M) ≤ (-(L x.2 : EReal)).toENNReal
    rw [← EReal.coe_neg, EReal.real_coe_toENNReal]
    exact ENNReal.ofReal_le_ofReal (by linarith [hM x.2])
  have hQne : Q S ≠ ⊤ := hfin.ne
  have hA_top : A ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQne) hA
  have hmr : 0 < (Q S).toReal := ENNReal.toReal_pos hpos.ne' hQne
  by_cases hBt : B = ⊤
  · rw [hBt]
    simp only [EReal.coe_ennreal_top, EReal.sub_top]
    rw [EReal.coe_mul_bot_of_pos (inv_pos.2 hmr)]
    exact bot_le
  · rw [← EReal.coe_ennreal_toReal hA_top, ← EReal.coe_ennreal_toReal hBt, ← EReal.coe_sub,
      ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have hA' : A.toReal ≤ max M 0 * (Q S).toReal := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hQne) hA
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
    have hB' : max (-M) 0 * (Q S).toReal ≤ B.toReal := by
      have := ENNReal.toReal_mono hBt hB
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at this
    rw [inv_mul_le_iff₀ hmr]
    have : max M 0 - max (-M) 0 = M := by
      rcases le_total M 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    nlinarith

theorem proposition_3_1 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (hA : Assumption24 DX DY x0 0 xh) (hH1 : NotIsolated DX x0)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Y → ℝ) :
    worstCasePos DX DY xh yh x0 0 ρ L = ⨆ y, (L y : EReal) := by
  classical
  apply le_antisymm
  · unfold worstCasePos
    apply iSup₂_le
    rintro Q ⟨⟨hprob, -⟩, hpos⟩
    have hfin : Q (fiber DX x0 0) < ⊤ := measure_lt_top _ _
    -- case split on the supremum
    have hne : Nonempty Y := ⟨yh ⟨0, hN⟩⟩
    induction h : (⨆ y, (L y : EReal)) using EReal.rec with
    | bot =>
      exfalso
      have := le_iSup (fun y => (L y : EReal)) (yh ⟨0, hN⟩)
      rw [h] at this
      exact absurd this (by simp)
    | top => exact le_top
    | coe m =>
      apply condExp_le_of_bound Q _ L m _ hpos hfin
      intro y
      have := le_iSup (fun y => (L y : EReal)) y
      rw [h] at this
      exact_mod_cast this
  · apply iSup_le
    intro y
    set i0 : Fin N := ⟨0, hN⟩
    have hDX0 : ∀ x, DX x x = 0 := by
      intro x
      have := (hA.cost_eq_zero_iff x x (yh i0) (yh i0)).2 rfl
      linarith [hA.DX_nonneg x x, hA.DY_nonneg (yh i0) (yh i0)]
    have hDY0 : ∀ y, DY y y = 0 := by
      intro y
      have := (hA.cost_eq_zero_iff x0 x0 y y).2 rfl
      linarith [hA.DX_nonneg x0 x0, hA.DY_nonneg y y]
    have hpos_of_ne : ∀ x, x ≠ x0 → 0 < DX x x0 := by
      intro x hx
      rcases (hA.DX_nonneg x x0).lt_or_eq with h | h
      · exact h
      · exfalso
        have := (hA.cost_eq_zero_iff x x0 y y).1 (by rw [← h, hDY0]; ring)
        exact hx (Prod.mk.inj this).1
    obtain ⟨x', hx'ne, hx'r⟩ := hH1 (ρ / 2) (by linarith)
    set xs : Fin N → X := fun i => if xh i = x0 then x' else xh i with hxs_def
    have hxs : ∀ i, xs i ≠ x0 := by
      intro i
      simp only [xs]
      split_ifs with h
      · exact hx'ne
      · exact h
    have hxscost : ∀ i, DX (xs i) (xh i) ≤ ρ / 2 := by
      intro i
      simp only [xs]
      split_ifs with h
      · rw [h]; exact hx'r
      · rw [hDX0]; linarith
    set w : X × Y := (x0, y)
    set Ssum : ENNReal := ∑ i, ENNReal.ofReal (DX x0 (xh i) + DY y (yh i))
    have hSfin : Ssum ≠ ⊤ := by
      simp [Ssum, ENNReal.sum_ne_top]
    set t : ENNReal := min 1 (ENNReal.ofReal (ρ / 2) / (Ssum + 1))
    have ht1 : t ≤ 1 := min_le_left _ _
    have hS1 : Ssum + 1 ≠ ⊤ := by simp [hSfin]
    have hS1' : Ssum + 1 ≠ 0 := by simp
    have ht0 : t ≠ 0 := by
      simp only [t, ne_eq]
      intro h
      rcases min_eq_iff.1 h with h | h
      · exact one_ne_zero h.1
      · have := h.1
        rw [ENNReal.div_eq_zero_iff] at this
        rcases this with h' | h'
        · simp at h'; linarith
        · exact hS1 h'
    have htS : t * Ssum ≤ ENNReal.ofReal (ρ / 2) := by
      calc t * Ssum ≤ ENNReal.ofReal (ρ / 2) / (Ssum + 1) * (Ssum + 1) := by
            gcongr
            · exact min_le_right _ _
            · exact le_self_add
        _ = ENNReal.ofReal (ρ / 2) := ENNReal.div_mul_cancel hS1' hS1
    have hcont : Continuous (fun x => DX x x0) :=
      hA.DX_cont.comp (continuous_id.prodMk continuous_const)
    have hFm : MeasurableSet (fiber (Y := Y) DX x0 0) :=
      ((isClosed_le hcont continuous_const).measurableSet).prod MeasurableSet.univ
    have hw : w ∈ fiber (Y := Y) DX x0 0 := by
      simp [w, fiber, nbhd, hDX0]
    have hzs : ∀ i, (xs i, yh i) ∉ fiber (Y := Y) DX x0 0 := by
      intro i
      simp only [fiber, nbhd, Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true, not_le]
      exact hpos_of_ne _ (hxs i)
    set π : Measure ((X × Y) × (X × Y)) := (N : ENNReal)⁻¹ • ∑ i,
      ((1 - t) • Measure.dirac ((xs i, yh i), (xh i, yh i)) + t • Measure.dirac (w, (xh i, yh i)))
    set Q : Measure (X × Y) := (N : ENNReal)⁻¹ • ∑ i,
      ((1 - t) • Measure.dirac (xs i, yh i) + t • Measure.dirac w)
    have hNne : (N : ENNReal) ≠ 0 := by simp; omega
    have hNtop : (N : ENNReal) ≠ ⊤ := by simp
    have h1t : 1 - t + t = 1 := tsub_add_cancel_of_le ht1
    have hfst : π.map Prod.fst = Q := by
      simp only [π, Q]
      rw [Measure.map_smul, Measure.map_finset_sum' measurable_fst.aemeasurable]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
        Measure.map_dirac' measurable_fst, Measure.map_dirac' measurable_fst]
    have hsnd : π.map Prod.snd = empirical xh yh := by
      simp only [π, empirical]
      rw [Measure.map_smul, Measure.map_finset_sum' measurable_snd.aemeasurable]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
        Measure.map_dirac' measurable_snd, Measure.map_dirac' measurable_snd, ← add_smul, h1t,
        one_smul]
    have hπprob : IsProbabilityMeasure π := by
      constructor
      simp only [π, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
        Measure.add_apply, measure_univ, smul_eq_mul, mul_one, h1t, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact ENNReal.inv_mul_cancel hNne hNtop
    have hQprob : IsProbabilityMeasure Q := by
      rw [← hfst]; exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    have hcost : RWPI.SqrtLasso.transportCost (groundCost DX DY) Q (empirical xh yh)
        ≤ ENNReal.ofReal ρ := by
      refine (iInf₂_le π ⟨hπprob, hfst, hsnd⟩).trans ?_
      simp only [π, lintegral_smul_measure, lintegral_finset_sum_measure, lintegral_add_measure,
        lintegral_dirac, groundCost, smul_eq_mul]
      have hb : ∀ i, (1 - t) * ENNReal.ofReal (DX (xs i) (xh i) + DY (yh i) (yh i))
          ≤ ENNReal.ofReal (ρ / 2) := by
        intro i
        rw [hDY0, add_zero]
        calc (1 - t) * ENNReal.ofReal (DX (xs i) (xh i)) ≤ 1 * ENNReal.ofReal (ρ / 2) := by
              gcongr
              · exact tsub_le_self
              · exact hxscost i
          _ = _ := one_mul _
      calc (N : ENNReal)⁻¹ * ∑ i, ((1 - t) * ENNReal.ofReal (DX (xs i) (xh i) + DY (yh i) (yh i))
              + t * ENNReal.ofReal (DX w.1 (xh i) + DY w.2 (yh i)))
          ≤ (N : ENNReal)⁻¹ * ∑ i, (ENNReal.ofReal (ρ / 2)
              + t * ENNReal.ofReal (DX x0 (xh i) + DY y (yh i))) := by
            gcongr with i
            exact hb i
        _ = ENNReal.ofReal (ρ / 2) + (N : ENNReal)⁻¹ * (t * Ssum) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul, mul_add, ← mul_assoc,
              ENNReal.inv_mul_cancel hNne hNtop, one_mul]
        _ ≤ ENNReal.ofReal (ρ / 2) + 1 * ENNReal.ofReal (ρ / 2) := by
            gcongr
            exact ENNReal.inv_le_one.2 (by exact_mod_cast hN)
        _ = ENNReal.ofReal ρ := by
            rw [one_mul, ← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
    have hres : Q.restrict (fiber DX x0 0) = t • Measure.dirac w := by
      ext s hs
      rw [Measure.restrict_apply hs]
      simp only [Q, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
        Measure.add_apply, smul_eq_mul, Measure.dirac_apply' _ (hs.inter hFm),
        Measure.dirac_apply' _ hs]
      have h0 : ∀ i, Set.indicator (s ∩ fiber DX x0 0) (1 : X × Y → ENNReal) (xs i, yh i) = 0 :=
        fun i => Set.indicator_of_notMem (fun h => hzs i h.2) _
      have h1 : Set.indicator (s ∩ fiber DX x0 0) (1 : X × Y → ENNReal) w
          = Set.indicator s 1 w := by
        by_cases hws : w ∈ s
        · rw [Set.indicator_of_mem (show w ∈ s ∩ fiber DX x0 0 from ⟨hws, hw⟩), Set.indicator_of_mem hws]
        · rw [Set.indicator_of_notMem (fun h => hws h.1), Set.indicator_of_notMem hws]
      simp only [h0, h1, mul_zero, zero_add, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hNne hNtop, one_mul]
    have hQS : Q (fiber DX x0 0) = t := by
      rw [← Measure.restrict_apply_univ, hres]; simp
    have htt : t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ht1
    have htr : 0 < t.toReal := ENNReal.toReal_pos ht0 htt
    have hval : condExp Q (fiber DX x0 0) L = (L y : EReal) := by
      unfold condExp ModelRiskOT.Duality.extIntegral
      rw [hres, hQS, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
        lintegral_dirac]
      simp only [w, smul_eq_mul]
      rw [← EReal.coe_neg, EReal.real_coe_toENNReal, EReal.real_coe_toENNReal,
        ← EReal.coe_ennreal_toReal (ENNReal.mul_ne_top htt ENNReal.ofReal_ne_top),
        ← EReal.coe_ennreal_toReal (ENNReal.mul_ne_top htt ENNReal.ofReal_ne_top),
        ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_eq_coe_iff, ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', ← mul_sub]
      field_simp
      rcases le_total (L y) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    unfold worstCasePos
    refine le_iSup₂_of_le Q ⟨⟨hQprob, hcost⟩, ?_⟩ (le_of_eq hval.symm)
    rw [hQS]; exact pos_iff_ne_zero.2 ht0

end CondPortOT.SingUninf


-- Platform entry point: restates the target verbatim.
namespace CondPortOT.SingUninf

theorem _root_.solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (hA : Assumption24 DX DY x0 0 xh) (hH1 : NotIsolated DX x0)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Y → ℝ) :
    worstCasePos DX DY xh yh x0 0 ρ L = ⨆ y, (L y : EReal) := by
  apply @CondPortOT.SingUninf.proposition_3_1 <;> assumption

end CondPortOT.SingUninf
