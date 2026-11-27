-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.Supplement.value_horizon_monotone
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:20.519809+00:00
-- url     : https://prove2.me/submissions/071e324a-ff3f-4fb0-83f7-97fc1534ca39

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_ControlSystem
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_Stationary

open MeasureTheory Filter Topology

open GallegoOzerADI
open GallegoOzerADI.PositiveSetup
open GallegoOzerADI.PositiveSetup.Supplement

/-- Lemma 4 (p. 1351): in the stationary positive set-up cost problem, one more remaining period
never lowers the cost: `V_{t-1}(x, o) ≥ V_t(x, o)` and `J_{t-1}(x, o) ≥ J_t(x, o)`. -/
theorem solution {L M : ℕ} [NeZero M] (G : ℝ → ℝ) (K α : ℝ)
    (μ : Measure (Fin (L + M + 2) → ℝ)) [IsProbabilityMeasure μ]
    (hG_convex : ConvexOn ℝ Set.univ G) (hG_coercive : Tendsto G (cocompact ℝ) atTop)
    (hG_nonneg : ∀ y, 0 ≤ G y) (hK : 0 < K) (hα : 0 < α)
    (hμ_nonneg : ∀ᵐ D ∂μ, ∀ k, 0 ≤ D k) :
    ∀ (n : ℕ) (x : ℝ) (o : Fin M → ℝ), 0 ≤ o →
      Vgo G K α μ n x o ≤ Vgo G K α μ (n + 1) x o ∧
        Jgo G K α μ n x o ≤ Jgo G K α μ (n + 1) x o := by
          have hsi : ∀ z, 0 ≤ setupIndicator z ∧ setupIndicator z ≤ 1 := by
            intro z; unfold setupIndicator; split_ifs <;> norm_num
          have hbdd : ∀ (V : ℝ → ℝ), (∀ y, 0 ≤ V y) → ∀ x : ℝ,
              BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => K * setupIndicator ((y : ℝ) - x) + V y) := by
            intro V hV x
            refine ⟨0, ?_⟩
            rintro _ ⟨y, rfl⟩
            have := hsi ((y : ℝ) - x); have := hV y
            dsimp only; nlinarith
          have oc_le : ∀ (V : ℝ → ℝ), (∀ y, 0 ≤ V y) → ∀ x y : ℝ, x ≤ y →
              orderCost K V x ≤ K * setupIndicator (y - x) + V y := by
            intro V hV x y hy
            exact ciInf_le (hbdd V hV x) ⟨y, hy⟩
          have oc_nonneg : ∀ (V : ℝ → ℝ), (∀ y, 0 ≤ V y) → ∀ x : ℝ, 0 ≤ orderCost K V x := by
            intro V hV x
            have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
            refine le_ciInf fun y => ?_
            have := hsi ((y : ℝ) - x); have := hV y
            nlinarith
          have oc_mono : ∀ (V W : ℝ → ℝ), (∀ y, 0 ≤ V y) → (∀ y, V y ≤ W y) → ∀ x : ℝ,
              orderCost K V x ≤ orderCost K W x := by
            intro V W hV hVW x
            have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
            exact ciInf_mono (hbdd V hV x) fun y => by linarith [hVW y]
          have oc_bound : ∀ (V : ℝ → ℝ), (∀ y, 0 ≤ V y) → ∀ x c : ℝ, x ≤ c →
              orderCost K V x ≤ K + V c := by
            intro V hV x c hc
            have h1 := oc_le V hV x c hc
            have := hsi (c - x)
            nlinarith
          have oc_formula : ∀ (V : ℝ → ℝ), (∀ y, 0 ≤ V y) → ∀ x : ℝ,
              orderCost K V x = min (V x) (K + ⨅ z : {z : ℝ // x ≤ z}, V z) := by
            intro V hV x
            have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
            have hb : BddBelow (Set.range fun z : {z : ℝ // x ≤ z} => V z) :=
              ⟨0, by rintro _ ⟨y, rfl⟩; exact hV y⟩
            apply le_antisymm
            · refine le_min ?_ ?_
              · have := oc_le V hV x x le_rfl
                simpa [setupIndicator] using this
              · have : orderCost K V x - K ≤ ⨅ z : {z : ℝ // x ≤ z}, V z := by
                  refine le_ciInf fun z => ?_
                  have := oc_le V hV x z z.2
                  have := hsi ((z : ℝ) - x)
                  nlinarith
                linarith
            · refine le_ciInf fun z => ?_
              rcases eq_or_lt_of_le z.2 with h | h
              · have : (z : ℝ) = x := h.symm
                rw [this]; simp [setupIndicator]
              · have h2 : setupIndicator ((z : ℝ) - x) = 1 := by
                  unfold setupIndicator; rw [if_pos (by linarith)]
                rw [h2]
                have := ciInf_le hb z
                have := min_le_right (V x) (K + ⨅ z : {z : ℝ // x ≤ z}, V z)
                linarith
          have m_mono : ∀ (V : ℝ → ℝ), (∀ y, 0 ≤ V y) → ∀ x x' : ℝ, x ≤ x' →
              (⨅ z : {z : ℝ // x ≤ z}, V z) ≤ ⨅ z : {z : ℝ // x' ≤ z}, V z := by
            intro V hV x x' hxx
            have : Nonempty {y : ℝ // x' ≤ y} := ⟨⟨x', le_rfl⟩⟩
            have hb : BddBelow (Set.range fun z : {z : ℝ // x ≤ z} => V z) :=
              ⟨0, by rintro _ ⟨y, rfl⟩; exact hV y⟩
            exact le_ciInf fun z => ciInf_le hb ⟨z, le_trans hxx z.2⟩
          have m_rc : ∀ (V : ℝ → ℝ), (∀ y, 0 ≤ V y) → (∀ z, ContinuousWithinAt V (Set.Ici z) z) →
              ∀ x, ContinuousWithinAt (fun x => ⨅ z : {z : ℝ // x ≤ z}, V z) (Set.Ici x) x := by
            intro V hV hrc x
            have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
            rw [ContinuousWithinAt, tendsto_order]
            constructor
            · intro a ha
              filter_upwards [self_mem_nhdsWithin] with w hw
              exact lt_of_lt_of_le ha (m_mono V hV x w hw)
            · intro a ha
              obtain ⟨z, hz⟩ := exists_lt_of_ciInf_lt ha
              have hVz := hrc z
              rw [ContinuousWithinAt, tendsto_order] at hVz
              obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hVz.2 a hz)
              have hxu : x < u := lt_of_le_of_lt z.2 hu
              filter_upwards [Ico_mem_nhdsGE hxu] with w hw
              have hb : BddBelow (Set.range fun z : {z : ℝ // w ≤ z} => V z) :=
                ⟨0, by rintro _ ⟨y, rfl⟩; exact hV y⟩
              have h1 := ciInf_le hb ⟨max w z, le_max_left _ _⟩
              have h2 : V (max w z) < a := hsub ⟨le_max_right _ _, max_lt hw.2 hu⟩
              exact lt_of_le_of_lt h1 h2
          have m_count : ∀ (V : ℝ → ℝ), (∀ y, 0 ≤ V y) → (∀ z, ContinuousWithinAt V (Set.Ici z) z) →
              ∀ x, (⨅ z : {z : ℝ // x ≤ z}, V z) = ⨅ q : ℚ, (if x ≤ (q : ℝ) then V q else V x) := by
            intro V hV hrc x
            have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
            have hb : BddBelow (Set.range fun z : {z : ℝ // x ≤ z} => V z) :=
              ⟨0, by rintro _ ⟨y, rfl⟩; exact hV y⟩
            have hb2 : BddBelow (Set.range fun q : ℚ => (if x ≤ (q : ℝ) then V q else V x)) := by
              refine ⟨0, ?_⟩
              rintro _ ⟨q, rfl⟩
              dsimp only; split_ifs <;> exact hV _
            apply le_antisymm
            · refine le_ciInf fun q => ?_
              split_ifs with h
              · exact ciInf_le hb ⟨q, h⟩
              · exact ciInf_le hb ⟨x, le_rfl⟩
            · refine le_ciInf fun z => ?_
              refine le_of_forall_pos_lt_add fun ε hε => ?_
              have hVz := hrc z
              rw [ContinuousWithinAt, tendsto_order] at hVz
              obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hVz.2 (V z + ε) (by linarith))
              obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (z : ℝ) < u from hu)
              have h1 := ciInf_le hb2 q
              have hxq : x ≤ (q : ℝ) := by linarith [z.2]
              rw [if_pos hxq] at h1
              have h2 : V q < V z + ε := hsub ⟨hq1.le, hq2⟩
              linarith
          have oc_rc : ∀ (V : ℝ → ℝ), (∀ y, 0 ≤ V y) → (∀ z, ContinuousWithinAt V (Set.Ici z) z) →
              ∀ x, ContinuousWithinAt (fun x => orderCost K V x) (Set.Ici x) x := by
            intro V hV hrc x
            have : (fun x => orderCost K V x) = fun x => min (V x) (K + ⨅ z : {z : ℝ // x ≤ z}, V z) :=
              funext fun x => oc_formula V hV x
            rw [this]
            exact (hrc x).min (continuousWithinAt_const.add (m_rc V hV hrc x))
          have hGc : Continuous G :=
            continuousOn_univ.1 (hG_convex.continuousOn isOpen_univ)
          obtain ⟨pos, hpos_id, hpos0, hpos_c⟩ : ∃ pos : (Fin M → ℝ) → (Fin M → ℝ),
              (∀ o, 0 ≤ o → pos o = o) ∧ (∀ o, 0 ≤ pos o) ∧ Continuous pos := by
            refine ⟨fun o j => max (o j) 0, ?_, ?_, ?_⟩
            · intro o ho; funext j; exact max_eq_left (ho j)
            · intro o j; exact le_max_right _ _
            · exact continuous_pi fun j => (continuous_apply j).max continuous_const
          have hobs : ∀ j, Continuous fun o : Fin M → ℝ => obsComp o j := by
            intro j; unfold obsComp; split_ifs
            · exact continuous_apply _
            · exact continuous_const
          have hobs0 : ∀ o : Fin M → ℝ, 0 ≤ o → ∀ j, 0 ≤ obsComp o j := by
            intro o ho j; unfold obsComp; split_ifs
            · exact ho _
            · exact le_rfl
          have hnX : ∀ {X : Type} [TopologicalSpace X] (f : X → ℝ) (g : X → Fin M → ℝ)
              (h : X → Fin (L + M + 2) → ℝ), Continuous f → Continuous g → Continuous h →
              Continuous fun p => nextX (f p) (g p) (h p) := by
            intro X _ f g h hf hg hh
            unfold nextX
            exact (hf.sub (continuous_finsetSum _ fun k _ => (continuous_apply _).comp hh)).sub
              ((hobs 0).comp hg)
          have hnO : ∀ {X : Type} [TopologicalSpace X] (g : X → Fin M → ℝ)
              (h : X → Fin (L + M + 2) → ℝ), Continuous g → Continuous h →
              Continuous fun p => nextO (g p) (h p) := by
            intro X _ g h hg hh
            unfold nextO
            exact continuous_pi fun j => ((hobs _).comp hg).add ((continuous_apply _).comp hh)
          have hae : ∀ o : Fin M → ℝ, 0 ≤ o → ∀ y, ∀ᵐ D ∂μ, nextX y o D ≤ y ∧ 0 ≤ nextO o D := by
            intro o ho y
            filter_upwards [hμ_nonneg] with D hD
            constructor
            · unfold nextX
              exact (sub_le_self _ (hobs0 o ho 0)).trans (sub_le_self _ (Finset.sum_nonneg fun k _ => hD _))
            · intro j
              unfold nextO
              have := hobs0 o ho (j.val + 1)
              have := hD ⟨L + 2 + j.val, by have := j.isLt; omega⟩
              simp only [Pi.zero_apply]
              linarith
          have hmono_nX : ∀ (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) (y y' : ℝ), y ≤ y' → nextX y o D ≤ nextX y' o D := by
            intro o D y y' h; unfold nextX; linarith
          have Vfacts : ∀ n : ℕ, (∀ x o, 0 ≤ Jgo G K α μ n x o) →
              (∀ c, ∃ B, ∀ x ≤ c, ∀ o : Fin M → ℝ, 0 ≤ o → Jgo G K α μ n x o ≤ B) →
              (∀ o : Fin M → ℝ, 0 ≤ o → ∀ x,
                ContinuousWithinAt (fun x => Jgo G K α μ n x o) (Set.Ici x) x) →
              Measurable (fun p : ℝ × (Fin M → ℝ) => Jgo G K α μ n p.1 (pos p.2)) →
              (∀ o : Fin M → ℝ, 0 ≤ o → ∀ y,
                Integrable (fun D : Fin (L + M + 2) → ℝ => Jgo G K α μ n (nextX y o D) (nextO o D)) μ) ∧
              (∀ y o, 0 ≤ Vgo G K α μ n y o) ∧
              (∀ c, ∃ B, ∀ o : Fin M → ℝ, 0 ≤ o → Vgo G K α μ n c o ≤ B) ∧
              (∀ o : Fin M → ℝ, 0 ≤ o → ∀ y,
                ContinuousWithinAt (fun y => Vgo G K α μ n y o) (Set.Ici y) y) ∧
              Measurable (fun p : ℝ × (Fin M → ℝ) => Vgo G K α μ n p.1 (pos p.2)) := by
            intro n hJ0 hJB hJrc hJm
            have hmeasF : ∀ o : Fin M → ℝ, 0 ≤ o → ∀ y,
                AEStronglyMeasurable (fun D : Fin (L + M + 2) → ℝ => Jgo G K α μ n (nextX y o D) (nextO o D)) μ := by
              intro o ho y
              have hg : Measurable (fun D : Fin (L + M + 2) → ℝ => Jgo G K α μ n (nextX y o D) (pos (nextO o D))) := by
                have hc : Continuous (fun D : Fin (L + M + 2) → ℝ => (nextX y o D, nextO o D)) :=
                  (hnX (fun _ => y) (fun _ => o) id continuous_const continuous_const continuous_id).prodMk
                    (hnO (fun _ => o) id continuous_const continuous_id)
                exact hJm.comp hc.measurable
              refine hg.aestronglyMeasurable.congr ?_
              filter_upwards [hae o ho y] with D hD
              rw [hpos_id _ hD.2]
            have hint : ∀ o : Fin M → ℝ, 0 ≤ o → ∀ y,
                Integrable (fun D : Fin (L + M + 2) → ℝ => Jgo G K α μ n (nextX y o D) (nextO o D)) μ := by
              intro o ho y
              obtain ⟨B, hB⟩ := hJB y
              refine Integrable.of_bound (hmeasF o ho y) B ?_
              filter_upwards [hae o ho y] with D hD
              rw [Real.norm_eq_abs, abs_of_nonneg (hJ0 _ _)]
              exact hB _ hD.1 _ hD.2
            refine ⟨hint, ?_, ?_, ?_, ?_⟩
            · intro y o
              unfold Vgo
              have := integral_nonneg (μ := μ) (f := fun D : Fin (L + M + 2) → ℝ => Jgo G K α μ n (nextX y o D) (nextO o D)) (fun D => hJ0 (nextX y o D) (nextO o D))
              have := hG_nonneg y
              positivity
            · intro c
              obtain ⟨B, hB⟩ := hJB c
              refine ⟨G c + α * B, fun o ho => ?_⟩
              unfold Vgo
              have : ∫ D, Jgo G K α μ n (nextX c o D) (nextO o D) ∂μ ≤ B := by
                have h := integral_mono_of_nonneg (Eventually.of_forall fun D => hJ0 (nextX c o D) (nextO o D))
                  (integrable_const B) (by
                    filter_upwards [hae o ho c] with D hD
                    exact hB _ hD.1 _ hD.2)
                simpa using h
              nlinarith
            · intro o ho y0
              unfold Vgo
              refine hGc.continuousWithinAt.add (continuousWithinAt_const.mul ?_)
              obtain ⟨B, hB⟩ := hJB (y0 + 1)
              refine continuousWithinAt_of_dominated (bound := fun _ => B)
                (Eventually.of_forall fun y => hmeasF o ho y) ?_ (integrable_const B) ?_
              · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : y0 < y0 + 1))] with y hy
                filter_upwards [hae o ho y] with D hD
                rw [Real.norm_eq_abs, abs_of_nonneg (hJ0 _ _)]
                exact hB _ (hD.1.trans (le_of_lt hy)) _ hD.2
              · filter_upwards [hae o ho y0] with D hD
                have h1 := hJrc (nextO o D) hD.2 (nextX y0 o D)
                have h2 : ContinuousWithinAt (fun y => nextX y o D) (Set.Ici y0) y0 :=
                  (hnX id (fun _ => o) (fun _ => D) continuous_id continuous_const
                    continuous_const).continuousWithinAt
                exact ContinuousWithinAt.comp (g := fun x => Jgo G K α μ n x (nextO o D))
                  (f := fun y => nextX y o D) h1 h2 (fun y hy => hmono_nX o D y0 y hy)
            · have heq : (fun p : ℝ × (Fin M → ℝ) => Vgo G K α μ n p.1 (pos p.2)) =
                  fun p => G p.1 + α * ∫ D, Jgo G K α μ n (nextX p.1 (pos p.2) D)
                    (pos (nextO (pos p.2) D)) ∂μ := by
                funext p
                unfold Vgo
                congr 2
                refine integral_congr_ae ?_
                filter_upwards [hae (pos p.2) (hpos0 _) p.1] with D hD
                rw [hpos_id _ hD.2]
              rw [heq]
              refine (hGc.measurable.comp measurable_fst).add (measurable_const.mul ?_)
              refine (StronglyMeasurable.integral_prod_right
                (f := fun (p : ℝ × (Fin M → ℝ)) (D : Fin (L + M + 2) → ℝ) =>
                  Jgo G K α μ n (nextX p.1 (pos p.2) D) (pos (nextO (pos p.2) D))) ?_).measurable
              refine Measurable.stronglyMeasurable ?_
              have hc : Continuous (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
                  (nextX q.1.1 (pos q.1.2) q.2, nextO (pos q.1.2) q.2)) :=
                (hnX (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) => q.1.1) (fun q => pos q.1.2)
                  (fun q => q.2) (by fun_prop) (hpos_c.comp (by fun_prop)) (by fun_prop)).prodMk
                  (hnO (fun q : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) => pos q.1.2) (fun q => q.2)
                    (hpos_c.comp (by fun_prop)) (by fun_prop))
              exact hJm.comp hc.measurable
          have key : ∀ n : ℕ, (∀ x o, 0 ≤ Jgo G K α μ n x o) ∧
              (∀ c, ∃ B, ∀ x ≤ c, ∀ o : Fin M → ℝ, 0 ≤ o → Jgo G K α μ n x o ≤ B) ∧
              (∀ o : Fin M → ℝ, 0 ≤ o → ∀ x,
                ContinuousWithinAt (fun x => Jgo G K α μ n x o) (Set.Ici x) x) ∧
              Measurable (fun p : ℝ × (Fin M → ℝ) => Jgo G K α μ n p.1 (pos p.2)) := by
            intro n
            induction n with
            | zero =>
              refine ⟨fun x o => le_rfl, fun c => ⟨0, fun x _ o _ => le_rfl⟩, fun o _ x => ?_, ?_⟩
              · show ContinuousWithinAt (fun _ => (0 : ℝ)) _ _
                exact continuousWithinAt_const
              · show Measurable (fun _ => (0 : ℝ))
                exact measurable_const
            | succ n ih =>
              obtain ⟨h0, hB, hrc, hm⟩ := ih
              obtain ⟨-, hV0, hVB, hVrc, hVm⟩ := Vfacts n h0 hB hrc hm
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro x o; rw [Jgo_succ]; exact oc_nonneg _ (fun y => hV0 y o) x
              · intro c
                obtain ⟨B, hB'⟩ := hVB c
                refine ⟨K + B, fun x hx o ho => ?_⟩
                rw [Jgo_succ]
                exact (oc_bound _ (fun y => hV0 y o) x c hx).trans (by linarith [hB' o ho])
              · intro o ho x
                simp only [Jgo_succ]
                exact oc_rc _ (fun y => hV0 y o) (hVrc o ho) x
              · have heq : (fun p : ℝ × (Fin M → ℝ) => Jgo G K α μ (n + 1) p.1 (pos p.2)) =
                    fun p => min (Vgo G K α μ n p.1 (pos p.2)) (K + ⨅ q : ℚ,
                      (if p.1 ≤ (q : ℝ) then Vgo G K α μ n q (pos p.2) else Vgo G K α μ n p.1 (pos p.2))) := by
                  funext p
                  rw [Jgo_succ, oc_formula _ (fun y => hV0 y _),
                    m_count _ (fun y => hV0 y _) (hVrc _ (hpos0 _))]
                rw [heq]
                exact hVm.min (measurable_const.add (Measurable.iInf fun q =>
                  Measurable.ite (measurableSet_le measurable_fst measurable_const)
                    (hVm.comp (measurable_const.prodMk measurable_snd)) hVm))
          have hVle : ∀ n : ℕ, (∀ x (o : Fin M → ℝ), 0 ≤ o → Jgo G K α μ n x o ≤ Jgo G K α μ (n + 1) x o) →
              ∀ y (o : Fin M → ℝ), 0 ≤ o → Vgo G K α μ n y o ≤ Vgo G K α μ (n + 1) y o := by
            intro n h y o ho
            obtain ⟨h0, -, -, -⟩ := key n
            obtain ⟨k0, kB, krc, km⟩ := key (n + 1)
            obtain ⟨hint, -⟩ := Vfacts (n + 1) k0 kB krc km
            unfold Vgo
            have : ∫ D, Jgo G K α μ n (nextX y o D) (nextO o D) ∂μ ≤
                ∫ D, Jgo G K α μ (n + 1) (nextX y o D) (nextO o D) ∂μ :=
              integral_mono_of_nonneg (Eventually.of_forall fun D => h0 _ _) (hint o ho y) (by
                filter_upwards [hae o ho y] with D hD
                exact h _ _ hD.2)
            nlinarith
          have hJmono : ∀ n : ℕ, ∀ x (o : Fin M → ℝ), 0 ≤ o →
              Jgo G K α μ n x o ≤ Jgo G K α μ (n + 1) x o := by
            intro n
            induction n with
            | zero =>
              intro x o _
              exact (key 1).1 x o
            | succ n ih =>
              intro x o ho
              obtain ⟨h0, hB, hrc, hm⟩ := key n
              obtain ⟨-, hV0, -, -, -⟩ := Vfacts n h0 hB hrc hm
              rw [Jgo_succ, Jgo_succ (n := n + 1)]
              exact oc_mono _ _ (fun y => hV0 y o) (fun y => hVle n ih y o ho) x
          intro n x o ho
          exact ⟨hVle n (hJmono n) x o ho, hJmono n x o ho⟩
