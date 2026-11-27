-- Prove2me | solution 1 for EarlyInspect.Align.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:07:37.330543+00:00
-- url     : https://prove2.me/submissions/27dd91a8-07ec-4b82-b3e6-b6fdd1b7d8ba

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model
import Definitions.Def_EarlyInspect_Align_Supplement_SchemeM

open EarlyInspect
open EarlyInspect.Align
open EarlyInspect.Align.Supplement

open MeasureTheory

theorem solution (P : Measure ℝ) [IsProbabilityMeasure P] (f : ℝ → ℝ) (J : Set ℝ)
    (hJopen : IsOpen J) (hJconn : J.OrdConnected)
    (hfcont : ContinuousOn f J) (hfpos : ∀ x ∈ J, 0 < f x) (hfzero : ∀ x ∉ J, f x = 0)
    (hP : P = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hneg : Integrable (fun x => max (-x) 0) P)
    (hinj : Set.InjOn (revHazardRecip P f) J)
    (hincr : BddAbove J → ¬ BddBelow J → StrictMonoOn (revHazardRecip P f) J)
    (chat M s₀ I : ℝ) (hchat : 0 < chat) (hs₀ : s₀ ∈ J)
    (hroot : revHazardRecip P f s₀ = M / chat) :
    EarlyInspect.Align.argminFrom (agentCostM P chat M) I = {max I s₀} := by
      classical
      have hf0 : ∀ x, 0 ≤ f x := by
        intro x; by_cases hx : x ∈ J
        · exact (hfpos x hx).le
        · exact (hfzero x hx).ge
      have hfeq : f = J.piecewise f (fun _ => 0) := by
        funext x; by_cases hx : x ∈ J
        · simp [Set.piecewise, hx]
        · simp [Set.piecewise, hx, hfzero x hx]
      have hfmeas : Measurable f := by
        rw [hfeq]
        exact ContinuousOn.measurable_piecewise hfcont continuousOn_const hJopen.measurableSet
      have hPapply : ∀ s, MeasurableSet s → P s = ∫⁻ x in s, ENNReal.ofReal (f x) := by
        intro s hs; rw [hP, withDensity_apply _ hs]
      have hfint : Integrable f volume := by
        have h1 : ∫⁻ x, ENNReal.ofReal (f x) = 1 := by
          have := hPapply Set.univ MeasurableSet.univ
          rw [Measure.restrict_univ] at this
          rw [← this, measure_univ]
        have := integrable_toReal_of_lintegral_ne_top (μ := volume)
          (f := fun x => ENNReal.ofReal (f x)) hfmeas.ennreal_ofReal.aemeasurable
          (by rw [h1]; exact ENNReal.one_ne_top)
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp [ENNReal.toReal_ofReal (hf0 x)]
      have hac : P ≪ volume := hP ▸ withDensity_absolutelyContinuous _ _
      have : NullSingletonClass P := ⟨fun x => hac (measure_singleton x)⟩
      have hFmono : Monotone (fun x => ProbabilityTheory.cdf P x) := (ProbabilityTheory.cdf P).mono
      have hPIoc : ∀ x y, x ≤ y → ProbabilityTheory.cdf P y - ProbabilityTheory.cdf P x = ∫ t in Set.Ioc x y, f t := by
        intro x y hxy
        have h1 := (ProbabilityTheory.cdf P).measure_Ioc x y
        rw [ProbabilityTheory.measure_cdf, hPapply _ measurableSet_Ioc,
          ← ofReal_integral_eq_lintegral_ofReal hfint.integrableOn
            (Filter.Eventually.of_forall fun t => hf0 t)] at h1
        exact ((ENNReal.ofReal_eq_ofReal_iff (setIntegral_nonneg measurableSet_Ioc (fun t _ => hf0 t))
          (sub_nonneg.mpr (hFmono hxy))).mp h1).symm
      have hFint : ∀ x y, ProbabilityTheory.cdf P y - ProbabilityTheory.cdf P x = ∫ t in x..y, f t := by
        intro x y
        rcases le_total x y with h | h
        · rw [intervalIntegral.integral_of_le h]; exact hPIoc x y h
        · rw [intervalIntegral.integral_of_ge h, ← hPIoc y x h]; ring
      have hFfun : (fun x => ProbabilityTheory.cdf P x) = fun x => ProbabilityTheory.cdf P 0 + ∫ t in (0:ℝ)..x, f t := by
        funext x; linarith [hFint 0 x]
      have hFcont : Continuous (fun x => ProbabilityTheory.cdf P x) := by
        rw [hFfun]
        exact continuous_const.add
          (intervalIntegral.continuous_primitive (fun a b => hfint.intervalIntegrable) 0)
      have hFderiv : ∀ t ∈ J, HasDerivAt (fun x => ProbabilityTheory.cdf P x) (f t) t := by
        intro t ht
        have h := intervalIntegral.integral_hasDerivAt_right (hfint.intervalIntegrable (a := 0) (b := t))
          (hfmeas.stronglyMeasurable.stronglyMeasurableAtFilter)
          (hfcont.continuousAt (hJopen.mem_nhds ht))
        rw [hFfun]
        exact h.const_add (ProbabilityTheory.cdf P 0)
      have hIci : ∀ S, P.real (Set.Ici S) = 1 - ProbabilityTheory.cdf P S := by
        intro S
        rw [← measureReal_congr (Ioi_ae_eq_Ici (μ := P)), ← Set.compl_Iic,
          probReal_compl_eq_one_sub measurableSet_Iic, ProbabilityTheory.cdf_eq_real]
      -- F vanishes left of J
      have hF0 : ∀ t, (∀ u ∈ J, t < u) → ProbabilityTheory.cdf P t = 0 := by
        intro t ht
        have h1 : P (Set.Iic t) = 0 := by
          rw [hPapply _ measurableSet_Iic]
          rw [setLIntegral_congr_fun measurableSet_Iic (g := fun _ => 0)]
          · simp
          · intro u hu
            have : u ∉ J := fun h => absurd (ht u h) (not_lt.mpr hu)
            simp [hfzero u this]
        rw [ProbabilityTheory.cdf_eq_real, measureReal_def, h1]; rfl
      have hFmono' : ∀ a b, a ≤ b → ProbabilityTheory.cdf P a ≤ ProbabilityTheory.cdf P b :=
        fun a b h => (ProbabilityTheory.cdf P).mono h
      have hr : ∀ x, revHazardRecip P f x = ProbabilityTheory.cdf P x / f x := fun x => rfl
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJopen s₀ hs₀
      have hJball : ∀ x, |x - s₀| < ε → x ∈ J := fun x hx =>
        hball (by rw [Metric.mem_ball, Real.dist_eq]; exact hx)
      have hlo : s₀ - ε/2 ∈ J := hJball _ (by rw [abs_lt]; constructor <;> linarith)
      have hhi : s₀ + ε/2 ∈ J := hJball _ (by rw [abs_lt]; constructor <;> linarith)
      have hFs₀ : 0 < ProbabilityTheory.cdf P s₀ := by
        rcases (ProbabilityTheory.cdf_nonneg P s₀).lt_or_eq with h | h
        · exact h
        · exfalso
          have h0 := hFmono' (s₀ - ε/2) s₀ (by linarith)
          have h1 : ProbabilityTheory.cdf P (s₀ - ε/2) = 0 :=
            le_antisymm (by linarith) (ProbabilityTheory.cdf_nonneg P _)
          have := hinj hlo hs₀ (by rw [hr, hr, h1, ← h]; simp)
          linarith
      have hrcont : ContinuousOn (revHazardRecip P f) J :=
        (hFcont.continuousOn).div hfcont (fun t ht => (hfpos t ht).ne')
      have hsub : ∀ x ∈ J, ∀ y ∈ J, Set.Icc x y ⊆ J := fun x hx y hy => hJconn.out hx hy
      have hkey : ∀ x ∈ J, ∀ y ∈ J, x < y → (revHazardRecip P f x < revHazardRecip P f y ↔
          revHazardRecip P f s₀ < revHazardRecip P f (s₀ + ε/2)) := by
        intro x hx y hy hxy
        have hlo' : min x s₀ ∈ J := by rcases min_choice x s₀ with h | h <;> rw [h] <;> assumption
        have hhi' : max y (s₀ + ε/2) ∈ J := by
          rcases max_choice y (s₀+ε/2) with h | h <;> rw [h] <;> assumption
        have hS := hsub _ hlo' _ hhi'
        have hle : min x s₀ ≤ max y (s₀ + ε/2) :=
          le_trans (min_le_left _ _) (le_trans hxy.le (le_max_left _ _))
        have hxI : x ∈ Set.Icc (min x s₀) (max y (s₀ + ε/2)) :=
          ⟨min_le_left _ _, le_trans hxy.le (le_max_left _ _)⟩
        have hyI : y ∈ Set.Icc (min x s₀) (max y (s₀ + ε/2)) :=
          ⟨le_trans (min_le_left _ _) hxy.le, le_max_left _ _⟩
        have hsI : s₀ ∈ Set.Icc (min x s₀) (max y (s₀ + ε/2)) :=
          ⟨min_le_right _ _, by have := le_max_right y (s₀+ε/2); linarith⟩
        have hqI : s₀ + ε/2 ∈ Set.Icc (min x s₀) (max y (s₀ + ε/2)) :=
          ⟨by have := min_le_right x s₀; linarith, le_max_right _ _⟩
        rcases ContinuousOn.strictMonoOn_of_injOn_Icc' hle (hrcont.mono hS) (hinj.mono hS) with h | h
        · exact ⟨fun _ => h hsI hqI (by linarith), fun _ => h hxI hyI hxy⟩
        · exact ⟨fun h' => absurd (h hxI hyI hxy) (not_lt.mpr h'.le),
            fun h' => absurd (h hsI hqI (by linarith)) (not_lt.mpr h'.le)⟩
      have hdich : StrictMonoOn (revHazardRecip P f) J ∨ StrictAntiOn (revHazardRecip P f) J := by
        by_cases hc : revHazardRecip P f s₀ < revHazardRecip P f (s₀ + ε/2)
        · left; intro x hx y hy hxy; exact (hkey x hx y hy hxy).mpr hc
        · right; intro x hx y hy hxy
          rcases lt_trichotomy (revHazardRecip P f x) (revHazardRecip P f y) with h | h | h
          · exact absurd ((hkey x hx y hy hxy).mp h) hc
          · exact absurd (hinj hx hy h) hxy.ne
          · exact h
      have hc0 : 0 < revHazardRecip P f s₀ := div_pos hFs₀ (hfpos s₀ hs₀)
      obtain ⟨c, hc⟩ : ∃ c, c = revHazardRecip P f s₀ := ⟨_, rfl⟩
      have hmono : StrictMonoOn (revHazardRecip P f) J := by
        rcases hdich with h | h
        · exact h
        exfalso
        by_cases hbb : BddBelow J
        · have hJne : J.Nonempty := ⟨s₀, hs₀⟩
          have haJ : ∀ u ∈ J, sInf J < u := by
            intro u hu
            obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp hJopen u hu
            have h1 : u - δ/2 ∈ J :=
              hb (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
            have := csInf_le hbb h1
            linarith
          have hIoo : Set.Ioo (sInf J) s₀ ⊆ J := by
            intro t ht
            obtain ⟨u, hu, hut⟩ := exists_lt_of_csInf_lt hJne ht.1
            exact hsub u hu s₀ hs₀ ⟨hut.le, ht.2.le⟩
          have has : sInf J < s₀ := haJ s₀ hs₀
          have hd : ∀ t ∈ J, HasDerivAt (fun t => ProbabilityTheory.cdf P t * Real.exp (-t / c))
              (f t * Real.exp (-t / c) + ProbabilityTheory.cdf P t * (Real.exp (-t / c) * (-1 / c))) t := by
            intro t ht
            exact (hFderiv t ht).mul ((hasDerivAt_neg t).div_const c).exp
          have hφ : AntitoneOn (fun t => ProbabilityTheory.cdf P t * Real.exp (-t / c))
              (Set.Icc (sInf J) s₀) := by
            apply antitoneOn_of_deriv_nonpos (convex_Icc _ s₀)
            · exact (hFcont.mul (Real.continuous_exp.comp (continuous_neg.div_const c))).continuousOn
            · intro t ht; rw [interior_Icc] at ht
              exact (hd t (hIoo ht)).differentiableAt.differentiableWithinAt
            · intro t ht; rw [interior_Icc] at ht
              have htJ := hIoo ht
              rw [(hd t htJ).deriv]
              have h1 : c < revHazardRecip P f t := hc ▸ h htJ hs₀ ht.2
              have h2 : c * f t < ProbabilityTheory.cdf P t := by
                rw [hr] at h1; exact (lt_div_iff₀ (hfpos t htJ)).mp h1
              have hc0' : 0 < c := hc ▸ hc0
              have h3 : f t - ProbabilityTheory.cdf P t / c ≤ 0 := by
                rw [sub_nonpos, le_div_iff₀ hc0']; linarith
              have he := Real.exp_pos (-t / c)
              have : f t * Real.exp (-t / c) + ProbabilityTheory.cdf P t * (Real.exp (-t / c) * (-1 / c))
                  = (f t - ProbabilityTheory.cdf P t / c) * Real.exp (-t/c) := by ring
              rw [this]; exact mul_nonpos_of_nonpos_of_nonneg h3 he.le
          have := hφ ⟨le_refl _, has.le⟩ ⟨has.le, le_refl s₀⟩ has.le
          simp only at this
          rw [hF0 _ haJ, zero_mul] at this
          have := mul_pos hFs₀ (Real.exp_pos (-s₀ / c))
          linarith
        by_cases hba : BddAbove J
        · have h1 := hincr hba hbb hs₀ hhi (by linarith)
          have h2 := h hs₀ hhi (by linarith)
          linarith
        · have hge : ∀ t, s₀ ≤ t → t ∈ J := by
            intro t ht
            obtain ⟨u, hu, htu⟩ := not_bddAbove_iff.mp hba t
            exact hsub s₀ hs₀ u hu ⟨ht, htu.le⟩
          have hc0' : 0 < c := hc ▸ hc0
          obtain ⟨κ, hκ⟩ : ∃ κ, κ = ProbabilityTheory.cdf P s₀ / c := ⟨_, rfl⟩
          have hκ0 : 0 < κ := hκ ▸ div_pos hFs₀ hc0'
          have hlow : ∀ t, s₀ ≤ t → κ ≤ f t := by
            intro t ht
            have htJ := hge t ht
            have h1 : revHazardRecip P f t ≤ c := by
              rcases ht.lt_or_eq with h' | h'
              · exact hc ▸ (h hs₀ htJ h').le
              · exact le_of_eq (by rw [hc, h'])
            rw [hr] at h1
            have h2 : ProbabilityTheory.cdf P t ≤ c * f t := by
              have := (div_le_iff₀ (hfpos t htJ)).mp h1; linarith
            rw [hκ, div_le_iff₀ hc0']
            have := hFmono' _ _ ht
            linarith
          have hL := hFint s₀ (s₀ + 2/κ)
          have hint : ∫ t in s₀..(s₀ + 2/κ), κ ≤ ∫ t in s₀..(s₀ + 2/κ), f t :=
            intervalIntegral.integral_mono_on (by have := div_pos two_pos hκ0; linarith)
              intervalIntegrable_const hfint.intervalIntegrable (fun t ht => hlow t ht.1)
          rw [intervalIntegral.integral_const, smul_eq_mul] at hint
          have h3 : (s₀ + 2/κ - s₀) * κ = 2 := by field_simp; ring
          have := ProbabilityTheory.cdf_le_one P (s₀ + 2/κ)
          have := ProbabilityTheory.cdf_nonneg P s₀
          linarith
      have hhint : ∀ S, Integrable (fun x => max (S - x) 0) P := by
        intro S
        refine Integrable.mono' ((integrable_const (max S 0)).add hneg)
          ((continuous_const.sub continuous_id).max continuous_const).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall fun x => ?_
        show ‖max (S - x) 0‖ ≤ max S 0 + max (-x) 0
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        have h1 := le_max_left S 0
        have h2 := le_max_left (-x) 0
        have h3 := le_max_right S 0
        have h4 := le_max_right (-x) 0
        exact max_le (by linarith) (by linarith)
      have hhlow : ∀ x y, (y - x) * ProbabilityTheory.cdf P x ≤
          (∫ t, max (y - t) 0 ∂P) - ∫ t, max (x - t) 0 ∂P := by
        intro x y
        rw [← integral_sub (hhint y) (hhint x), ProbabilityTheory.cdf_eq_real, mul_comm,
          ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Iic]
        apply integral_mono ((integrable_const _).indicator measurableSet_Iic) ((hhint y).sub (hhint x))
        intro t
        show Set.indicator (Set.Iic x) (fun _ => y - x) t ≤ max (y - t) 0 - max (x - t) 0
        by_cases ht : t ∈ Set.Iic x
        · rw [Set.indicator_of_mem ht]; simp only [Set.mem_Iic] at ht
          rw [max_eq_left (by linarith : (0:ℝ) ≤ x - t)]
          linarith [le_max_left (y - t) 0]
        · rw [Set.indicator_of_notMem ht]; simp only [Set.mem_Iic, not_le] at ht
          rw [max_eq_right (by linarith : x - t ≤ 0)]
          linarith [le_max_right (y - t) 0]
      have hHd : ∀ x, HasDerivAt (fun S => ∫ t, max (S - t) 0 ∂P) (ProbabilityTheory.cdf P x) x := by
        intro x
        rw [hasDerivAt_iff_isLittleO]
        have hb : ∀ y, ‖(∫ t, max (y - t) 0 ∂P) - (∫ t, max (x - t) 0 ∂P) -
            (y - x) • ProbabilityTheory.cdf P x‖ ≤
            1 * ‖(y - x) * (ProbabilityTheory.cdf P y - ProbabilityTheory.cdf P x)‖ := by
          intro y
          have h1 := hhlow x y
          have h2 := hhlow y x
          have hA : 0 ≤ (∫ t, max (y - t) 0 ∂P) - (∫ t, max (x - t) 0 ∂P) -
            (y - x) * ProbabilityTheory.cdf P x := by linarith
          have hAB : (∫ t, max (y - t) 0 ∂P) - (∫ t, max (x - t) 0 ∂P) -
            (y - x) * ProbabilityTheory.cdf P x ≤
              (y - x) * (ProbabilityTheory.cdf P y - ProbabilityTheory.cdf P x) := by
            nlinarith
          rw [smul_eq_mul, one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA,
            abs_of_nonneg (le_trans hA hAB)]
          exact hAB
        have hO : (fun y => (∫ t, max (y - t) 0 ∂P) - (∫ t, max (x - t) 0 ∂P) -
            (y - x) • ProbabilityTheory.cdf P x) =O[nhds x]
            (fun y => (y - x) * (ProbabilityTheory.cdf P y - ProbabilityTheory.cdf P x)) :=
          Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall hb)
        have ho : (fun y => (y - x) * (ProbabilityTheory.cdf P y - ProbabilityTheory.cdf P x))
            =o[nhds x] (fun y => (y - x) * (1:ℝ)) := by
          apply (Asymptotics.isBigO_refl (fun y => y - x) (nhds x)).mul_isLittleO
          rw [Asymptotics.isLittleO_one_iff ℝ]
          have := (hFcont.tendsto x).sub_const (ProbabilityTheory.cdf P x)
          simpa using this
        simpa using hO.trans_isLittleO ho
      have hHint : ∀ x y, (∫ t, max (y - t) 0 ∂P) - (∫ t, max (x - t) 0 ∂P) =
          ∫ t in x..y, ProbabilityTheory.cdf P t := fun x y =>
        (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hHd t)
          hFmono.intervalIntegrable).symm
      have hq_int : ∀ a b, IntervalIntegrable
          (fun t => chat * ProbabilityTheory.cdf P t - M * f t) volume a b :=
        fun a b => (hFmono.intervalIntegrable.const_mul chat).sub
          (hfint.intervalIntegrable.const_mul M)
      have hg : ∀ x y, agentCostM P chat M y - agentCostM P chat M x =
          ∫ t in x..y, (chat * ProbabilityTheory.cdf P t - M * f t) := by
        intro x y
        rw [intervalIntegral.integral_sub (hFmono.intervalIntegrable.const_mul chat)
          (hfint.intervalIntegrable.const_mul M), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, ← hHint x y, ← hFint x y]
        unfold agentCostM; rw [hIci, hIci]; ring
      have hM : M = chat * revHazardRecip P f s₀ := by
        rw [hroot]; field_simp
      have hq : ∀ t ∈ J, chat * ProbabilityTheory.cdf P t - M * f t =
          f t * chat * (revHazardRecip P f t - revHazardRecip P f s₀) := by
        intro t ht
        have : ProbabilityTheory.cdf P t = revHazardRecip P f t * f t := by
          rw [hr, div_mul_cancel₀ _ (hfpos t ht).ne']
        rw [this, hM]; ring
      have hQ1 : ∀ t, s₀ < t → 0 < chat * ProbabilityTheory.cdf P t - M * f t := by
        intro t h
        by_cases ht : t ∈ J
        · rw [hq t ht]
          exact mul_pos (mul_pos (hfpos t ht) hchat) (sub_pos.mpr (hmono hs₀ ht h))
        · rw [hfzero t ht, mul_zero, sub_zero]
          exact mul_pos hchat (lt_of_lt_of_le hFs₀ (hFmono' _ _ h.le))
      have hQ3 : ∀ t ∈ J, t < s₀ → chat * ProbabilityTheory.cdf P t - M * f t < 0 := by
        intro t ht h
        rw [hq t ht]
        exact mul_neg_of_pos_of_neg (mul_pos (hfpos t ht) hchat) (sub_neg.mpr (hmono ht hs₀ h))
      have hQ2 : ∀ t, t < s₀ → chat * ProbabilityTheory.cdf P t - M * f t ≤ 0 := by
        intro t h
        by_cases ht : t ∈ J
        · exact (hQ3 t ht h).le
        · have : ∀ u ∈ J, t < u := by
            intro u hu
            by_contra hle; push_neg at hle
            exact ht (hsub u hu s₀ hs₀ ⟨hle, h.le⟩)
          rw [hfzero t ht, hF0 t this]; simp
      have hstrict : ∀ S, I ≤ S → S ≠ max I s₀ →
          agentCostM P chat M (max I s₀) < agentCostM P chat M S := by
        intro S hS hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hms : max I s₀ = s₀ := by
            rcases max_choice I s₀ with h | h
            · rw [h] at hlt; linarith
            · exact h
          rw [hms] at hlt ⊢
          have hgd := hg S s₀
          obtain ⟨d, hd⟩ : ∃ d, d = max ((S + s₀)/2) (s₀ - ε/2) := ⟨_, rfl⟩
          have hd0 := le_max_left ((S + s₀)/2) (s₀ - ε/2)
          have hd0' := le_max_right ((S + s₀)/2) (s₀ - ε/2)
          rw [← hd] at hd0 hd0'
          have hd1 : S < d := by linarith
          have hd2 : d < s₀ := by rw [hd]; exact max_lt (by linarith) (by linarith)
          have hdJ : d ∈ J := hJball d (by rw [abs_lt]; constructor <;> linarith)
          have hsplit := intervalIntegral.integral_add_adjacent_intervals (hq_int S d) (hq_int d s₀)
          have hA : ∫ t in S..d, (chat * ProbabilityTheory.cdf P t - M * f t) ≤ 0 := by
            have := intervalIntegral.integral_nonneg (μ := volume) hd1.le
              (f := fun t => -(chat * ProbabilityTheory.cdf P t - M * f t))
              (fun u hu => by have := hQ2 u (by linarith [hu.2]); linarith)
            rw [intervalIntegral.integral_neg] at this; linarith
          have hB : ∫ t in d..s₀, (chat * ProbabilityTheory.cdf P t - M * f t) < 0 := by
            have := intervalIntegral.intervalIntegral_pos_of_pos_on
              (f := fun t => -(chat * ProbabilityTheory.cdf P t - M * f t)) (hq_int d s₀).neg
              (fun u hu => by
                have := hQ3 u (hsub d hdJ s₀ hs₀ ⟨hu.1.le, hu.2.le⟩) hu.2; linarith) hd2
            rw [intervalIntegral.integral_neg] at this; linarith
          linarith
        · have h1 := intervalIntegral.intervalIntegral_pos_of_pos_on (hq_int _ S)
            (fun u hu => hQ1 u (lt_of_le_of_lt (le_max_right I s₀) hu.1)) hgt
          have h2 := hg (max I s₀) S
          linarith
      ext S
      simp only [EarlyInspect.Align.argminFrom, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hIS, hmin⟩
        by_contra hne
        have h1 := hstrict S hIS hne
        have h2 := hmin (max I s₀) (le_max_left _ _)
        linarith
      · rintro rfl
        refine ⟨le_max_left _ _, fun S' hS' => ?_⟩
        by_cases h : S' = max I s₀
        · rw [h]
        · exact (hstrict S' hS' h).le
