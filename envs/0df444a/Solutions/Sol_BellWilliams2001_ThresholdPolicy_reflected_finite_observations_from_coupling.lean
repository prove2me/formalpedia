-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.reflected_finite_observations_from_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:08:14.109729+00:00
-- url     : https://prove2.me/submissions/f3c0595f-9e17-4462-a83a-bf1a4809d752

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_past_infimum_from_dyadic_grid
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

private theorem cadlag_compact_bounds (f : ℝ → ℝ) (hf : IsCadlag f) (T : ℝ) :
    ∃ C ≥ (0:ℝ), ∀ t ∈ Set.Icc (0:ℝ) T, |f t| ≤ C := by
  have hl (s : ℝ) (hs : s ∈ Icc (0:ℝ) T) :
      ∃ r > (0:ℝ), ∃ C ≥ (0:ℝ), ∀ t ∈ Metric.ball s r ∩ Icc (0:ℝ) T, |f t| ≤ C := by
    obtain ⟨r,hr,hright⟩ := Metric.continuousWithinAt_iff.1 (hf.1 s hs.1) 1 zero_lt_one
    rcases hs.1.eq_or_lt with h | h
    · refine ⟨r,hr,|f s|+1,by positivity,?_⟩
      intro t ht
      have hts : s ≤ t := h ▸ ht.2.1
      have hft := hright hts ht.1
      rw [Real.dist_eq] at hft
      have w := abs_add_le (f t-f s) (f s)
      rw [sub_add_cancel] at w
      linarith
    · obtain ⟨u,hu⟩ := hf.2 s h
      have hleft := (Metric.tendsto_nhdsWithin_nhds.1 hu) 1 zero_lt_one
      obtain ⟨q,hq,hq'⟩ := hleft
      refine ⟨min r q,lt_min hr hq,max |f s| |u|+1,by positivity,?_⟩
      intro t ht
      have ht' : dist t s < min r q := ht.1
      rcases le_or_gt s t with hst | hst
      · have hft := hright hst (lt_min_iff.1 ht').1
        rw [Real.dist_eq] at hft
        have w := abs_add_le (f t-f s) (f s)
        rw [sub_add_cancel] at w
        linarith [le_max_left |f s| |u|]
      · have hft := hq' hst (lt_min_iff.1 ht').2
        rw [Real.dist_eq] at hft
        have w := abs_add_le (f t-u) u
        rw [sub_add_cancel] at w
        linarith [le_max_right |f s| |u|]
  choose r hr C hC h using fun s : Icc (0:ℝ) T => hl s s.2
  obtain ⟨S,hS⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).elim_finite_subcover
    (fun s : Icc (0:ℝ) T => Metric.ball (s:ℝ) (r s))
    (fun _ => Metric.isOpen_ball) (by
      intro s hs
      exact mem_iUnion.2 ⟨⟨s,hs⟩,Metric.mem_ball_self (hr ⟨s,hs⟩)⟩)
  refine ⟨∑ s ∈ S,C s,Finset.sum_nonneg (fun s _ => hC s),?_⟩
  intro t ht
  obtain ⟨s,hs,hst⟩ := mem_iUnion₂.1 (hS ht)
  exact (h s t ⟨hst,ht⟩).trans (Finset.single_le_sum (fun s _ => hC s) hs)

private noncomputable def grid (t : ℝ≥0) (p : ℕ × ℕ) : ℝ≥0 :=
  ⟨min (t:ℝ) ((p.2 : ℝ) / (2 : ℝ) ^ p.1), le_min t.2 (by positivity)⟩

private noncomputable def reflectionObs (t : ℝ≥0) (κ : ℝ)
    (f : ℝ≥0 → Fin 1 → ℝ) : ℝ≥0∞ :=
  ⨆ p : ℕ × ℕ, ENNReal.ofReal (κ * (f t 0 - f (grid t p) 0))

private theorem measurable_reflectionObs (t : ℝ≥0) (κ : ℝ) :
    Measurable (reflectionObs t κ) := by
  refine Measurable.iSup (fun p => ?_)
  have hval (s : ℝ≥0) : Measurable (fun f : ℝ≥0 → Fin 1 → ℝ => f s 0) :=
    (measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply s)
  simpa only [Pi.sub_def] using (((hval t).sub (hval (grid t p))).const_mul κ).ennreal_ofReal


private theorem point_of_uoc (U : ℕ → ℝ → Fin 1 → ℝ) (V : ℝ → Fin 1 → ℝ)
    (h : ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => supDist (U n) V t) atTop (𝓝 0))
    (t : ℝ≥0) :
    Tendsto (fun n => U n t 0) atTop (𝓝 (V t 0)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [(h t t.2).eventually_lt_const (ENNReal.ofReal_pos.2 hε)] with n hn
  have hSup : ENNReal.ofReal |U n t 0 - V t 0| ≤ supDist (U n) V t := by
    apply le_iSup_of_le (t : ℝ)
    apply le_iSup_of_le (show (t:ℝ) ∈ Icc (0:ℝ) (t:ℝ) from ⟨t.2,le_rfl⟩)
    simp
  rw [Real.dist_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (hSup.trans_lt hn)

private noncomputable def pathGridInf (t : ℝ≥0) (f : ℝ≥0 → Fin 1 → ℝ) : ℝ :=
  (⨅ p : ℕ × ℕ, f (grid t p) 0)

private theorem reflectionObs_toReal (f : ℝ≥0 → Fin 1 → ℝ) (t : ℝ≥0)
    (hb : BddBelow (range (fun p : ℕ × ℕ => f (grid t p) 0))) :
    (reflectionObs t 1 f).toReal = f t 0 - pathGridInf t f := by
  let a := f t 0-pathGridInf t f
  have ht : ∃ p : ℕ × ℕ, grid t p = t := by
    obtain ⟨n,hn⟩ := exists_nat_ge (t:ℝ)
    refine ⟨(0,n),Subtype.ext ?_⟩
    change min (t:ℝ) ((n:ℝ)/(2:ℝ)^0) = (t:ℝ)
    simp [min_eq_left hn]
  obtain ⟨p,hp⟩ := ht
  have ha : 0 ≤ a := by
    have h := ciInf_le hb p
    rw [hp] at h
    exact sub_nonneg.mpr h
  have hu : reflectionObs t 1 f ≤ ENNReal.ofReal a := by
    refine iSup_le fun p => ?_
    simp only [one_mul]
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (ciInf_le hb p) _)
  have hT : reflectionObs t 1 f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hl : a ≤ (reflectionObs t 1 f).toReal := by
    have h (p : ℕ × ℕ) : f t 0-(reflectionObs t 1 f).toReal ≤ f (grid t p) 0 := by
      have h0 := ENNReal.toReal_mono hT (le_iSup (fun j : ℕ × ℕ =>
        ENNReal.ofReal (1*(f t 0-f (grid t j) 0))) p)
      rw [one_mul,ENNReal.toReal_ofReal'] at h0
      linarith [le_max_left (f t 0-f (grid t p) 0) 0]
    have h1 := le_ciInf h
    change f t 0-(reflectionObs t 1 f).toReal ≤ pathGridInf t f at h1
    linarith
  have hu' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  rw [ENNReal.toReal_ofReal ha] at hu'
  exact le_antisymm hu' hl

private theorem reflected_values (f : ℝ → ℝ) (t : ℝ≥0)
    (hR : ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt f (Ici s) s)
    (hb : BddBelow (range (fun s : Icc (0:ℝ) (t:ℝ) => f s))) :
    (reflectionObs t 1 (fun u => ![f u])).toReal =
      f t - ⨅ s : Icc (0:ℝ) (t:ℝ), f s := by
  have hd := past_infimum_from_dyadic_grid f t hR hb
  have hNon : 0 ≤ f t-⨅ s : Icc (0:ℝ) (t:ℝ), f s :=
    sub_nonneg.mpr (ciInf_le hb (⟨t,t.2,le_rfl⟩ : Icc (0:ℝ) (t:ℝ)))
  have heq : reflectionObs t 1 (fun u => ![f u]) =
      ENNReal.ofReal (f t-⨅ s : Icc (0:ℝ) (t:ℝ), f s) := by
    change (⨆ p : ℕ × ℕ, ENNReal.ofReal (1 * (f t -
      f (min (t:ℝ) ((p.2:ℝ)/(2:ℝ)^p.1))))) = _
    simpa using hd.symm
  rw [heq,ENNReal.toReal_ofReal hNon]

private theorem grid_reflection_converges (Y : ℕ → ℝ → Fin 1 → ℝ)
    (Z : ℝ → Fin 1 → ℝ) (hCad : ∀ n, IsCadlag (fun s => Y n s 0))
    (hU : ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => supDist (Y n) Z t) atTop (𝓝 0))
    (t : ℝ≥0) :
    Tendsto (fun n => (reflectionObs t 1 (fun u => Y n u)).toReal) atTop
      (𝓝 ((reflectionObs t 1 (fun u => Z u)).toReal)) := by
  have boundY (n : ℕ) : BddBelow (range
      (fun p : ℕ × ℕ => Y n (grid t p) 0)) := by
    obtain ⟨D,_,hD⟩ := cadlag_compact_bounds _ (hCad n) t
    exact ⟨-D,fun _ ⟨p,hp⟩ => hp ▸ (abs_le.1 (hD (grid t p)
      ⟨(grid t p).2,min_le_left _ _⟩)).1⟩
  have hErr (ε : ℝ) (he : 0 < ε) :
      ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) (t:ℝ), |Y n s 0-Z s 0| ≤ ε := by
    filter_upwards [(hU t t.2).eventually_lt_const (ENNReal.ofReal_pos.2 he)] with n hn s hs
    have hu : ENNReal.ofReal |Y n s 0-Z s 0| ≤ supDist (Y n) Z t := by
      apply le_iSup_of_le s
      apply le_iSup_of_le hs
      simp
    exact ((ENNReal.ofReal_lt_ofReal_iff he).1 (hu.trans_lt hn)).le
  have boundZ : BddBelow (range (fun p : ℕ × ℕ => Z (grid t p) 0)) := by
    obtain ⟨n,hn⟩ := (hErr 1 zero_lt_one).exists
    obtain ⟨d,hd⟩ := boundY n
    refine ⟨d-1,fun _ ⟨p,hp⟩ => hp ▸ ?_⟩
    have hP := (abs_le.1 (hn (grid t p) ⟨(grid t p).2,min_le_left _ _⟩)).2
    have hQ := hd ⟨p,rfl⟩
    linarith
  have hr (n : ℕ) := reflectionObs_toReal (fun u : ℝ≥0 => Y n u) t (boundY n)
  have hz := reflectionObs_toReal (fun u : ℝ≥0 => Z u) t boundZ
  simp_rw [hr,hz]
  have hi : Tendsto (fun n => pathGridInf t (fun u => Y n u)) atTop
      (𝓝 (pathGridInf t (fun u => Z u))) := by
    apply Metric.tendsto_nhds.2
    intro ε he
    filter_upwards [hErr (ε/2) (by positivity)] with n hn
    have h1 : pathGridInf t (fun u => Z u)-ε/2 ≤ pathGridInf t (fun u => Y n u) := by
      apply le_ciInf
      intro p
      have hP := ciInf_le boundZ p
      have hQ := (abs_le.1 (hn (grid t p) ⟨(grid t p).2,min_le_left _ _⟩)).1
      change pathGridInf t (fun u => Z u) ≤ _ at hP
      linarith
    have h2 : pathGridInf t (fun u => Y n u)-ε/2 ≤ pathGridInf t (fun u => Z u) := by
      apply le_ciInf
      intro p
      have hP := ciInf_le (boundY n) p
      have hQ := (abs_le.1 (hn (grid t p) ⟨(grid t p).2,min_le_left _ _⟩)).2
      change pathGridInf t (fun u => Y n u) ≤ _ at hP
      linarith
    rw [Real.dist_eq]
    apply abs_lt.2
    constructor <;> linarith
  exact (point_of_uoc Y Z hU t).sub hi

set_option maxHeartbeats 2500000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ℝ → ℝ) (Z : Ω' → ℝ → ℝ)
    (hX : ∀ n ω, IsCadlag (X n ω))
    (hXm : ∀ n t, 0 ≤ t → AEMeasurable (fun ω => X n ω t) P)
    (hZ : ∀ᵐ ω ∂P', Continuous (Z ω))
    (hCouple : CouplingConverges P P' (fun n ω t => ![X n ω t]) (fun ω t => ![Z ω t]))
    (a b : ℕ → ℝ) (A B : ℝ) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    let R (x : ℝ → ℝ) (t : ℝ) := x t-⨅ s : Icc (0:ℝ) t, x s
    let V (x : ℝ → ℝ) (t : ℝ) := -(⨅ s : Icc (0:ℝ) t, x s)
    let Y (n : ℕ) (ω : Ω) (t : ℝ) := ![0,a n*R (X n ω) t,0,b n*V (X n ω) t]
    let W (ω : Ω') (t : ℝ) := ![0,A*R (Z ω) t,0,B*V (Z ω) t]
    ∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => Y n ω (τ j)) atTop
        (fun ω j => W ω (τ j)) (fun _ => P) P' := by
  classical
  intro R V Y W q τ hτ
  obtain ⟨Λ,mΛ,Q,U,F,hQ,hLaw,hL,hCad,hConv⟩ := hCouple
  letI : IsProbabilityMeasure Q := hQ
  let T (j : Fin q) : ℝ≥0 := ⟨τ j,hτ j⟩
  let obs (a b : ℝ) (x : ℝ≥0 → Fin 1 → ℝ) (j : Fin q) : Fin 4 → ℝ :=
    let r := (reflectionObs (T j) 1 x).toReal
    ![0,a*r,0,b*(r-x (T j) 0)]
  have hm (a b : ℝ) : Measurable (obs a b) := by
    apply measurable_pi_lambda
    intro j
    have hR := ENNReal.measurable_toReal.comp (measurable_reflectionObs (T j) 1)
    have hi : Measurable (fun x : ℝ≥0 → Fin 1 → ℝ => x (T j) 0) :=
      (measurable_pi_apply (0:Fin 1)).comp (measurable_pi_apply (T j))
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact measurable_const
    · exact hR.const_mul a
    · exact measurable_const
    · simpa [obs, Function.comp_def,Pi.sub_def] using (hR.sub hi).const_mul b
  have hXobs (n : ℕ) (ω : Ω) : obs (a n) (b n) (fun s => ![X n ω s]) =
      fun j => Y n ω (τ j) := by
    funext j
    obtain ⟨D,_,hD⟩ := cadlag_compact_bounds (X n ω) (hX n ω) (τ j)
    have hh : BddBelow (range (fun s : Icc (0:ℝ) (τ j) => X n ω s)) :=
      ⟨-D,fun _ ⟨s,hs⟩ => hs ▸ (abs_le.1 (hD s s.2)).1⟩
    have hr := reflected_values (X n ω) (T j) (hX n ω).1 hh
    dsimp only [obs,Y]
    rw [hr]
    funext i
    fin_cases i <;> simp only [R,V,T,NNReal.coe_mk, Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceFinMk] <;> first | rfl | (congr 2 <;> ring <;> rfl)
  have hZobs : ∀ᵐ ω ∂P', obs A B (fun s => ![Z ω s]) = fun j => W ω (τ j) := by
    filter_upwards [hZ] with ω hω
    funext j
    have hh : BddBelow (range (fun s : Icc (0:ℝ) (τ j) => Z ω s)) := by
      rw [←Set.image_eq_range]
      exact (isCompact_Icc.image hω).bddBelow
    have hr := reflected_values (Z ω) (T j) (fun _ _ => hω.continuousWithinAt) hh
    dsimp only [obs,W]
    rw [hr]
    funext i
    fin_cases i <;> simp only [R,V,T,NNReal.coe_mk, Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceFinMk] <;> first | rfl | (congr 2 <;> ring <;> rfl)
  have hPre (n : ℕ) : AEMeasurable (fun ω j => Y n ω (τ j)) P := by
    have hCount (j : Fin q) : AEMeasurable
        (fun ω => (reflectionObs (T j) 1 (fun s => ![X n ω s])).toReal) P := by
      apply ENNReal.measurable_toReal.comp_aemeasurable
      apply AEMeasurable.iSup
      intro p
      exact (((hXm n (T j) (T j).2).sub (hXm n (grid (T j) p) (grid (T j) p).2)).const_mul 1).ennreal_ofReal
    have he : AEMeasurable (fun ω => obs (a n) (b n) (fun s => ![X n ω s])) P := by
      apply aemeasurable_pi_lambda
      intro j
      apply aemeasurable_pi_lambda
      intro i
      fin_cases i
      · exact aemeasurable_const
      · exact (hCount j).const_mul _
      · exact aemeasurable_const
      · simpa [obs,Pi.sub_def] using ((hCount j).sub (hXm n (T j) (T j).2)).const_mul (b n)
    simpa only [hXobs] using he
  let Un (n : ℕ) (ω : Λ) := obs (a n) (b n) (fun s => U n ω s)
  let Lim (ω : Λ) := obs A B (fun s => F ω s)
  have hPreLaw : ∀ᶠ n in atTop, IdentDistrib (Un n) (fun ω j => Y n ω (τ j)) Q P := by
    filter_upwards [hLaw] with n hn
    have h := hn.comp (hm (a n) (b n))
    exact h.trans (.of_ae_eq h.aemeasurable_snd (ae_of_all _ (hXobs n)))
  have hLimLaw : IdentDistrib Lim (fun ω j => W ω (τ j)) Q P' :=
    let h := hL.comp (hm A B)
    h.trans (.of_ae_eq h.aemeasurable_snd hZobs)
  let un (n : ℕ) := if AEMeasurable (Un n) Q then Un n else fun _ => 0
  have hun (n : ℕ) : AEMeasurable (un n) Q := by
    dsimp [un]
    split <;> first | assumption | exact aemeasurable_const
  have hEq : un =ᶠ[atTop] Un := hPreLaw.mono fun n hn => if_pos hn.aemeasurable_fst
  have hv : ∀ᵐ ω ∂Q, Tendsto (fun n => un n ω) atTop (𝓝 (Lim ω)) := by
    filter_upwards [hConv] with ω hω
    apply Tendsto.congr' (hEq.symm.mono fun n hn => congrFun hn ω)
    apply tendsto_pi_nhds.2
    intro j
    have hR := grid_reflection_converges (fun n => U n ω) (F ω) (fun n => hCad n ω 0) hω (T j)
    have hz := point_of_uoc (fun n => U n ω) (F ω) hω (T j)
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact ha.mul hR
    · exact tendsto_const_nhds
    · exact hb.mul (hR.sub hz)
  have hWeak := tendstoInDistribution_of_ae_tendsto hun hLimLaw.aemeasurable_fst hv
  refine ⟨hPre,hLimLaw.aemeasurable_snd,?_⟩
  have hLmap : (⟨Q.map Lim,Measure.isProbabilityMeasure_map hLimLaw.aemeasurable_fst⟩ :
      ProbabilityMeasure (Fin q → Fin 4 → ℝ)) =
    ⟨P'.map (fun ω j => W ω (τ j)),Measure.isProbabilityMeasure_map hLimLaw.aemeasurable_snd⟩ :=
    Subtype.ext hLimLaw.map_eq
  rw [←hLmap]
  refine hWeak.tendsto.congr' ?_
  filter_upwards [hEq,hPreLaw] with n he hl
  apply Subtype.ext
  change Q.map (un n) = P.map (fun ω j => Y n ω (τ j))
  rw [he,hl.map_eq]
