-- Prove2me | solution 1 for DriverSurge.IC.remark_1_continuity
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T04:31:28.721027+00:00
-- url     : https://prove2.me/submissions/2f07ec4f-a759-4013-bf31-842659f6a79e

import Mathlib
import Definitions.Def_DriverSurge_IC_Pricing
open MeasureTheory Set Filter Topology
namespace Queelius.DriverMarginal
open DriverSurge.IC
lemma other_other (i : Fin 2) : other (other i)=i := by fin_cases i <;> rfl
lemma other_ne (i : Fin 2) : other i≠i := by fin_cases i <;> decide
lemma ae_nonnegative (P : Primitives) (i : Fin 2) : ∀ᵐ x ∂P.F i,(0:ℝ) ≤ x := by
  apply ae_iff.mpr
  apply measure_mono_null _ (P.support i)
  intro x hx
  change ¬0 ≤ x at hx
  exact (lt_of_not_ge hx).le
lemma q_continuous (P : Primitives) (i : Fin 2) : Continuous (q P i) := by
  unfold q
  fun_prop
lemma q_bounds (P : Primitives) (i : Fin 2) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ q P i x ∧ q P i x ≤ 1 := by
  have hs : 0 < P.sw i+P.sw (other i) := add_pos (P.sw_pos i) (P.sw_pos (other i))
  have hc0 : 0 ≤ P.sw i/(P.sw i+P.sw (other i)) := (div_pos (P.sw_pos i) hs).le
  have hc1 : P.sw i/(P.sw i+P.sw (other i)) ≤ 1 := (div_le_one hs).mpr (by linarith [P.sw_pos (other i)])
  have he0 := (Real.exp_pos (-(P.sw i+P.sw (other i))*x)).le
  have he1 : Real.exp (-(P.sw i+P.sw (other i))*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  unfold q
  constructor
  · exact mul_nonneg hc0 (by linarith)
  · nlinarith
lemma q_integrable (P : Primitives) (i : Fin 2) : Integrable (q P i) (P.F i) := by
  letI : IsProbabilityMeasure (P.F i) := P.prob i
  apply Integrable.mono' (integrable_const (1:ℝ)) (q_continuous P i).aestronglyMeasurable
  filter_upwards [ae_nonnegative P i] with x hx
  have hh := q_bounds P i x hx
  simpa [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
lemma Tn_one_le (P : Primitives) (i : Fin 2) (s : Set ℝ) : 1 ≤ Tn P i s := by
  have h : 0 ≤ ∫ x in s,x ∂P.F i := integral_nonneg_of_ae ((ae_nonnegative P i).filter_mono (ae_mono (Measure.restrict_le_self)))
  unfold Tn
  nlinarith [P.lam_pos i]
lemma Qn_sw_le (P : Primitives) (i : Fin 2) (s : Set ℝ) : P.sw i ≤ Qn P i s := by
  have hq : ∀ᵐ x ∂(P.F i).restrict s,0 ≤ q P i x := by
    filter_upwards [(ae_nonnegative P i).filter_mono (ae_mono Measure.restrict_le_self)] with x hx
    exact (q_bounds P i x hx).1
  have h := integral_nonneg_of_ae hq
  unfold Qn
  nlinarith [P.lam_pos i]
lemma Tn_pos (P : Primitives) (i : Fin 2) (s : Set ℝ) : 0 < Tn P i s := lt_of_lt_of_le zero_lt_one (Tn_one_le P i s)
lemma Qn_pos (P : Primitives) (i : Fin 2) (s : Set ℝ) : 0 < Qn P i s := lt_of_lt_of_le (P.sw_pos i) (Qn_sw_le P i s)
lemma denominator_pos (P : Primitives) (σ : Fin 2 → Set ℝ) (i : Fin 2) :
    0 < Qn P i (σ i)*Tn P (other i) (σ (other i))+Qn P (other i) (σ (other i))*Tn P i (σ i) :=
  add_pos (mul_pos (Qn_pos P i _) (Tn_pos P (other i) _)) (mul_pos (Qn_pos P (other i) _) (Tn_pos P i _))
lemma reward_quotient (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2) :
    rewardCF P w σ =
      (Qn P (other i) (σ (other i))*Wn P i (w i) (σ i)+Qn P i (σ i)*Wn P (other i) (w (other i)) (σ (other i))) /
      (Qn P (other i) (σ (other i))*Tn P i (σ i)+Qn P i (σ i)*Tn P (other i) (σ (other i))) := by
  have hT0 := ne_of_gt (Tn_pos P 0 (σ 0))
  have hT1 := ne_of_gt (Tn_pos P 1 (σ 1))
  have hD : Qn P 1 (σ 1)*Tn P 0 (σ 0)+Qn P 0 (σ 0)*Tn P 1 (σ 1) ≠ 0 :=
    ne_of_gt (add_pos (mul_pos (Qn_pos P 1 _) (Tn_pos P 0 _)) (mul_pos (Qn_pos P 0 _) (Tn_pos P 1 _)))
  have hbase : rewardCF P w σ =
      (Qn P 1 (σ 1)*Wn P 0 (w 0) (σ 0)+Qn P 0 (σ 0)*Wn P 1 (w 1) (σ 1)) /
      (Qn P 1 (σ 1)*Tn P 0 (σ 0)+Qn P 0 (σ 0)*Tn P 1 (σ 1)) := by
    unfold rewardCF
    rw [Fin.sum_univ_two]
    change (Tn P 0 (σ 0)*Qn P 1 (σ 1)/(Tn P 1 (σ 1)*Qn P 0 (σ 0)+Tn P 0 (σ 0)*Qn P 1 (σ 1))*(Wn P 0 (w 0) (σ 0)/Tn P 0 (σ 0)) +
      Tn P 1 (σ 1)*Qn P 0 (σ 0)/(Tn P 0 (σ 0)*Qn P 1 (σ 1)+Tn P 1 (σ 1)*Qn P 0 (σ 0))*(Wn P 1 (w 1) (σ 1)/Tn P 1 (σ 1))) = _
    have hd1 : Tn P 1 (σ 1)*Qn P 0 (σ 0)+Tn P 0 (σ 0)*Qn P 1 (σ 1) ≠ 0 := ne_of_gt (add_pos (mul_pos (Tn_pos P 1 _) (Qn_pos P 0 _)) (mul_pos (Tn_pos P 0 _) (Qn_pos P 1 _)))
    have hd2 : Tn P 0 (σ 0)*Qn P 1 (σ 1)+Tn P 1 (σ 1)*Qn P 0 (σ 0) ≠ 0 := ne_of_gt (add_pos (mul_pos (Tn_pos P 0 _) (Qn_pos P 1 _)) (mul_pos (Tn_pos P 1 _) (Qn_pos P 0 _)))
    field_simp
    <;> ring
  fin_cases i
  · exact hbase
  · change rewardCF P w σ = (Qn P 0 (σ 0)*Wn P 1 (w 1) (σ 1)+Qn P 1 (σ 1)*Wn P 0 (w 0) (σ 0)) /
      (Qn P 0 (σ 0)*Tn P 1 (σ 1)+Qn P 1 (σ 1)*Tn P 0 (σ 0))
    rw [hbase]
    congr 1 <;> ring

lemma rFun_continuous_u (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2)
    (hw : ContinuousOn (w i) (Ioi 0)) : ContinuousOn (rFun P w σ i) (Ioi 0) := by
  unfold rFun
  have hq : ContinuousOn (q P i) (Ioi 0) := (q_continuous P i).continuousOn
  have hnonzero : ∀ u ∈ Ioi (0:ℝ),u≠0 := fun u hu => ne_of_gt hu
  exact (((hq.div continuousOn_id hnonzero).mul continuousOn_const).add
    ((hw.div continuousOn_id hnonzero).mul continuousOn_const)).sub continuousOn_const
lemma empty_policy_control (P : Primitives) (i : Fin 2) (w : ℝ → ℝ) :
    Wn P i w ∅=0 ∧ Tn P i ∅=1 ∧ Qn P i ∅=P.sw i := by simp [Wn,Tn,Qn]
lemma integral_small {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) (hg : Integrable g μ)
    (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ,0 < δ ∧ ∀ s : Set α,μ s < ENNReal.ofReal δ → |∫ x in s,g x ∂μ| < ε := by
  let L : Filter (Set α) := Filter.comap (fun s => μ s) (𝓝 0)
  have hμ : Tendsto (fun s : Set α => μ s) L (𝓝 0) := Filter.tendsto_comap
  have ht : Tendsto (fun s : Set α => ∫ x in s,g x ∂μ) L (𝓝 0) := hg.tendsto_setIntegral_nhds_zero hμ
  have hball : {x : ℝ | |x| < ε} ∈ 𝓝 (0:ℝ) := by simpa [Metric.ball,Real.dist_eq] using Metric.ball_mem_nhds (0:ℝ) hε
  have he := ht.eventually hball
  change ∀ᶠ s : Set α in Filter.comap (fun s => μ s) (𝓝 0),|∫ x in s,g x ∂μ| < ε at he
  rw [Filter.eventually_comap] at he
  obtain ⟨a,ha,haspec⟩ := ENNReal.nhds_zero_basis.mem_iff.mp he
  obtain ⟨δ,hδ0,hδpos,hδa⟩ := ENNReal.lt_iff_exists_real_btwn.mp ha
  refine ⟨δ,ENNReal.ofReal_pos.mp hδpos,fun s hs => ?_⟩
  exact haspec (lt_trans hs hδa) s rfl
lemma integral_difference_bound (μ : Measure ℝ) (g : ℝ → ℝ) (hg : Integrable g μ)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    |(∫ x in t,g x ∂μ)-(∫ x in s,g x ∂μ)| ≤ ∫ x in symmDiff s t,|g x| ∂μ := by
  classical
  rw [← integral_indicator ht,← integral_indicator hs,← integral_sub (hg.indicator ht) (hg.indicator hs)]
  have hb (x : ℝ) : ‖t.indicator g x-s.indicator g x‖ ≤ (symmDiff s t).indicator (fun x => |g x|) x := by
    by_cases hxs : x∈s <;> by_cases hxt : x∈t <;> simp [Set.indicator_of_mem,Set.indicator_of_notMem,hxs,hxt,Real.norm_eq_abs,mem_symmDiff]
  have hi : Integrable (fun x => |g x|) μ := hg.abs
  calc
    _ ≤ ∫ x,‖t.indicator g x-s.indicator g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x,(symmDiff s t).indicator (fun x => |g x|) x ∂μ :=
      integral_mono_ae ((hg.indicator ht).sub (hg.indicator hs)).norm (hi.indicator (hs.symmDiff ht)) (ae_of_all _ hb)
    _ = _ := integral_indicator (hs.symmDiff ht)
lemma set_integral_continuous (μ : Measure ℝ) (g : ℝ → ℝ) (hg : Integrable g μ) :
    ContinuousInSet μ (fun s => ∫ x in s,g x ∂μ) := by
  intro s hs ε hε
  obtain ⟨δ,hδ,hδspec⟩ := integral_small μ (fun x => |g x|) hg.abs ε hε
  refine ⟨δ,hδ,fun t ht hst => ?_⟩
  have hi := hδspec (symmDiff s t) hst
  have hn : 0 ≤ ∫ x in symmDiff s t,|g x| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  rw [abs_of_nonneg hn] at hi
  exact (integral_difference_bound μ g hg s t hs.1.measurableSet ht.1.measurableSet).trans_lt hi
lemma policy_integral_continuous (P : Primitives) (i : Fin 2) (g : ℝ → ℝ) (hg : Integrable g (P.F i)) :
    ContinuousInPolicy P (fun σ => ∫ x in σ i,g x ∂P.F i) := by
  intro σ hσ ε hε
  obtain ⟨δ,hδ,hδspec⟩ := set_integral_continuous (P.F i) g hg (σ i) (hσ i) ε hε
  refine ⟨δ,hδ,fun τ hτ hστ => ?_⟩
  apply hδspec (τ i) (hτ i)
  have hi : P.F i (symmDiff (σ i) (τ i)) ≤ ∑ j : Fin 2,P.F j (symmDiff (σ j) (τ j)) :=
    Finset.single_le_sum (f := fun j : Fin 2 => P.F j (symmDiff (σ j) (τ j))) (fun j _ => bot_le) (Finset.mem_univ i)
  exact hi.trans_lt hστ
lemma policy_binary (P : Primitives) (G H : (Fin 2 → Set ℝ) → ℝ)
    (hG : ContinuousInPolicy P G) (hH : ContinuousInPolicy P H) (F : ℝ × ℝ → ℝ)
    (hF : ∀ σ,IsPolicy σ → ContinuousAt F (G σ,H σ)) :
    ContinuousInPolicy P (fun σ => F (G σ,H σ)) := by
  intro σ hσ ε hε
  obtain ⟨η,hη,hηspec⟩ := Metric.continuousAt_iff.mp (hF σ hσ) ε hε
  obtain ⟨δG,hδG,hGspec⟩ := hG σ hσ η hη
  obtain ⟨δH,hδH,hHspec⟩ := hH σ hσ η hη
  refine ⟨min δG δH,lt_min hδG hδH,fun τ hτ hdist => ?_⟩
  have hg := hGspec τ hτ (hdist.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
  have hh := hHspec τ hτ (hdist.trans_le (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  have hin : dist (G τ,H τ) (G σ,H σ) < η := by simpa [Prod.dist_eq,Real.dist_eq] using max_lt hg hh
  have hout := hηspec hin
  simpa [Real.dist_eq] using hout
lemma policy_const (P : Primitives) (c : ℝ) : ContinuousInPolicy P (fun _ => c) := by
  intro σ hσ ε hε
  exact ⟨1,by norm_num,fun τ hτ hd => by simpa using hε⟩
lemma policy_add (P : Primitives) (G H : (Fin 2 → Set ℝ) → ℝ)
    (hG : ContinuousInPolicy P G) (hH : ContinuousInPolicy P H) :
    ContinuousInPolicy P (fun σ => G σ+H σ) :=
  policy_binary P G H hG hH (fun z => z.1+z.2) (fun _ _ => by fun_prop)
lemma policy_mul (P : Primitives) (G H : (Fin 2 → Set ℝ) → ℝ)
    (hG : ContinuousInPolicy P G) (hH : ContinuousInPolicy P H) :
    ContinuousInPolicy P (fun σ => G σ*H σ) :=
  policy_binary P G H hG hH (fun z => z.1*z.2) (fun _ _ => by fun_prop)
lemma policy_div (P : Primitives) (G H : (Fin 2 → Set ℝ) → ℝ)
    (hG : ContinuousInPolicy P G) (hH : ContinuousInPolicy P H) (hH0 : ∀ σ,IsPolicy σ → H σ≠0) :
    ContinuousInPolicy P (fun σ => G σ/H σ) :=
  policy_binary P G H hG hH (fun z => z.1/z.2) (fun σ hσ => continuousAt_fst.div continuousAt_snd (hH0 σ hσ))
lemma Wn_continuous (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2) (hw : Integrable (w i) (P.F i)) :
    ContinuousInPolicy P (fun σ => Wn P i (w i) (σ i)) :=
  policy_mul P _ _ (policy_const P _) (policy_integral_continuous P i (w i) hw)
lemma Tn_continuous (P : Primitives) (i : Fin 2) (hmean : FiniteMean P) :
    ContinuousInPolicy P (fun σ => Tn P i (σ i)) :=
  policy_add P _ _ (policy_const P 1) (policy_mul P _ _ (policy_const P _) (policy_integral_continuous P i _ (hmean i)))
lemma Qn_continuous (P : Primitives) (i : Fin 2) :
    ContinuousInPolicy P (fun σ => Qn P i (σ i)) :=
  policy_add P _ _ (policy_const P _) (policy_mul P _ _ (policy_const P _) (policy_integral_continuous P i _ (q_integrable P i)))
lemma stateRate_continuous (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2)
    (hw : Integrable (w i) (P.F i)) (hmean : FiniteMean P) :
    ContinuousInPolicy P (fun σ => stateRate P i (w i) (σ i)) :=
  policy_div P _ _ (Wn_continuous P w i hw) (Tn_continuous P i hmean) (fun σ _ => ne_of_gt (Tn_pos P i (σ i)))
lemma mu_continuous (P : Primitives) (i : Fin 2) (hmean : FiniteMean P) :
    ContinuousInPolicy P (fun σ => mu P σ i) := by
  unfold mu
  apply policy_div P
  · exact policy_mul P _ _ (Tn_continuous P i hmean) (Qn_continuous P (other i))
  · exact policy_add P _ _
      (policy_mul P _ _ (Tn_continuous P (other i) hmean) (Qn_continuous P i))
      (policy_mul P _ _ (Tn_continuous P i hmean) (Qn_continuous P (other i)))
  · intro σ _
    exact ne_of_gt (add_pos (mul_pos (Tn_pos P (other i) _) (Qn_pos P i _)) (mul_pos (Tn_pos P i _) (Qn_pos P (other i) _)))
lemma reward_continuous (P : Primitives) (w : Fin 2 → ℝ → ℝ)
    (hw : ∀ i,Integrable (w i) (P.F i)) (hmean : FiniteMean P) :
    ContinuousInPolicy P (rewardCF P w) := by
  have hr : rewardCF P w = fun σ => mu P σ 0*stateRate P 0 (w 0) (σ 0)+mu P σ 1*stateRate P 1 (w 1) (σ 1) := by
    funext σ
    exact Fin.sum_univ_two _
  rw [hr]
  exact policy_add P _ _
    (policy_mul P _ _ (mu_continuous P 0 hmean) (stateRate_continuous P w 0 (hw 0) hmean))
    (policy_mul P _ _ (mu_continuous P 1 hmean) (stateRate_continuous P w 1 (hw 1) hmean))
lemma payment_integrable (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2)
    (hw : IntegrableOn (w i) (Ioi 0) (P.F i)) : Integrable (w i) (P.F i) := by
  have hae : ∀ᵐ x ∂P.F i,x ∈ Ioi (0:ℝ) := by
    rw [ae_iff]
    have he : {a : ℝ | a ∉ Ioi 0}=Iic 0 := by ext x; simp
    rw [he]
    exact P.support i
  have hr := Measure.restrict_eq_self_of_ae_mem hae
  simpa only [IntegrableOn,hr] using hw
lemma policy_sub (P : Primitives) (G H : (Fin 2 → Set ℝ) → ℝ)
    (hG : ContinuousInPolicy P G) (hH : ContinuousInPolicy P H) :
    ContinuousInPolicy P (fun σ => G σ-H σ) :=
  policy_binary P G H hG hH (fun z => z.1-z.2) (fun _ _ => by fun_prop)
lemma rFun_continuous_policy (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2) (u : ℝ)
    (hw : ∀ k,Integrable (w k) (P.F k)) (hmean : FiniteMean P) :
    ContinuousInPolicy P (fun σ => rFun P w σ i u) := by
  have hRi := stateRate_continuous P w i (hw i) hmean
  have hRj := stateRate_continuous P w (other i) (hw (other i)) hmean
  have hQi := policy_div P _ _ (Qn_continuous P i) (Tn_continuous P i hmean) (fun σ _ => ne_of_gt (Tn_pos P i (σ i)))
  have hQj := policy_div P _ _ (Qn_continuous P (other i)) (Tn_continuous P (other i) hmean) (fun σ _ => ne_of_gt (Tn_pos P (other i) (σ (other i))))
  unfold rFun
  exact policy_sub P _ _
    (policy_add P _ _
      (policy_mul P _ _ (policy_const P _) (policy_sub P _ _ hRj hRi))
      (policy_mul P _ _ (policy_const P _) (policy_add P _ _ hQi hQj)))
    (policy_add P _ _ (policy_mul P _ _ hQi hRj) (policy_mul P _ _ hQj hRi))
end Queelius.DriverMarginal

namespace Queelius.DriverMarginal
open DriverSurge.IC
lemma union_difference_integral (μ : Measure ℝ) (g : ℝ → ℝ) (hg : Integrable g μ)
    (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (∫ x in s∪t,g x ∂μ)-(∫ x in s\t,g x ∂μ)=∫ x in t,g x ∂μ := by
  classical
  rw [← integral_indicator (hs.union ht),← integral_indicator (hs.diff ht),← integral_indicator ht]
  rw [← integral_sub (hg.indicator (hs.union ht)) (hg.indicator (hs.diff ht))]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  by_cases hxs : x∈s <;> by_cases hxt : x∈t <;> simp [hxs,hxt]
lemma interval_swap (μ : Measure ℝ) [NullSingletonClass μ] (g : ℝ → ℝ) (hg : Integrable g μ)
    (s : Set ℝ) (hs : MeasurableSet s) (u v : ℝ) :
    (∫ x in s∪Ioo u v,g x ∂μ)-(∫ x in s\Icc u v,g x ∂μ)=∫ x in Ioo u v,g x ∂μ := by
  have he : (s \ Icc u v : Set ℝ) =ᵐ[μ] (s \ Ioo u v : Set ℝ) := by
    filter_upwards [Ioo_ae_eq_Icc (μ := μ) (a := u) (b := v)] with x hx
    change (x ∈ Ioo u v) = (x ∈ Icc u v) at hx
    change (x ∈ s ∧ x ∉ Icc u v) = (x ∈ s ∧ x ∉ Ioo u v)
    rw [hx]
  rw [setIntegral_congr_set (f := g) he]
  exact union_difference_integral μ g hg s (Ioo u v) hs measurableSet_Ioo
lemma density_integral (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (i : Fin 2) (g : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    (∫ x in s,g x ∂P.F i)=∫ x in s,f i x*g x := by
  rw [(hf i).2.2]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (show AEMeasurable (fun x => ENNReal.ofReal (f i x)) (volume.restrict s) from (ENNReal.measurable_ofReal.comp (hf i).1).aemeasurable)
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) g hs]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  obtain ⟨B,hB⟩ := (hf i).2.1
  simp only [ENNReal.toReal_ofReal (hB x).1,smul_eq_mul]
lemma density_integrable (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (i : Fin 2) (g : ℝ → ℝ) (hg : Integrable g (P.F i)) : Integrable (fun x => f i x*g x) volume := by
  rw [(hf i).2.2] at hg
  have hh := (integrable_withDensity_iff_integrable_smul' (ENNReal.measurable_ofReal.comp (hf i).1)
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))).mp hg
  obtain ⟨B,hB⟩ := (hf i).2.1
  simpa only [Function.comp_apply,ENNReal.toReal_ofReal (hB _).1,smul_eq_mul] using hh
lemma density_noAtoms (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f) (i : Fin 2) :
    NullSingletonClass (P.F i) := by
  rw [(hf i).2.2]
  infer_instance
lemma short_integral_limit (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (i : Fin 2) (g : ℝ → ℝ) (hg : Integrable g (P.F i)) (u : ℝ)
    (hfu : ContinuousAt (f i) u) (hgu : ContinuousAt g u) :
    Tendsto (fun h => (∫ x in Ioo u (u+h),g x ∂P.F i)/h) (𝓝[>] 0) (𝓝 (f i u*g u)) := by
  have hgf := density_integrable P f hf i g hg
  have hd := intervalIntegral.integral_hasDerivAt_right (a := u) (b := u)
    (IntervalIntegrable.refl : IntervalIntegrable (fun x => f i x*g x) volume u u)
    hgf.aestronglyMeasurable.stronglyMeasurableAtFilter (hfu.mul hgu)
  have ht := hd.tendsto_slope_zero_right
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : u ≤ u+h := by linarith [show (0:ℝ) < h from hh]
  rw [density_integral P f hf i g _ measurableSet_Ioo,intervalIntegral.integral_same,sub_zero]
  rw [intervalIntegral.integral_of_le hp]
  rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := u) (b := u+h))]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]
lemma set_integral_marginal (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (i : Fin 2) (g : ℝ → ℝ) (hg : Integrable g (P.F i)) (s : Set ℝ) (hs : MeasurableSet s)
    (u : ℝ) (hfu : ContinuousAt (f i) u) (hgu : ContinuousAt g u) :
    HasMarginalGain (fun t => ∫ x in t,g x ∂P.F i) s u (f i u*g u) := by
  letI := density_noAtoms P f hf i
  unfold HasMarginalGain
  simpa only [interval_swap (P.F i) g hg s hs] using short_integral_limit P f hf i g hg u hfu hgu
end Queelius.DriverMarginal

namespace Queelius.DriverMarginal
open DriverSurge.IC
lemma ratio_secant_limit (Ap Am Bp Bm : ℝ → ℝ) (A B da db : ℝ)
    (hAm : Tendsto Am (𝓝[>] 0) (𝓝 A)) (hBp : Tendsto Bp (𝓝[>] 0) (𝓝 B))
    (hBm : Tendsto Bm (𝓝[>] 0) (𝓝 B)) (hB : B≠0)
    (hda : Tendsto (fun h => (Ap h-Am h)/h) (𝓝[>] 0) (𝓝 da))
    (hdb : Tendsto (fun h => (Bp h-Bm h)/h) (𝓝[>] 0) (𝓝 db)) :
    Tendsto (fun h => (Ap h/Bp h-Am h/Bm h)/h) (𝓝[>] 0) (𝓝 ((da*B-A*db)/B^2)) := by
  have ht := ((hda.mul hBm).sub (hAm.mul hdb)).div (hBp.mul hBm) (mul_ne_zero hB hB)
  rw [← pow_two] at ht
  apply ht.congr'
  filter_upwards [hBp.eventually_ne hB,hBm.eventually_ne hB,self_mem_nhdsWithin] with h hp hm hh
  have hh0 : h≠0 := ne_of_gt hh
  dsimp
  field_simp
  <;> ring
lemma marginal_factor_algebra (Wi Wj Ti Tj Qi Qj lam f qu wu u : ℝ)
    (hTi : Ti≠0) (hTj : Tj≠0) (hu : u≠0) (hD : Qi*Tj+Qj*Ti≠0) :
    (((Qj*(lam*f*wu)+Wj*(lam*f*qu))*(Qi*Tj+Qj*Ti) -
      (Qj*Wi+Qi*Wj)*(Tj*(lam*f*qu)+Qj*(lam*f*u))) / (Qi*Tj+Qj*Ti)^2) =
    lam*f*u*Qj*Ti*Tj/(Qi*Tj+Qj*Ti)^2 *
      (qu/u*(Wj/Tj-Wi/Ti)+wu/u*(Qi/Ti+Qj/Tj)-(Qi/Ti*(Wj/Tj)+Qj/Tj*(Wi/Ti))) := by
  field_simp
  <;> ring
lemma rewardOn_quotient (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2) (s : Set ℝ) :
    rewardOn P w σ i s =
      (Qn P (other i) (σ (other i))*Wn P i (w i) s+Qn P i s*Wn P (other i) (w (other i)) (σ (other i))) /
      (Qn P i s*Tn P (other i) (σ (other i))+Qn P (other i) (σ (other i))*Tn P i s) := by
  unfold rewardOn
  rw [reward_quotient P w _ i]
  simp only [Function.update_self,Function.update_of_ne (other_ne i)]
  congr 1
  ring
end Queelius.DriverMarginal

namespace Queelius.DriverMarginal
open DriverSurge.IC
lemma interval_excludes (u x : ℝ) (hx : x≠u) : ∀ᶠ h : ℝ in 𝓝 0,x ∉ Icc u (u+h) := by
  rcases lt_or_gt_of_ne hx with hxu | hux
  · exact Eventually.of_forall (fun h hxmem => (not_le.mpr hxu) hxmem.1)
  · have hh : ∀ᶠ h : ℝ in 𝓝 0,h < x-u := eventually_lt_nhds (by linarith)
    filter_upwards [hh] with h hh
    intro hmem
    have := hmem.2
    linarith
lemma integral_set_convergence (μ : Measure ℝ) [NullSingletonClass μ] (g : ℝ → ℝ) (hg : Integrable g μ)
    (s : Set ℝ) (hs : MeasurableSet s) (U : ℝ → Set ℝ) (hU : ∀ h,MeasurableSet (U h)) (u : ℝ)
    (hpoint : ∀ x,x≠u → ∀ᶠ h : ℝ in 𝓝 0,x∈U h ↔ x∈s) :
    Tendsto (fun h => ∫ x in U h,g x ∂μ) (𝓝 0) (𝓝 (∫ x in s,g x ∂μ)) := by
  have hae : ∀ᵐ x ∂μ,x≠u := by simpa [ae_iff] using (measure_singleton u : μ {u}=0)
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 (0:ℝ)) (F := fun h => (U h).indicator g)
    (f := s.indicator g) (fun x => ‖g x‖)
    (Eventually.of_forall (fun h => hg.aestronglyMeasurable.indicator (hU h)))
    (Eventually.of_forall (fun h => ae_of_all _ (fun x => norm_indicator_le_norm_self _ _))) hg.norm ?_
  · simp_rw [integral_indicator (hU _),integral_indicator hs] at ht
    exact ht
  · filter_upwards [hae] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hpoint x hx] with h hh
    by_cases hxs : x ∈ s
    · have hxu := hh.mpr hxs
      simp [hxs,hxu]
    · have hxu : x ∉ U h := fun hmem => hxs (hh.mp hmem)
      simp [hxs,hxu]
lemma perturbed_integral_limits (μ : Measure ℝ) [NullSingletonClass μ] (g : ℝ → ℝ) (hg : Integrable g μ)
    (s : Set ℝ) (hs : MeasurableSet s) (u : ℝ) :
    Tendsto (fun h => ∫ x in s∪Ioo u (u+h),g x ∂μ) (𝓝 0) (𝓝 (∫ x in s,g x ∂μ)) ∧
    Tendsto (fun h => ∫ x in s\Icc u (u+h),g x ∂μ) (𝓝 0) (𝓝 (∫ x in s,g x ∂μ)) := by
  constructor
  · apply integral_set_convergence μ g hg s hs _ (fun h => hs.union measurableSet_Ioo) u
    intro x hx
    filter_upwards [interval_excludes u x hx] with h hh
    have hn : x ∉ Ioo u (u+h) := fun hi => hh ⟨hi.1.le,hi.2.le⟩
    simp [hn]
  · apply integral_set_convergence μ g hg s hs _ (fun h => hs.diff measurableSet_Icc) u
    intro x hx
    filter_upwards [interval_excludes u x hx] with h hh
    simp [hh]
end Queelius.DriverMarginal

namespace Queelius.DriverMarginal
open DriverSurge.IC
lemma integral_affine_marginal (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (i : Fin 2) (g : ℝ → ℝ) (hg : Integrable g (P.F i)) (s : Set ℝ) (hs : MeasurableSet s)
    (u : ℝ) (hfu : ContinuousAt (f i) u) (hgu : ContinuousAt g u) (a b : ℝ) :
    HasMarginalGain (fun t => a+b*∫ x in t,g x ∂P.F i) s u (b*(f i u*g u)) := by
  have ht := (set_integral_marginal P f hf i g hg s hs u hfu hgu).const_mul b
  apply ht.congr'
  exact Eventually.of_forall (fun h => by dsimp;ring)
lemma linear_secant_limit (Xp Xm Yp Ym : ℝ → ℝ) (dx dy a b : ℝ)
    (hX : Tendsto (fun h => (Xp h-Xm h)/h) (𝓝[>] 0) (𝓝 dx))
    (hY : Tendsto (fun h => (Yp h-Ym h)/h) (𝓝[>] 0) (𝓝 dy)) :
    Tendsto (fun h => ((a*Xp h+b*Yp h)-(a*Xm h+b*Ym h))/h)
      (𝓝[>] 0) (𝓝 (a*dx+b*dy)) := by
  apply ((hX.const_mul a).add (hY.const_mul b)).congr'
  exact Eventually.of_forall (fun h => by dsimp;ring)
lemma fraction_three_marginal (X Y Z : Set ℝ → ℝ) (s : Set ℝ) (u a b c d dx dy dz : ℝ)
    (hX : HasMarginalGain X s u dx) (hY : HasMarginalGain Y s u dy) (hZ : HasMarginalGain Z s u dz)
    (hXm : Tendsto (fun h => X (s\Icc u (u+h))) (𝓝[>] 0) (𝓝 (X s)))
    (hYp : Tendsto (fun h => Y (s∪Ioo u (u+h))) (𝓝[>] 0) (𝓝 (Y s)))
    (hYm : Tendsto (fun h => Y (s\Icc u (u+h))) (𝓝[>] 0) (𝓝 (Y s)))
    (hZp : Tendsto (fun h => Z (s∪Ioo u (u+h))) (𝓝[>] 0) (𝓝 (Z s)))
    (hZm : Tendsto (fun h => Z (s\Icc u (u+h))) (𝓝[>] 0) (𝓝 (Z s)))
    (hden : c*Y s+d*Z s≠0) :
    HasMarginalGain (fun t => (a*X t+b*Y t)/(c*Y t+d*Z t)) s u
      (((a*dx+b*dy)*(c*Y s+d*Z s)-(a*X s+b*Y s)*(c*dy+d*dz))/(c*Y s+d*Z s)^2) := by
  unfold HasMarginalGain at *
  apply ratio_secant_limit
  · exact (hXm.const_mul a).add (hYm.const_mul b)
  · exact (hYp.const_mul c).add (hZp.const_mul d)
  · exact (hYm.const_mul c).add (hZm.const_mul d)
  · exact hden
  · exact linear_secant_limit _ _ _ _ dx dy a b hX hY
  · exact linear_secant_limit _ _ _ _ dy dz c d hY hZ
end Queelius.DriverMarginal

namespace Queelius.DriverMarginal
open DriverSurge.IC
/-- Conditional analytic version: global payment integrability and finite means are explicit.
This does not prove the platform lemma with only integrability on the initial policy. -/
lemma reward_marginal_integrable (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hw : ∀ k,Integrable (w k) (P.F k)) (hmean : FiniteMean P)
    (i : Fin 2) (u : ℝ) (hu : 0 < u) (hfu : ContinuousAt (f i) u) (hwu : ContinuousAt (w i) u) :
    HasMarginalGain (rewardOn P w σ i) (σ i) u
      (P.lam i*f i u*u*Qn P (other i) (σ (other i))*Tn P i (σ i)*Tn P (other i) (σ (other i)) /
        (Qn P i (σ i)*Tn P (other i) (σ (other i))+Qn P (other i) (σ (other i))*Tn P i (σ i))^2*rFun P w σ i u) := by
  letI := density_noAtoms P f hf i
  let X := Wn P i (w i)
  let Y := Qn P i
  let Z := Tn P i
  have hX : HasMarginalGain X (σ i) u (P.lam i*(f i u*w i u)) := by
    change HasMarginalGain (fun t => P.lam i*∫ x in t,w i x ∂P.F i) (σ i) u (P.lam i*(f i u*w i u))
    simpa only [zero_add] using integral_affine_marginal P f hf i (w i) (hw i) (σ i) (hσ i).1.measurableSet u hfu hwu 0 (P.lam i)
  have hY : HasMarginalGain Y (σ i) u (P.lam i*(f i u*q P i u)) := by
    exact integral_affine_marginal P f hf i (q P i) (q_integrable P i) (σ i) (hσ i).1.measurableSet u hfu (q_continuous P i).continuousAt (P.sw i) (P.lam i)
  have hZ : HasMarginalGain Z (σ i) u (P.lam i*(f i u*u)) := by
    exact integral_affine_marginal P f hf i id (hmean i) (σ i) (hσ i).1.measurableSet u hfu continuousAt_id 1 (P.lam i)
  have hW := perturbed_integral_limits (P.F i) (w i) (hw i) (σ i) (hσ i).1.measurableSet u
  have hQ := perturbed_integral_limits (P.F i) (q P i) (q_integrable P i) (σ i) (hσ i).1.measurableSet u
  have hT := perturbed_integral_limits (P.F i) id (hmean i) (σ i) (hσ i).1.measurableSet u
  have hXm : Tendsto (fun h => X (σ i\Icc u (u+h))) (𝓝[>] 0) (𝓝 (X (σ i))) :=
    tendsto_const_nhds.mul (hW.2.mono_left nhdsWithin_le_nhds)
  have hYp : Tendsto (fun h => Y (σ i∪Ioo u (u+h))) (𝓝[>] 0) (𝓝 (Y (σ i))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (hQ.1.mono_left nhdsWithin_le_nhds))
  have hYm : Tendsto (fun h => Y (σ i\Icc u (u+h))) (𝓝[>] 0) (𝓝 (Y (σ i))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (hQ.2.mono_left nhdsWithin_le_nhds))
  have hZp : Tendsto (fun h => Z (σ i∪Ioo u (u+h))) (𝓝[>] 0) (𝓝 (Z (σ i))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (hT.1.mono_left nhdsWithin_le_nhds))
  have hZm : Tendsto (fun h => Z (σ i\Icc u (u+h))) (𝓝[>] 0) (𝓝 (Z (σ i))) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (hT.2.mono_left nhdsWithin_le_nhds))
  let a := Qn P (other i) (σ (other i))
  let b := Wn P (other i) (w (other i)) (σ (other i))
  let c := Tn P (other i) (σ (other i))
  have hden : c*Y (σ i)+a*Z (σ i)≠0 := ne_of_gt (add_pos (mul_pos (Tn_pos P (other i) _) (Qn_pos P i _)) (mul_pos (Qn_pos P (other i) _) (Tn_pos P i _)))
  have ht := fraction_three_marginal X Y Z (σ i) u a b c a _ _ _ hX hY hZ hXm hYp hYm hZp hZm hden
  have he : rewardOn P w σ i = fun t => (a*X t+b*Y t)/(c*Y t+a*Z t) := by
    funext t
    rw [rewardOn_quotient P w σ i t]
    dsimp [a,b,c,X,Y,Z]
    congr 1 <;> ring
  rw [he]
  have hc := marginal_factor_algebra (X (σ i)) b (Z (σ i)) c (Y (σ i)) a (P.lam i) (f i u) (q P i u) (w i u) u
    (ne_of_gt (Tn_pos P i _)) (ne_of_gt (Tn_pos P (other i) _)) (ne_of_gt hu)
    (ne_of_gt (denominator_pos P σ i))
  unfold rFun stateRate
  dsimp [a,b,c,X,Y,Z] at ht hc ⊢
  rw [← hc]
  simpa only [mul_assoc,mul_comm,mul_left_comm,add_comm,add_left_comm,add_assoc] using ht
end Queelius.DriverMarginal

namespace Queelius.DriverMarginal
open DriverSurge.IC
lemma bounded_interval_mass (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f) (i : Fin 2) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ u h : ℝ,0 < h → (P.F i).real (Ioo u (u+h)) ≤ B*h := by
  letI : IsProbabilityMeasure (P.F i) := P.prob i
  obtain ⟨B,hB⟩ := (hf i).2.1
  refine ⟨B,(hB 0).1.trans (hB 0).2,?_⟩
  have hfi : Integrable (f i) volume := by
    simpa using density_integrable P f hf i (fun _ => (1:ℝ)) (integrable_const 1)
  intro u h hh
  have hc : IntegrableOn (fun _ : ℝ => B) (Ioo u (u+h)) volume :=
    integrableOn_const (by rw [Real.volume_Ioo];exact ENNReal.ofReal_ne_top)
  have hm : (P.F i).real (Ioo u (u+h)) = ∫ x in Ioo u (u+h),f i x := by
    have he := density_integral P f hf i (fun _ => (1:ℝ)) (Ioo u (u+h)) measurableSet_Ioo
    simpa using he
  rw [hm]
  calc
    _ ≤ ∫ x in Ioo u (u+h),B := setIntegral_mono_on hfi.integrableOn hc measurableSet_Ioo (fun x _ => (hB x).2)
    _ = B*h := by simp [Measure.real,Real.volume_Ioo,hh.le,mul_comm]
lemma weighted_short_error (μ : Measure ℝ) [IsFiniteMeasure μ] (g : ℝ → ℝ) (hg : Integrable g μ)
    (u B : ℝ) (hB : 0 ≤ B) (hmass : ∀ h : ℝ,0 < h → μ.real (Ioo u (u+h)) ≤ B*h)
    (hgu : ContinuousAt g u) :
    Tendsto (fun h => (∫ x in Ioo u (u+h),g x ∂μ)/h-g u*(μ.real (Ioo u (u+h))/h))
      (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε/(B+1)
  have hB1 : 0 < B+1 := by linarith
  have hη : 0 < η := div_pos hε hB1
  obtain ⟨δ,hδ,hcont⟩ := Metric.continuousAt_iff.mp hgu η hη
  have hhδ : ∀ᶠ h : ℝ in 𝓝[>] 0,h < δ := (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [hhδ,self_mem_nhdsWithin] with h hhδ (hh : 0 < h)
  have hbnd : ∀ x ∈ Ioo u (u+h),‖g x-g u‖ ≤ η := by
    intro x hx
    have hd : dist x u < δ := by rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hx.1)];linarith [hx.2]
    simpa only [Real.dist_eq,Real.norm_eq_abs] using (hcont hd).le
  have he : (∫ x in Ioo u (u+h),g x-g u ∂μ) = (∫ x in Ioo u (u+h),g x ∂μ)-g u*μ.real (Ioo u (u+h)) := by
    rw [integral_sub hg.integrableOn (integrable_const _),integral_const]
    simp [Measure.real,mul_comm]
  have hn := norm_setIntegral_le_of_norm_le_const (measure_lt_top μ _) hbnd
  rw [Real.norm_eq_abs,he] at hn
  have herr : (∫ x in Ioo u (u+h),g x ∂μ)/h-g u*(μ.real (Ioo u (u+h))/h) =
      ((∫ x in Ioo u (u+h),g x ∂μ)-g u*μ.real (Ioo u (u+h)))/h := by ring
  rw [Real.dist_eq,sub_zero,herr,abs_div,abs_of_pos hh]
  have hsmall : η*B < ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hB1).mpr
    nlinarith
  calc
    _ ≤ (η*μ.real (Ioo u (u+h)))/h := div_le_div_of_nonneg_right hn hh.le
    _ ≤ η*B := (div_le_iff₀ hh).mpr (by nlinarith [hmass h hh])
    _ < ε := hsmall
lemma density_weighted_error (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (i : Fin 2) (g : ℝ → ℝ) (hg : Integrable g (P.F i)) (u : ℝ) (hgu : ContinuousAt g u) :
    Tendsto (fun h => (∫ x in Ioo u (u+h),g x ∂P.F i)/h-g u*((P.F i).real (Ioo u (u+h))/h))
      (𝓝[>] 0) (𝓝 0) := by
  letI : IsProbabilityMeasure (P.F i) := P.prob i
  obtain ⟨B,hB,hbound⟩ := bounded_interval_mass P f hf i
  exact weighted_short_error (P.F i) g hg u B hB (hbound u) hgu
end Queelius.DriverMarginal

namespace Queelius.DriverMarginal
open DriverSurge.IC
lemma bounded_factor_zero (r e : ℝ → ℝ) (K : ℝ)
    (hb : ∀ᶠ h in 𝓝[>] 0,‖r h‖ ≤ K) (he : Tendsto e (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h => r h*e h) (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun h => K*‖e h‖)
  · filter_upwards [hb] with h hh
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
  · simpa using tendsto_const_nhds.mul he.norm
lemma ratio_common_driver (Ap Am Bp Bm r : ℝ → ℝ) (A B da db K : ℝ)
    (hAm : Tendsto Am (𝓝[>] 0) (𝓝 A)) (hBp : Tendsto Bp (𝓝[>] 0) (𝓝 B))
    (hBm : Tendsto Bm (𝓝[>] 0) (𝓝 B)) (hB : B≠0)
    (hb : ∀ᶠ h in 𝓝[>] 0,‖r h‖ ≤ K)
    (hda : Tendsto (fun h => (Ap h-Am h)/h-da*r h) (𝓝[>] 0) (𝓝 0))
    (hdb : Tendsto (fun h => (Bp h-Bm h)/h-db*r h) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h => (Ap h/Bp h-Am h/Bm h)/h-((da*B-A*db)/B^2)*r h)
      (𝓝[>] 0) (𝓝 0) := by
  let C := fun h => (da*Bm h-Am h*db)/(Bp h*Bm h)
  let C0 := (da*B-A*db)/(B*B)
  have hc : Tendsto C (𝓝[>] 0) (𝓝 C0) :=
    ((tendsto_const_nhds.mul hBm).sub (hAm.mul tendsto_const_nhds)).div (hBp.mul hBm) (mul_ne_zero hB hB)
  have hce : Tendsto (fun h => C h-C0) (𝓝[>] 0) (𝓝 0) := by simpa only [sub_self] using hc.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => C0) (𝓝[>] 0) (𝓝 C0))
  have hm := bounded_factor_zero r (fun h => C h-C0) K hb hce
  have he := ((hda.mul hBm).sub (hAm.mul hdb)).div (hBp.mul hBm) (mul_ne_zero hB hB)
  have he0 : Tendsto (fun h => (((Ap h-Am h)/h-da*r h)*Bm h-Am h*((Bp h-Bm h)/h-db*r h))/(Bp h*Bm h))
      (𝓝[>] 0) (𝓝 0)  := by
    convert he using 1 <;> first | rfl | simp
  have hsum : Tendsto (fun h => (((Ap h-Am h)/h-da*r h)*Bm h-Am h*((Bp h-Bm h)/h-db*r h))/(Bp h*Bm h)+r h*(C h-C0)) (𝓝[>] 0) (𝓝 0) := by simpa using he0.add hm
  apply hsum.congr'
  filter_upwards [hBp.eventually_ne hB,hBm.eventually_ne hB,self_mem_nhdsWithin] with h hp hm (hh : 0 < h)
  have hh0 : h≠0 := ne_of_gt hh
  dsimp [C,C0]
  field_simp
  <;> ring
lemma linear_common_driver (Xp Xm Yp Ym r : ℝ → ℝ) (dx dy a b : ℝ)
    (hX : Tendsto (fun h => (Xp h-Xm h)/h-dx*r h) (𝓝[>] 0) (𝓝 0))
    (hY : Tendsto (fun h => (Yp h-Ym h)/h-dy*r h) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h => ((a*Xp h+b*Yp h)-(a*Xm h+b*Ym h))/h-(a*dx+b*dy)*r h)
      (𝓝[>] 0) (𝓝 0) := by
  have ht := (hX.const_mul a).add (hY.const_mul b)
  have ht0 : Tendsto (fun h => a*((Xp h-Xm h)/h-dx*r h)+b*((Yp h-Ym h)/h-dy*r h)) (𝓝[>] 0) (𝓝 0) := by simpa using ht
  apply ht0.congr'
  exact Eventually.of_forall (fun h => by dsimp;ring)
lemma affine_integral_error (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (i : Fin 2) (g : ℝ → ℝ) (hg : Integrable g (P.F i)) (s : Set ℝ) (hs : MeasurableSet s)
    (u : ℝ) (hgu : ContinuousAt g u) (a b : ℝ) :
    Tendsto (fun h => ((a+b*∫ x in s∪Ioo u (u+h),g x ∂P.F i)-(a+b*∫ x in s\Icc u (u+h),g x ∂P.F i))/h-
      (b*g u)*((P.F i).real (Ioo u (u+h))/h)) (𝓝[>] 0) (𝓝 0) := by
  letI := density_noAtoms P f hf i
  have ht := (density_weighted_error P f hf i g hg u hgu).const_mul b
  have ht0 : Tendsto (fun h => b*((∫ x in Ioo u (u+h),g x ∂P.F i)/h-g u*((P.F i).real (Ioo u (u+h))/h))) (𝓝[>] 0) (𝓝 0) := by simpa using ht
  apply ht0.congr'
  apply Eventually.of_forall
  intro h
  dsimp only
  rw [show (a+b*∫ x in s∪Ioo u (u+h),g x ∂P.F i)-(a+b*∫ x in s\Icc u (u+h),g x ∂P.F i)=
      b*((∫ x in s∪Ioo u (u+h),g x ∂P.F i)-(∫ x in s\Icc u (u+h),g x ∂P.F i)) by ring,
    interval_swap (P.F i) g hg s hs]
  ring
end Queelius.DriverMarginal

namespace Queelius.DriverMarginal
open DriverSurge.IC
noncomputable def gainCoefficient (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2) (u : ℝ) : ℝ :=
  P.lam i*u*Qn P (other i) (σ (other i))*Tn P i (σ i)*Tn P (other i) (σ (other i)) /
    (Qn P i (σ i)*Tn P (other i) (σ (other i))+Qn P (other i) (σ (other i))*Tn P i (σ i))^2*rFun P w σ i u
lemma reward_common_error (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (hσ : IsPolicy σ)
    (hw : ∀ k,Integrable (w k) (P.F k)) (hmean : FiniteMean P)
    (i : Fin 2) (u : ℝ) (hu : 0 < u) (hwu : ContinuousAt (w i) u) :
    Tendsto (fun h => (rewardOn P w σ i (σ i∪Ioo u (u+h))-rewardOn P w σ i (σ i\Icc u (u+h)))/h-
      gainCoefficient P w σ i u*((P.F i).real (Ioo u (u+h))/h)) (𝓝[>] 0) (𝓝 0) := by
  letI : IsProbabilityMeasure (P.F i) := P.prob i
  letI := density_noAtoms P f hf i
  let X := Wn P i (w i)
  let Y := Qn P i
  let Z := Tn P i
  let r := fun h => (P.F i).real (Ioo u (u+h))/h
  have hX : Tendsto (fun h => (X (σ i∪Ioo u (u+h))-X (σ i\Icc u (u+h)))/h-(P.lam i*w i u)*r h) (𝓝[>] 0) (𝓝 0) := by
    simpa only [X,Wn,zero_add,r] using affine_integral_error P f hf i (w i) (hw i) (σ i) (hσ i).1.measurableSet u hwu 0 (P.lam i)
  have hY : Tendsto (fun h => (Y (σ i∪Ioo u (u+h))-Y (σ i\Icc u (u+h)))/h-(P.lam i*q P i u)*r h) (𝓝[>] 0) (𝓝 0) :=
    affine_integral_error P f hf i (q P i) (q_integrable P i) (σ i) (hσ i).1.measurableSet u (q_continuous P i).continuousAt (P.sw i) (P.lam i)
  have hZ : Tendsto (fun h => (Z (σ i∪Ioo u (u+h))-Z (σ i\Icc u (u+h)))/h-(P.lam i*u)*r h) (𝓝[>] 0) (𝓝 0) :=
    affine_integral_error P f hf i id (hmean i) (σ i) (hσ i).1.measurableSet u continuousAt_id 1 (P.lam i)
  have hW := perturbed_integral_limits (P.F i) (w i) (hw i) (σ i) (hσ i).1.measurableSet u
  have hQ := perturbed_integral_limits (P.F i) (q P i) (q_integrable P i) (σ i) (hσ i).1.measurableSet u
  have hT := perturbed_integral_limits (P.F i) id (hmean i) (σ i) (hσ i).1.measurableSet u
  have hXm : Tendsto (fun h => X (σ i\Icc u (u+h))) (𝓝[>] 0) (𝓝 (X (σ i))) := tendsto_const_nhds.mul (hW.2.mono_left nhdsWithin_le_nhds)
  have hYp : Tendsto (fun h => Y (σ i∪Ioo u (u+h))) (𝓝[>] 0) (𝓝 (Y (σ i))) := tendsto_const_nhds.add (tendsto_const_nhds.mul (hQ.1.mono_left nhdsWithin_le_nhds))
  have hYm : Tendsto (fun h => Y (σ i\Icc u (u+h))) (𝓝[>] 0) (𝓝 (Y (σ i))) := tendsto_const_nhds.add (tendsto_const_nhds.mul (hQ.2.mono_left nhdsWithin_le_nhds))
  have hZp : Tendsto (fun h => Z (σ i∪Ioo u (u+h))) (𝓝[>] 0) (𝓝 (Z (σ i))) := tendsto_const_nhds.add (tendsto_const_nhds.mul (hT.1.mono_left nhdsWithin_le_nhds))
  have hZm : Tendsto (fun h => Z (σ i\Icc u (u+h))) (𝓝[>] 0) (𝓝 (Z (σ i))) := tendsto_const_nhds.add (tendsto_const_nhds.mul (hT.2.mono_left nhdsWithin_le_nhds))
  let a := Qn P (other i) (σ (other i))
  let b := Wn P (other i) (w (other i)) (σ (other i))
  let c := Tn P (other i) (σ (other i))
  obtain ⟨K,hK,hbound⟩ := bounded_interval_mass P f hf i
  have hr : ∀ᶠ h in 𝓝[>] 0,‖r h‖ ≤ K := by
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    dsimp [r]
    have hnonneg : 0 ≤ (P.F i).real (Ioo u (u+h))/h := div_nonneg (show 0 ≤ (P.F i).real (Ioo u (u+h)) from ENNReal.toReal_nonneg) hh.le
    rw [abs_of_nonneg hnonneg]
    exact (div_le_iff₀ hh).mpr (hbound u h hh)
  have hden : c*Y (σ i)+a*Z (σ i)≠0 := ne_of_gt (add_pos (mul_pos (Tn_pos P (other i) _) (Qn_pos P i _)) (mul_pos (Qn_pos P (other i) _) (Tn_pos P i _)))
  have ht := ratio_common_driver
    (fun h => a*X (σ i∪Ioo u (u+h))+b*Y (σ i∪Ioo u (u+h)))
    (fun h => a*X (σ i\Icc u (u+h))+b*Y (σ i\Icc u (u+h)))
    (fun h => c*Y (σ i∪Ioo u (u+h))+a*Z (σ i∪Ioo u (u+h)))
    (fun h => c*Y (σ i\Icc u (u+h))+a*Z (σ i\Icc u (u+h))) r
    (a*X (σ i)+b*Y (σ i)) (c*Y (σ i)+a*Z (σ i))
    (a*(P.lam i*w i u)+b*(P.lam i*q P i u)) (c*(P.lam i*q P i u)+a*(P.lam i*u)) K
    ((hXm.const_mul a).add (hYm.const_mul b)) ((hYp.const_mul c).add (hZp.const_mul a))
    ((hYm.const_mul c).add (hZm.const_mul a)) hden hr
    (linear_common_driver _ _ _ _ r _ _ a b hX hY) (linear_common_driver _ _ _ _ r _ _ c a hY hZ)
  have he : rewardOn P w σ i = fun t => (a*X t+b*Y t)/(c*Y t+a*Z t) := by
    funext t
    rw [rewardOn_quotient P w σ i t]
    dsimp [a,b,c,X,Y,Z]
    congr 1 <;> ring
  rw [he]
  have hc := marginal_factor_algebra (X (σ i)) b (Z (σ i)) c (Y (σ i)) a (P.lam i) 1 (q P i u) (w i u) u
    (ne_of_gt (Tn_pos P i _)) (ne_of_gt (Tn_pos P (other i) _)) (ne_of_gt hu) (ne_of_gt (denominator_pos P σ i))
  unfold gainCoefficient rFun stateRate
  dsimp [a,b,c,X,Y,Z,r] at ht hc ⊢
  simp only [mul_one] at hc
  rw [← hc]
  simpa only [mul_assoc,mul_comm,mul_left_comm,add_comm,add_left_comm,add_assoc] using ht
end Queelius.DriverMarginal

namespace Queelius.DriverMarginal
open DriverSurge.IC
lemma policy_congr (P : Primitives) (F G : (Fin 2 → Set ℝ) → ℝ)
    (h : ∀ σ,IsPolicy σ → F σ=G σ) (hG : ContinuousInPolicy P G) : ContinuousInPolicy P F := by
  intro σ hσ ε hε
  obtain ⟨δ,hδ,hδspec⟩ := hG σ hσ ε hε
  refine ⟨δ,hδ,fun τ hτ hd => ?_⟩
  rw [h σ hσ,h τ hτ]
  exact hδspec τ hτ hd
lemma common_driver_policy_continuity (P : Primitives) (C D : (Fin 2 → Set ℝ) → ℝ) (r : ℝ → ℝ)
    (hC : ContinuousInPolicy P C)
    (hD : ∀ σ,IsPolicy σ → Tendsto (fun h => C σ*r h) (𝓝[>] 0) (𝓝 (D σ))) : ContinuousInPolicy P D := by
  classical
  by_cases hex : ∃ σ,IsPolicy σ ∧ C σ≠0
  · obtain ⟨σ,hσ,hc⟩ := hex
    have hr : Tendsto r (𝓝[>] 0) (𝓝 (D σ/C σ)) := by
      have ht := (hD σ hσ).div_const (C σ)
      apply ht.congr'
      exact Eventually.of_forall (fun h => by dsimp;field_simp)
    have heq (τ) (hτ : IsPolicy τ) : D τ=C τ*(D σ/C σ) :=
      tendsto_nhds_unique (hD τ hτ) (tendsto_const_nhds.mul hr)
    exact policy_congr P D _ heq (policy_mul P _ _ hC (policy_const P _))
  · have heq (σ) (hσ : IsPolicy σ) : D σ=0 := by
      have hc : C σ=0 := by by_contra hn;exact hex ⟨σ,hσ,hn⟩
      have ht := hD σ hσ
      simp only [hc,zero_mul] at ht
      exact tendsto_nhds_unique ht tendsto_const_nhds
    exact policy_congr P D _ heq (policy_const P 0)
lemma gainCoefficient_policy (P : Primitives) (w : Fin 2 → ℝ → ℝ) (i : Fin 2) (u : ℝ)
    (hw : ∀ k,Integrable (w k) (P.F k)) (hmean : FiniteMean P) :
    ContinuousInPolicy P (fun σ => gainCoefficient P w σ i u) := by
  have hTi := Tn_continuous P i hmean
  have hTj := Tn_continuous P (other i) hmean
  have hQi := Qn_continuous P i
  have hQj := Qn_continuous P (other i)
  have hnum := policy_mul P _ _ (policy_mul P _ _ (policy_mul P _ _ (policy_const P (P.lam i*u)) hQj) hTi) hTj
  have hden := policy_add P _ _ (policy_mul P _ _ hQi hTj) (policy_mul P _ _ hQj hTi)
  unfold gainCoefficient
  simp only [pow_two]
  apply policy_mul P
  · exact policy_div P _ _ hnum (policy_mul P _ _ hden hden)
      (fun σ _ => mul_ne_zero (ne_of_gt (denominator_pos P σ i)) (ne_of_gt (denominator_pos P σ i)))
  · exact rFun_continuous_policy P w i u hw hmean
lemma gainCoefficient_u (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2)
    (hw : ContinuousOn (w i) (Ioi 0)) : ContinuousOn (gainCoefficient P w σ i) (Ioi 0) := by
  unfold gainCoefficient
  have hc : Continuous (fun u : ℝ => P.lam i*u*Qn P (other i) (σ (other i))*Tn P i (σ i)*Tn P (other i) (σ (other i)) /
    (Qn P i (σ i)*Tn P (other i) (σ (other i))+Qn P (other i) (σ (other i))*Tn P i (σ i))^2) := by fun_prop
  exact hc.continuousOn.mul (rFun_continuous_u P w σ i hw)
end Queelius.DriverMarginal

namespace DriverSurge.IC

open MeasureTheory Set

/-- Remark 1, bullets 1–2 (p. 57; corrected: the continuity of `∂/∂u R(w, σ)` in `u` is claimed when
the densities are continuous on `(0, ∞)`). Let `F_i` have bounded densities and finite means, and let
the payments `w_i` be continuous on `(0, ∞)` and `F_i`-integrable there. Continuity in `σ` is with
respect to `F_1(σ_1 △ σ'_1) + F_2(σ_2 △ σ'_2)` over policies.
1. `R_i(σ)`, `R(σ)` and `µ_i(σ)` are continuous in `σ`;
2. `r(u, i, w, σ)` is continuous in `u > 0` for fixed `σ` and continuous in `σ` for fixed `u`;
3. every marginal gain `∂/∂u R(w, σ)` (with respect to state `i`'s policy) is continuous in `σ` for
   fixed `u > 0`, and, if the densities are continuous on `(0, ∞)`, continuous in `u > 0` for fixed
   `σ`. -/
theorem _root_.solution (P : Primitives) (f : Fin 2 → ℝ → ℝ) (hf : HasBoundedDensity P f)
    (hmean : FiniteMean P) (w : Fin 2 → ℝ → ℝ) (hwc : ∀ k, ContinuousOn (w k) (Ioi 0))
    (hwi : ∀ k, IntegrableOn (w k) (Ioi 0) (P.F k)) (i : Fin 2) :
    ContinuousInPolicy P (fun σ => stateRate P i (w i) (σ i)) ∧
    ContinuousInPolicy P (fun σ => rewardCF P w σ) ∧
    ContinuousInPolicy P (fun σ => mu P σ i) ∧
    (∀ σ, IsPolicy σ → ContinuousOn (rFun P w σ i) (Ioi 0)) ∧
    (∀ u : ℝ, 0 < u → ContinuousInPolicy P (fun σ => rFun P w σ i u)) ∧
    (∀ D : (Fin 2 → Set ℝ) → ℝ → ℝ,
      (∀ σ, IsPolicy σ → ∀ u : ℝ, 0 < u → HasMarginalGain (rewardOn P w σ i) (σ i) u (D σ u)) →
      (∀ u : ℝ, 0 < u → ContinuousInPolicy P (fun σ => D σ u)) ∧
      ((∀ k, ContinuousOn (f k) (Ioi 0)) → ∀ σ, IsPolicy σ → ContinuousOn (D σ) (Ioi 0))) := by
  have hglobal (k) := Queelius.DriverMarginal.payment_integrable P w k (hwi k)
  refine ⟨Queelius.DriverMarginal.stateRate_continuous P w i (hglobal i) hmean,
    Queelius.DriverMarginal.reward_continuous P w hglobal hmean,
    Queelius.DriverMarginal.mu_continuous P i hmean,
    (fun σ _ => Queelius.DriverMarginal.rFun_continuous_u P w σ i (hwc i)),
    (fun u _ => Queelius.DriverMarginal.rFun_continuous_policy P w i u hglobal hmean),?_⟩
  intro D hD
  constructor
  · intro u hu
    apply Queelius.DriverMarginal.common_driver_policy_continuity P
      (fun σ => Queelius.DriverMarginal.gainCoefficient P w σ i u) (fun σ => D σ u)
      (fun h => (P.F i).real (Ioo u (u+h))/h)
      (Queelius.DriverMarginal.gainCoefficient_policy P w i u hglobal hmean)
    intro σ hσ
    have herr := Queelius.DriverMarginal.reward_common_error P f hf w σ hσ hglobal hmean i u hu
      ((hwc i).continuousAt (isOpen_Ioi.mem_nhds hu))
    have hd := hD σ hσ u hu
    unfold HasMarginalGain at hd
    have ht := hd.sub herr
    have ht0 : Filter.Tendsto (fun h =>
        (rewardOn P w σ i (σ i∪Ioo u (u+h))-rewardOn P w σ i (σ i\Icc u (u+h)))/h -
        ((rewardOn P w σ i (σ i∪Ioo u (u+h))-rewardOn P w σ i (σ i\Icc u (u+h)))/h -
          Queelius.DriverMarginal.gainCoefficient P w σ i u*((P.F i).real (Ioo u (u+h))/h)))
        (nhdsWithin 0 (Ioi 0)) (nhds (D σ u)) := by simpa using ht
    apply ht0.congr'
    exact Filter.Eventually.of_forall (fun h => by dsimp;ring)
  · intro hfc σ hσ
    have heq (u : ℝ) (hu : u ∈ Ioi (0:ℝ)) : D σ u=f i u*Queelius.DriverMarginal.gainCoefficient P w σ i u := by
      have hformula := Queelius.DriverMarginal.reward_marginal_integrable P f hf w σ hσ hglobal hmean i u hu
        ((hfc i).continuousAt (isOpen_Ioi.mem_nhds hu)) ((hwc i).continuousAt (isOpen_Ioi.mem_nhds hu))
      have hh := tendsto_nhds_unique (hD σ hσ u hu) hformula
      rw [hh]
      unfold Queelius.DriverMarginal.gainCoefficient
      ring
    exact ((hfc i).mul (Queelius.DriverMarginal.gainCoefficient_u P w σ i (hwc i))).congr heq


end DriverSurge.IC

namespace Queelius.DriverMarginal
open DriverSurge.IC
lemma atomic_endpoint_control (u h : ℝ) (hh : 0 < h) :
    (∫ x in Ioo u (u+h),(1:ℝ) ∂Measure.dirac u)=0 ∧
    (∫ x in Icc u (u+h),(1:ℝ) ∂Measure.dirac u)=1 := by
  constructor <;> simp [Measure.real,Measure.dirac_apply,hh.le]
lemma zero_gain_control (P : Primitives) (σ : Fin 2 → Set ℝ) (i : Fin 2) (u : ℝ) :
    gainCoefficient P (fun _ _ => 0) σ i u=0 := by
  simp [gainCoefficient,rFun,stateRate,Wn]
end Queelius.DriverMarginal
