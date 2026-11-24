-- Prove2me | solution 1 for BroughanRH.jensen
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:01:31.11564+00:00
-- url     : https://prove2.me/submissions/1eb81529-21a8-4063-a429-085ed2caa6db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_XiPairingPublished_concrete_upper_paired_product
import Theorems.Thm_BranchActualCount_concrete_zero_count_bounds

open Filter Topology Complex

namespace JensenAux

lemma li_iter {ι : Type*} {φ : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {W : Set ℂ}
    (hW : IsOpen W) (hF : ∀ i, DifferentiableOn ℂ (F i) W)
    (h : TendstoLocallyUniformlyOn F f φ W) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv k (F i)) (iteratedDeriv k f) φ W ∧
    ∀ i, DifferentiableOn ℂ (iteratedDeriv k (F i)) W := by
  induction k with
  | zero => simpa using ⟨h, hF⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, fun i => ?_⟩
    · simp only [iteratedDeriv_succ]
      exact h1.deriv (Eventually.of_forall h2) hW
    · rw [iteratedDeriv_succ]; exact (h2 i).deriv hW

noncomputable def xiL (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

noncomputable def FL (z : ℂ) : ℂ :=
  ((z + 1/2) * ((z + 1/2) - 1) * completedRiemannZeta₀ (z + 1/2) + 1) / 2

lemma FL_eq (z : ℂ) : FL z = xiL (z + 1/2) := by unfold FL xiL; ring

lemma xiL_differentiable : Differentiable ℂ xiL := by
  intro z; unfold xiL; have := differentiable_completedZeta₀; fun_prop

abbrev UL : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt FL z.val)

lemma key_UL : ∀ w : ℂ, Multipliable (fun p : UL => 1 + w^2/(-p.1.val^2)) ∧
    FL w / FL 0 = ∏' p : UL, (1 + w^2/(-p.1.val^2)) :=
  XiPairingPublished.concrete_upper_paired_product

lemma li_completed_ne_zero {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0] at hζ
  intro h
  rw [h, zero_div] at hζ
  exact hζ rfl

lemma xiL_zero_re {s : ℂ} (hx' : xiL s = 0) : s.re = 1/2 := by
  have hx : 1 + s * (s-1) * completedRiemannZeta₀ s = 0 := by
    unfold xiL at hx'; linear_combination 2 * hx'
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hs1 : s ≠ 1 := by rintro h; rw [h] at hx; simp at hx
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq]
    have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp
    linear_combination (-1 : ℂ) * hx
  rcases le_or_gt 1 s.re with h | h
  · exact absurd hΛ (li_completed_ne_zero h hs1)
  rcases le_or_gt s.re 0 with h' | h'
  · have : 1 ≤ (1 - s).re := by simp; linarith
    refine absurd ?_ (li_completed_ne_zero this ?_)
    · rw [completedRiemannZeta_one_sub]; exact hΛ
    · intro h2; apply hs0; linear_combination -h2
  have hζ : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  apply riemann_hypothesis s hζ
  · rintro ⟨n, hn⟩
    rw [hn] at h'
    simp at h'
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hs1

lemma UL_re (p : UL) : p.1.val.re = 0 := by
  have hord : analyticOrderNatAt FL p.1.val ≠ 0 := by
    intro h; have := p.2.isLt; omega
  have h1 : analyticOrderAt FL p.1.val ≠ 0 := by
    intro h0; apply hord; simp [analyticOrderNatAt, h0]
  have h2 := (analyticOrderAt_ne_zero.mp h1).2
  rw [FL_eq] at h2
  have := xiL_zero_re h2
  simpa using this

lemma UL_sq (p : UL) : -p.1.val^2 = (((p.1.val.im)^2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [pow_two, UL_re p]

lemma li_prod_ge {α : Type*} (S : Finset α) (x : α → ℝ) (hx : ∀ i, 0 ≤ x i) :
    1 + ∑ i ∈ S, x i ≤ ∏ i ∈ S, (1 + x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 : 0 ≤ ∑ i ∈ S, x i := Finset.sum_nonneg (fun i _ => hx i)
    nlinarith [hx a]

lemma li_prod_real (x : ℝ) :
    (∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))).im = 0 ∧
    ∀ S : Finset UL, 1 + ∑ p ∈ S, x^2/(p.1.val.im)^2 ≤ (∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))).re := by
  set P := ∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))
  have hT := (key_UL x).1.hasProd
  have hfac : ∀ p : UL, (1 + (x:ℂ)^2/(-p.1.val^2)) = ((1 + x^2/(p.1.val.im)^2 : ℝ) : ℂ) := by
    intro p; rw [UL_sq]; push_cast; ring
  have hT' : Tendsto (fun S : Finset UL => (((∏ p ∈ S, (1 + x^2/(p.1.val.im)^2) : ℝ)) : ℂ))
      atTop (𝓝 P) := by
    have := hT
    simp only [HasProd] at this
    refine this.congr (fun S => ?_)
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun p _ => hfac p)
  constructor
  · have h := (Complex.continuous_im.tendsto P).comp hT'
    have : (fun S : Finset UL => (((∏ p ∈ S, (1 + x^2/(p.1.val.im)^2) : ℝ)) : ℂ).im) = fun _ => 0 := by
      funext S; exact Complex.ofReal_im _
    simp only [Function.comp_def] at h
    rw [this] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  · intro S0
    have h := (Complex.continuous_re.tendsto P).comp hT'
    simp only [Function.comp_def, Complex.ofReal_re] at h
    have hnn : ∀ p : UL, 0 ≤ x^2/(p.1.val.im)^2 := fun p => by positivity
    refine ge_of_tendsto h ?_
    filter_upwards [Filter.eventually_ge_atTop S0] with S hS
    calc 1 + ∑ p ∈ S0, x^2/(p.1.val.im)^2 ≤ ∏ p ∈ S0, (1 + x^2/(p.1.val.im)^2) :=
          li_prod_ge S0 _ hnn
      _ ≤ ∏ p ∈ S, (1 + x^2/(p.1.val.im)^2) := by
          rw [← Finset.prod_sdiff hS]
          have h1 : 1 ≤ ∏ p ∈ S \ S0, (1 + x^2/(p.1.val.im)^2) := by
            have := li_prod_ge (S \ S0) _ hnn
            have : 0 ≤ ∑ p ∈ S \ S0, x^2/(p.1.val.im)^2 := Finset.sum_nonneg (fun i _ => hnn i)
            linarith
          have h2 : 0 ≤ ∏ p ∈ S0, (1 + x^2/(p.1.val.im)^2) :=
            Finset.prod_nonneg (fun p _ => by linarith [hnn p])
          nlinarith

lemma li_summable : Summable (fun p : UL => 1/(p.1.val.im)^2) := by
  have h := (li_prod_real 1).2
  refine summable_of_sum_le (c := Complex.re (∏' p : UL, (1 + ((1:ℝ):ℂ)^2/(-p.1.val^2))) - 1)
    (fun p => by positivity) (fun S => ?_)
  have := h S
  simp only [one_pow] at this
  linarith

lemma li_P_real (x : ℝ) : ∃ r : ℝ, 1 ≤ r ∧ (∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))) = (r:ℂ) := by
  obtain ⟨h1, h2⟩ := li_prod_real x
  refine ⟨(∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))).re, ?_, ?_⟩
  · simpa using h2 ∅
  · exact Complex.ext (by simp) (by simp [h1])

/-- The region. -/
def WL (R : ℝ) : Set ℂ := {w : ℂ | |w.im| < w.re} ∩ Metric.ball 0 R
lemma FL_zero_ne : FL 0 ≠ 0 := by
  intro h
  have k := (key_UL ((1/2 : ℝ) : ℂ)).2
  rw [h, div_zero] at k
  obtain ⟨r, hr, hr'⟩ := li_P_real (1/2)
  rw [hr'] at k
  have : r = 0 := by exact_mod_cast k.symm
  linarith

lemma zs_analyticAt (s : ℂ) (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)

/-- There are zeta zeros of positive multiplicity at arbitrarily large height. -/
lemma zs_exists_large_zero (M : ℝ) :
    ∃ s : ℂ, riemannZeta s = 0 ∧ M < s.im ∧ analyticOrderNatAt riemannZeta s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set M' := max M 1 with hM'
  obtain ⟨-, hev⟩ := BranchActualCount.concrete_zero_count_bounds
  set f : ℂ → ℝ := fun s => (((meromorphicOrderAt riemannZeta s).untopD 0 : ℤ) : ℝ) with hf
  let S : ℝ → Set ℂ := fun T => {s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z = 0}}
  have hfz : ∀ s : ℂ, riemannZeta s = 0 → M' < s.im → f s = 0 := by
    intro s hz him
    have hs1 : s ≠ 1 := by
      rintro rfl; simp at him; have := le_max_right M 1; linarith
    have han := zs_analyticAt s hs1
    have h0 := hcon s hz (lt_of_le_of_lt (le_max_left M 1) him)
    simp only [hf, han.meromorphicOrderAt_eq]
    unfold analyticOrderNatAt at h0
    by_cases ht : analyticOrderAt riemannZeta s = ⊤
    · rw [ht]; simp
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp ht
      rw [← hk] at h0 ⊢
      simp at h0
      subst h0
      simp
  have hconst : ∀ T ≥ M' + 1, (∑' ρ : S T, f ρ) = ∑' ρ : S (M' + 1), f ρ := by
    intro T hT
    rw [tsum_subtype (S T) f, tsum_subtype (S (M' + 1)) f]
    congr 1
    funext x
    by_cases hx : x ∈ S (M' + 1)
    · have hx' : x ∈ S T := by
        obtain ⟨a, ⟨b, c⟩, d⟩ := hx
        exact ⟨a, ⟨b, by linarith⟩, d⟩
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · rw [Set.indicator_of_notMem hx]
      by_cases hx' : x ∈ S T
      · rw [Set.indicator_of_mem hx']
        obtain ⟨_, ⟨b, _⟩, d⟩ := hx'
        apply hfz x d
        by_contra hle
        push Not at hle
        exact hx ⟨trivial, ⟨b, by linarith⟩, d⟩
      · rw [Set.indicator_of_notMem hx']
  set c := ∑' ρ : S (M' + 1), f ρ
  have hK := (hev.and (Filter.eventually_ge_atTop (max (M' + 1) (max (Real.exp 1)
    (32 * Real.pi * (|c| + 1)))))).exists
  obtain ⟨T, hT1, hT2⟩ := hK
  have hTa : M' + 1 ≤ T := le_trans (le_max_left _ _) hT2
  have hTb : Real.exp 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT2
  have hTc : 32 * Real.pi * (|c| + 1) ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT2
  have hNT : (∑' ρ : S T, f ρ) = c := hconst T hTa
  simp only at hT1
  change T * Real.log T / (32 * Real.pi) ≤ ∑' ρ : S T, f ρ at hT1
  rw [hNT] at hT1
  have hlog : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]; exact hTb
  have hpi : 0 < Real.pi := Real.pi_pos
  have hT0 : 0 < T := by linarith [Real.exp_pos 1]
  have : T ≤ T * Real.log T := by nlinarith
  have h32 : |c| + 1 ≤ T * Real.log T / (32 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have := le_abs_self c
  linarith

lemma li_large_p (M : ℝ) : ∃ p : UL, M < p.1.val.im := by
  obtain ⟨s, hz, him, -⟩ := zs_exists_large_zero (max M 1)
  have him1 : 1 < s.im := lt_of_le_of_lt (le_max_right _ _) him
  have hs1 : s ≠ 1 := by rintro rfl; norm_num at him1
  have hre : s.re = 1 / 2 := by
    refine riemann_hypothesis s hz ?_ hs1
    rintro ⟨m, rfl⟩; norm_num at him1
  have hs0 : s ≠ 0 := by rintro rfl; simp at hre
  have hspos : 0 < s.re := by rw [hre]; norm_num
  have hΛ : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
    rcases hz with h | h
    · exact h
    · exact absurd h (Complex.Gammaℝ_ne_zero_of_re_pos hspos)
  have hxi : xiL s = 0 := by
    have e := completedRiemannZeta_eq s
    rw [hΛ] at e
    have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    unfold xiL
    have : completedRiemannZeta₀ s = 1/s + 1/(1-s) := by linear_combination -e
    rw [this]; field_simp; ring
  set a := s - 1/2 with ha
  have haim : 0 < a.im := by rw [ha]; simp; linarith
  have hFa : FL a = 0 := by rw [FL_eq, ha]; ring_nf; ring_nf at hxi; simpa using hxi
  have hFan : AnalyticOnNhd ℂ FL Set.univ := by
    have : Differentiable ℂ FL := by
      intro z; unfold FL; have := differentiable_completedZeta₀; fun_prop
    exact fun z _ => this.analyticAt z
  have h0 : analyticOrderAt FL 0 ≠ ⊤ := by
    have : analyticOrderAt FL 0 = 0 := analyticOrderAt_eq_zero.mpr (Or.inr FL_zero_ne)
    rw [this]; exact ENat.zero_ne_top
  have htop : analyticOrderAt FL a ≠ ⊤ :=
    hFan.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
      (Set.mem_univ a) h0
  have hz0 : analyticOrderAt FL a ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hFan a (Set.mem_univ _), hFa⟩
  have hord : analyticOrderNatAt FL a ≠ 0 := by
    unfold analyticOrderNatAt
    intro h
    rcases ENat.toNat_eq_zero.mp h with h' | h'
    · exact hz0 h'
    · exact htop h'
  refine ⟨⟨⟨a, haim⟩, ⟨0, Nat.pos_of_ne_zero hord⟩⟩, ?_⟩
  show M < a.im
  rw [ha]; simp; exact lt_of_le_of_lt (le_max_left _ _) him

end JensenAux

namespace JensenAux
open Polynomial

/-- `r` is zero or has only real zeros. -/
def RR0 (r : ℂ[X]) : Prop := r = 0 ∨ ∀ z : ℂ, r.eval z = 0 → z.im = 0

lemma ms_im_sum (m : Multiset ℂ) (g : ℂ → ℂ) :
    (m.map g).sum.im = (m.map (fun x => (g x).im)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [ih]

lemma ms_sum_neg (m : Multiset ℂ) (hm : m ≠ 0) (f : ℂ → ℝ) (hf : ∀ x ∈ m, f x < 0) :
    (m.map f).sum < 0 := by
  induction m using Multiset.induction_on with
  | empty => exact absurd rfl hm
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have ha := hf a (Multiset.mem_cons_self a m)
    by_cases hm0 : m = 0
    · subst hm0; simpa using ha
    have := ih hm0 (fun x hx => hf x (Multiset.mem_cons_of_mem hx))
    linarith

lemma RR0_step (r : ℂ[X]) (hr : RR0 r) (s : ℝ) : RR0 (derivative r - C (s:ℂ) * r) := by
  rcases hr with rfl | hr
  · left; simp
  by_cases hconst : derivative r - C (s:ℂ) * r = 0
  · left; exact hconst
  right
  intro z hz
  by_contra him
  have hrz : r.eval z ≠ 0 := fun h => him (hr z h)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hrz
  have hsplit := IsAlgClosed.splits r
  have key := hsplit.eval_derivative_div_eval_of_ne_zero hrz
  have hz' : (derivative r).eval z = s * r.eval z := by
    simp only [eval_sub, eval_mul, eval_C] at hz; linear_combination hz
  rw [hz', mul_div_cancel_right₀ _ hrz] at key
  by_cases hemp : r.roots = 0
  · have hdeg : r.natDegree = 0 := by
      rw [hsplit.natDegree_eq_card_roots, hemp]; simp
    rw [hemp] at key
    simp at key
    apply hconst
    rw [eq_C_of_natDegree_eq_zero hdeg, key]; simp
  · have himk := congrArg Complex.im key
    rw [ms_im_sum] at himk
    simp only [Complex.ofReal_im] at himk
    have hterm : ∀ x ∈ r.roots, (1 / (z - x)).im = -z.im / Complex.normSq (z - x) := by
      intro x hx
      have hx' : x.im = 0 := hr x ((mem_roots hr0).mp hx)
      rw [one_div, Complex.inv_im]; simp [hx']
    have hpos : ∀ x ∈ r.roots, 0 < Complex.normSq (z - x) := by
      intro x hx
      rw [Complex.normSq_pos, sub_ne_zero]
      rintro rfl; exact hrz ((mem_roots hr0).mp hx)
    rcases lt_or_gt_of_ne him with h | h
    · have := ms_sum_neg r.roots hemp (fun x => -(1 / (z - x)).im) (fun x hx => by
        rw [hterm x hx, neg_div, neg_neg]; exact div_neg_of_neg_of_pos h (hpos x hx))
      have e : (r.roots.map (fun x => -(1 / (z - x)).im)).sum
          = -(r.roots.map (fun x => (1 / (z - x)).im)).sum := by
        rw [← Multiset.sum_map_neg]
      rw [e, ← himk] at this; simp at this
    · have := ms_sum_neg r.roots hemp (fun x => (1 / (z - x)).im) (fun x hx => by
        rw [hterm x hx]; exact div_neg_of_neg_of_pos (by linarith) (hpos x hx))
      rw [← himk] at this; simp at this

lemma RR0_smul (r : ℂ[X]) (hr : RR0 r) (c : ℂ) : RR0 (c • r) := by
  by_cases hc : c = 0
  · left; simp [hc]
  rcases hr with rfl | hr
  · left; simp
  right
  intro z hz
  rw [eval_smul, smul_eq_mul] at hz
  exact hr z ((mul_eq_zero.mp hz).resolve_left hc)

/-- The differentiation operator as an element of `Module.End`. -/
noncomputable abbrev Dop : Module.End ℂ ℂ[X] := (derivative : ℂ[X] →ₗ[ℂ] ℂ[X])

lemma RR0_prod (m : Multiset ℂ) (hm : ∀ x ∈ m, x.im = 0) (r : ℂ[X]) (hr : RR0 r) :
    RR0 (aeval Dop (m.map (fun a => X - C a)).prod r) := by
  induction m using Multiset.induction_on generalizing r with
  | empty => simpa using hr
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_apply]
    set t := aeval Dop (m.map (fun a => X - C a)).prod r
    have ht : RR0 t := ih (fun x hx => hm x (Multiset.mem_cons_of_mem hx)) r hr
    have ha : a = ((a.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hm a (Multiset.mem_cons_self a m)])
    have e : aeval Dop (X - C a) t = derivative t - C ((a.re : ℝ) : ℂ) * t := by
      rw [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, ← ha,
        smul_eq_C_mul]
    rw [e]; exact RR0_step t ht a.re

lemma RR0_aeval (q : ℂ[X]) (hq : RR0 q) (r : ℂ[X]) (hr : RR0 r) : RR0 (aeval Dop q r) := by
  rcases hq with rfl | hq
  · left; simp
  have hq0 : q ≠ 0 := by
    rintro rfl; have := hq (Complex.I) (by simp); simp at this
  have hs := (IsAlgClosed.splits q).eq_prod_roots
  rw [hs, map_mul, Module.End.mul_apply, aeval_C, Module.algebraMap_end_apply]
  refine RR0_smul _ (RR0_prod _ (fun x hx => hq x ((mem_roots hq0).mp hx)) r hr) _

lemma RR0_Xpow (d : ℕ) : RR0 (X ^ d : ℂ[X]) := by
  right; intro z hz
  simp at hz; rw [hz.1]; simp

lemma ms_prod_ge (m : Multiset ℂ) (g : ℂ → ℂ) (c : ℝ) (hc : 0 ≤ c) (hg : ∀ x ∈ m, c ≤ ‖g x‖) :
    c ^ (Multiset.card m) ≤ ‖(m.map g).prod‖ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, norm_mul]
    have h1 := ih (fun x hx => hg x (Multiset.mem_cons_of_mem hx))
    have h2 := hg a (Multiset.mem_cons_self a m)
    have h3 : 0 ≤ c ^ Multiset.card m := pow_nonneg hc _
    nlinarith

lemma RR0_bound (r : ℂ[X]) (hr : RR0 r) (d : ℕ) (hd : r.natDegree ≤ d) (w : ℂ) :
    ‖r.coeff d‖ * |w.im| ^ d ≤ ‖r.eval w‖ := by
  rcases hr with rfl | hr
  · simp
  rcases lt_or_eq_of_le hd with h | h
  · rw [coeff_eq_zero_of_natDegree_lt h]; simp
  have hr0 : r ≠ 0 := by
    rintro rfl; have := hr (Complex.I) (by simp); simp at this
  have hs := IsAlgClosed.splits r
  rw [hs.eval_eq_prod_roots, norm_mul, ← h, coeff_natDegree]
  gcongr
  have hc : Multiset.card r.roots = r.natDegree := hs.natDegree_eq_card_roots.symm
  rw [← hc]
  apply ms_prod_ge _ _ _ (abs_nonneg _)
  intro x hx
  have hx' : x.im = 0 := hr x ((mem_roots hr0).mp hx)
  have := Complex.abs_im_le_norm (w - x)
  simpa [hx'] using this

/-- Explicit form of `q(D) X^d`. -/
lemma aeval_Xpow (q : ℂ[X]) (d : ℕ) :
    aeval Dop q (X ^ d) = ∑ i ∈ Finset.range (d+1), C (q.coeff i * (d.descFactorial i : ℂ)) * X ^ (d - i) := by
  rw [aeval_eq_sum_range' (n := q.natDegree + d + 1) (by omega)]
  rw [LinearMap.sum_apply]
  have hsub : Finset.range (d+1) ⊆ Finset.range (q.natDegree + d + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.smul_apply, Module.End.pow_apply]
    show q.coeff i • (derivative^[i] (X ^ d)) = _
    rw [iterate_derivative_X_pow_eq_C_mul, smul_eq_C_mul, ← mul_assoc, ← C_mul]
  · intro i _ hi
    have hi' : d < i := by simp at hi; omega
    rw [LinearMap.smul_apply, Module.End.pow_apply]
    show q.coeff i • (derivative^[i] (X ^ d)) = 0
    rw [iterate_derivative_X_pow_eq_C_mul, Nat.descFactorial_eq_zero_iff_lt.mpr hi']
    simp

lemma nat_identity (n d k : ℕ) (hk : k ≤ d) :
    (k + n).descFactorial n * d.descFactorial k = d.choose k * (n + k).factorial := by
  rw [Nat.descFactorial_eq_factorial_mul_choose d k]
  have h := Nat.factorial_mul_descFactorial (n := k + n) (k := n) (by omega)
  rw [show k + n - n = k by omega] at h
  rw [show n + k = k + n by omega, ← h]
  ring

/-- **Jensen polynomials of real-rooted polynomials are hyperbolic** (quantitative form):
for a complex polynomial `p` all of whose zeros are real, the reversed Jensen polynomial
`∑_k C(d,k) p^{(n+k)}(0) w^{d-k}` satisfies `|…| ≥ |p^{(n)}(0)| |Im w|^d`. -/
theorem jensen_poly_bound (p : ℂ[X]) (hp : ∀ z : ℂ, p.eval z = 0 → z.im = 0) (d n : ℕ) (w : ℂ) :
    ‖(n.factorial : ℂ) * p.coeff n‖ * |w.im| ^ d ≤
      ‖∑ k ∈ Finset.range (d+1), (d.choose k : ℂ) * (((n+k).factorial : ℂ) * p.coeff (n+k)) * w^(d-k)‖ := by
  set q := derivative^[n] p with hqdef
  have hq : RR0 q := by
    have : ∀ m : ℕ, RR0 (derivative^[m] p) := by
      intro m
      induction m with
      | zero => right; simpa using hp
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        have := RR0_step _ ih 0
        simpa using this
    exact this n
  have hP := RR0_aeval q hq (X ^ d) (RR0_Xpow d)
  rw [aeval_Xpow] at hP
  set P := ∑ i ∈ Finset.range (d+1), C (q.coeff i * (d.descFactorial i : ℂ)) * X ^ (d - i) with hPdef
  have hdeg : P.natDegree ≤ d := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have hcoeff : P.coeff d = (n.factorial : ℂ) * p.coeff n := by
    rw [hPdef, finsetSum_coeff, Finset.sum_eq_single 0]
    · rw [coeff_C_mul_X_pow, if_pos (by omega)]
      simp [hqdef, coeff_iterate_derivative, Nat.descFactorial_self]
    · intro i hi0 hi
      simp at hi0
      rw [coeff_C_mul_X_pow, if_neg (by omega)]
    · intro h; simp at h
  have heval : P.eval w = ∑ k ∈ Finset.range (d+1),
      (d.choose k : ℂ) * (((n+k).factorial : ℂ) * p.coeff (n+k)) * w^(d-k) := by
    rw [hPdef, eval_finsetSum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ d := by simp at hk; omega
    rw [eval_mul, eval_C, eval_pow, eval_X, hqdef, coeff_iterate_derivative, nsmul_eq_mul]
    have := nat_identity n d k hk'
    have hc : ((k + n).descFactorial n : ℂ) * (d.descFactorial k : ℂ)
        = (d.choose k : ℂ) * ((n + k).factorial : ℂ) := by exact_mod_cast this
    rw [show k + n = n + k by omega] at hc ⊢
    linear_combination (p.coeff (n + k) * w ^ (d - k)) * hc
  have := RR0_bound P hP d hdeg w
  rwa [hcoeff, heval] at this

end JensenAux

namespace JensenAux

open Polynomial

/-- the weights `1/γ²` -/
noncomputable def cw (p : UL) : ℝ := 1 / (p.1.val.im)^2

lemma cw_pos (p : UL) : 0 < cw p := by
  have : 0 < p.1.val.im := p.1.2
  unfold cw; positivity

/-- real partial product polynomial `∏ (1 + c X)` -/
noncomputable def pR (S : Finset UL) : ℝ[X] := ∏ p ∈ S, (1 + Polynomial.C (cw p) * X)

/-- complex partial product polynomial -/
noncomputable def pS (S : Finset UL) : ℂ[X] := (pR S).map (algebraMap ℝ ℂ)

lemma pS_eval (S : Finset UL) (z : ℂ) :
    (pS S).eval z = ∏ p ∈ S, (1 + (cw p : ℂ) * z) := by
  unfold pS pR
  rw [Polynomial.map_prod, eval_prod]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp

lemma pS_real_roots (S : Finset UL) (z : ℂ) (hz : (pS S).eval z = 0) : z.im = 0 := by
  rw [pS_eval, Finset.prod_eq_zero_iff] at hz
  obtain ⟨p, _, hp⟩ := hz
  have hc := cw_pos p
  have h := congrArg Complex.im hp
  simp at h
  rcases h with h | h
  · linarith
  · exact h

lemma pS_coeff (S : Finset UL) (k : ℕ) : (pS S).coeff k = (((pR S).coeff k : ℝ) : ℂ) := by
  unfold pS; rw [coeff_map]; rfl

lemma coeff_mul_nonneg (a b : ℝ[X]) (ha : ∀ k, 0 ≤ a.coeff k) (hb : ∀ k, 0 ≤ b.coeff k) (k : ℕ) :
    0 ≤ (a * b).coeff k := by
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (ha _) (hb _))

lemma pR_nonneg (S : Finset UL) (k : ℕ) : 0 ≤ (pR S).coeff k := by
  classical
  unfold pR
  induction S using Finset.induction_on generalizing k with
  | empty => simp [coeff_one]; split_ifs <;> norm_num
  | insert a S ha ih =>
    rw [Finset.prod_insert ha]
    refine coeff_mul_nonneg _ _ (fun k => ?_) ih k
    have hc := (cw_pos a).le
    rw [coeff_add, coeff_one, coeff_C_mul, coeff_X]
    split_ifs <;> simp [hc] <;> omega

lemma pR_coeff_zero (S : Finset UL) : (pR S).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]
  unfold pR; rw [eval_prod]; simp

lemma pR_mono (S T : Finset UL) (h : S ⊆ T) (k : ℕ) : (pR S).coeff k ≤ (pR T).coeff k := by
  classical
  have e : pR T = pR S * pR (T \ S) := by
    unfold pR; rw [mul_comm, Finset.prod_sdiff h]
  rw [e, coeff_mul]
  rw [← Finset.add_sum_erase _ _ (a := ((k,0) : ℕ × ℕ)) (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp))]
  have h1 := Finset.sum_nonneg (s := (Finset.HasAntidiagonal.antidiagonal k).erase ((k,0) : ℕ × ℕ))
    (f := fun x => (pR S).coeff x.1 * (pR (T \ S)).coeff x.2)
    (fun x _ => mul_nonneg (pR_nonneg _ _) (pR_nonneg _ _))
  rw [pR_coeff_zero]; linarith

lemma pR_top (S : Finset UL) : 0 < (pR S).coeff S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [pR]
  | insert a S ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    have e : pR (insert a S) = (1 + Polynomial.C (cw a) * X) * pR S := by
      unfold pR; rw [Finset.prod_insert ha]
    rw [e, add_mul, one_mul, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul]
    have := pR_nonneg S (S.card + 1)
    have := cw_pos a
    nlinarith

lemma UL_infinite : Infinite UL := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  have : Fintype UL := Fintype.ofFinite UL
  obtain ⟨p, hp⟩ := li_large_p (∑ q : UL, |q.1.val.im|)
  have : |p.1.val.im| ≤ ∑ q : UL, |q.1.val.im| :=
    Finset.single_le_sum (f := fun q : UL => |q.1.val.im|) (fun q _ => abs_nonneg _) (Finset.mem_univ p)
  have := le_abs_self p.1.val.im
  linarith

/-- the product converges locally uniformly on the unit disc -/
lemma prod_tlu : TendstoLocallyUniformlyOn (fun (S : Finset UL) (w : ℂ) => ∏ p ∈ S, (1 + w^2/(-p.1.val^2)))
    (fun w => FL w / FL 0) atTop (Metric.ball 0 1) := by
  have h := Summable.hasProdLocallyUniformlyOn_one_add (f := fun (p : UL) (w : ℂ) => w^2/(-p.1.val^2))
    (K := Metric.ball (0:ℂ) 1) Metric.isOpen_ball li_summable ?_ ?_
  · have e : (fun w => ∏' p : UL, (1 + w^2/(-p.1.val^2))) = (fun w => FL w / FL 0) := by
      funext w; exact ((key_UL w).2).symm
    rw [e] at h
    exact h
  · refine Filter.Eventually.of_forall (fun p w hw => ?_)
    rw [UL_sq, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hγ : 0 < p.1.val.im := p.1.2
    have hw1 : ‖w‖ < 1 := by simpa using hw
    rw [abs_of_pos (by positivity)]
    have : ‖w‖^2 ≤ 1 := by nlinarith [norm_nonneg w]
    exact div_le_div_of_nonneg_right this (by positivity)
  · intro p; fun_prop

lemma iteratedDeriv_poly (P : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (fun w => P.eval w) = fun w => (derivative^[k] P).eval w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext w; exact Polynomial.deriv _

lemma prod_eq_eval (S : Finset UL) (w : ℂ) :
    ∏ p ∈ S, (1 + w^2/(-p.1.val^2)) = (expand ℂ 2 (pS S)).eval w := by
  rw [expand_eval, pS_eval]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [UL_sq]; unfold cw; push_cast; ring

lemma deriv_prod_zero (S : Finset UL) (j : ℕ) :
    iteratedDeriv (2*j) (fun w => ∏ p ∈ S, (1 + w^2/(-p.1.val^2))) 0
      = ((2*j).factorial : ℂ) * (pS S).coeff j := by
  have e : (fun w => ∏ p ∈ S, (1 + w^2/(-p.1.val^2))) = fun w => (expand ℂ 2 (pS S)).eval w := by
    funext w; exact prod_eq_eval S w
  rw [e, iteratedDeriv_poly]
  beta_reduce
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, coeff_expand (by norm_num)]
  simp [Nat.descFactorial_self]

/-- Taylor coefficients `a j` of the statement. -/
noncomputable def aT (j : ℕ) : ℂ := (j.factorial : ℂ) * iteratedDeriv (2*j) xiL (1/2) / ((2*j).factorial : ℂ)

lemma coeff_tendsto (j : ℕ) :
    Tendsto (fun S : Finset UL => (j.factorial : ℂ) * (pS S).coeff j) atTop (𝓝 (aT j / FL 0)) := by
  have hd := (li_iter Metric.isOpen_ball (fun S => by
      have e : (fun (w : ℂ) => ∏ p ∈ S, (1 + w^2/(-p.1.val^2))) = fun w => (expand ℂ 2 (pS S)).eval w :=
        funext (prod_eq_eval S)
      rw [e]; exact (Polynomial.differentiable _).differentiableOn)
    prod_tlu (2*j)).1
  have ht := hd.tendsto_at (Metric.mem_ball_self one_pos)
  simp only [deriv_prod_zero] at ht
  have e : iteratedDeriv (2*j) (fun w => FL w / FL 0) 0 = iteratedDeriv (2*j) xiL (1/2) / FL 0 := by
    rw [iteratedDeriv_div_const]
    congr 1
    have : FL = fun w => xiL (w + 1/2) := by funext w; exact FL_eq w
    rw [this, iteratedDeriv_comp_add_const]; simp
  rw [e] at ht
  have hf : ((2*j).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have := ht.const_mul ((j.factorial : ℂ) / ((2*j).factorial : ℂ))
  convert this using 1
  · funext S; field_simp
  · unfold aT; field_simp

lemma aT_ne (n : ℕ) : aT n ≠ 0 := by
  classical
  have := UL_infinite
  obtain ⟨T0, hT0⟩ := Infinite.exists_subset_card_eq UL n
  have ht := (Complex.continuous_re.tendsto _).comp (coeff_tendsto n)
  have hlow : ∀ S ≥ T0, (n.factorial : ℝ) * (pR T0).coeff n ≤
      (Complex.re ∘ (fun S : Finset UL => (n.factorial : ℂ) * (pS S).coeff n)) S := by
    intro S hS
    simp only [Function.comp_apply, pS_coeff]
    rw [show ((n.factorial : ℂ) * (((pR S).coeff n : ℝ) : ℂ)) = (((n.factorial : ℝ) * (pR S).coeff n : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_left (pR_mono _ _ hS n) (by positivity)
  have hge := ge_of_tendsto ht (Filter.eventually_atTop.mpr ⟨T0, hlow⟩)
  have hpos : 0 < (n.factorial : ℝ) * (pR T0).coeff n := by
    have := pR_top T0; rw [hT0] at this; positivity
  intro h0
  rw [h0, zero_div, Complex.zero_re] at hge
  linarith

theorem jensen_main (d n : ℕ) (z : ℂ)
    (hz : (∑ j ∈ Finset.range (d+1), (d.choose j : ℂ) * aT (n+j) * z^j) = 0) : z.im = 0 := by
  by_cases hz0 : z = 0
  · rw [hz0]; simp
  set w := z⁻¹ with hw
  set A : ℕ → ℂ := fun j => aT j / FL 0 with hA
  have hbound : ‖A n‖ * |w.im| ^ d ≤
      ‖∑ k ∈ Finset.range (d+1), (d.choose k : ℂ) * A (n+k) * w^(d-k)‖ := by
    have h1 : Tendsto (fun S : Finset UL => ‖(n.factorial : ℂ) * (pS S).coeff n‖ * |w.im| ^ d)
        atTop (𝓝 (‖A n‖ * |w.im| ^ d)) :=
      ((coeff_tendsto n).norm).mul_const _
    have h2 : Tendsto (fun S : Finset UL => ‖∑ k ∈ Finset.range (d+1), (d.choose k : ℂ) *
        (((n+k).factorial : ℂ) * (pS S).coeff (n+k)) * w^(d-k)‖) atTop
        (𝓝 ‖∑ k ∈ Finset.range (d+1), (d.choose k : ℂ) * A (n+k) * w^(d-k)‖) := by
      refine Tendsto.norm (tendsto_finsetSum _ (fun k _ => ?_))
      exact ((coeff_tendsto (n+k)).const_mul _).mul_const _
    exact le_of_tendsto_of_tendsto' h1 h2 (fun S =>
      jensen_poly_bound (pS S) (pS_real_roots S) d n w)
  have hsum : ∑ k ∈ Finset.range (d+1), (d.choose k : ℂ) * A (n+k) * w^(d-k)
      = w^d / FL 0 * ∑ j ∈ Finset.range (d+1), (d.choose j : ℂ) * aT (n+j) * z^j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ d := by simp at hk; omega
    have : w^d = w^(d-k) * w^k := by rw [← pow_add]; congr 1; omega
    have hzk : w^k * z^k = 1 := by rw [hw, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hz0)]
    simp only [hA]
    rw [this]
    linear_combination (-(d.choose k : ℂ) * aT (n+k) / FL 0 * w^(d-k)) * hzk
  rw [hsum, hz, mul_zero, norm_zero] at hbound
  have hAn : A n ≠ 0 := div_ne_zero (aT_ne n) FL_zero_ne
  have hp : |w.im| ^ d ≤ 0 := by
    have := norm_pos_iff.mpr hAn
    nlinarith [pow_nonneg (abs_nonneg w.im) d]
  have hw0 : w.im = 0 := by
    have : |w.im| ^ d = 0 := le_antisymm hp (pow_nonneg (abs_nonneg _) _)
    exact abs_eq_zero.mp (eq_zero_of_pow_eq_zero this)
  rw [hw, Complex.inv_im, neg_div, neg_eq_zero, div_eq_zero_iff] at hw0
  rcases hw0 with h | h
  · exact h
  · exact absurd (Complex.normSq_eq_zero.mp h) hz0

end JensenAux

theorem solution :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    let a (j : ℕ) : ℂ := (j.factorial : ℂ) * iteratedDeriv (2*j) xi (1/2) / ((2*j).factorial : ℂ)
    ∀ d n : ℕ, ∀ z : ℂ, (∑ j ∈ Finset.range (d+1), (d.choose j : ℂ) * a (n+j) * z^j) = 0 → z.im = 0 := by
  intro xi a d n z hz
  exact JensenAux.jensen_main d n z hz
