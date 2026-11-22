-- Prove2me | solution 1 for EntireDivisor.exists_differentiable_iteratedDeriv_eq
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T19:12:29.636909+00:00
-- url     : https://prove2.me/submissions/367a6de6-202d-4369-be91-2e463311c36b

import Mathlib

set_option autoImplicit false

open Filter Topology Metric

lemma ed_iteratedDeriv_taylor (a : ℕ → ℂ) (z₀ : ℂ) (m k : ℕ) (hk : k < m) :
    iteratedDeriv k (fun w => ∑ j ∈ Finset.range m, a j / j.factorial * (w - z₀) ^ j) z₀
      = a k := by
  have h1 := iteratedDeriv_comp_sub_const k
    (fun x : ℂ => ∑ j ∈ Finset.range m, a j / j.factorial * x ^ j) z₀
  have h2 := congrFun h1 z₀
  rw [h2, sub_self]
  simp (disch := fun_prop) only [iteratedDeriv_fun_sum, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero]
  simp [Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_range.mpr hk), Nat.factorial_ne_zero]

lemma ed_iteratedDeriv_eq_zero_of_lt {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) {k : ℕ}
    {N : ℕ∞} (hk : (k : ℕ∞) < N) (hN : N ≤ analyticOrderAt g z) : iteratedDeriv k g z = 0 := by
  have h1 : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g z := by
    have := Order.add_one_le_of_lt hk
    push_cast
    exact this.trans hN
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).mp h1 k (Nat.lt_succ_self k)

lemma ed_exists_factor {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} {m : ℕ}
    (hm : analyticOrderAt f z₀ = m) :
    ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ u z₀ ≠ 0 ∧ ∀ w, f w = (w - z₀) ^ m * u w := by
  obtain ⟨v, hva, hv0, hfv⟩ := (hf.analyticAt z₀).analyticOrderAt_eq_natCast.mp hm
  classical
  set u : ℂ → ℂ := Function.update (fun w => f w / (w - z₀) ^ m) z₀ (v z₀) with hudef
  have hfu : ∀ w, f w = (w - z₀) ^ m * u w := by
    intro w
    by_cases hw : w = z₀
    · subst hw
      have := hfv.self_of_nhds
      simp only [smul_eq_mul] at this
      simp [hudef, this]
    · have : (w - z₀) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw)
      simp only [hudef, Function.update_of_ne hw]
      field_simp
  have huv : u =ᶠ[𝓝 z₀] v := by
    have h1 : ∀ᶠ w in 𝓝[≠] z₀, u w = v w := by
      filter_upwards [self_mem_nhdsWithin, hfv.filter_mono nhdsWithin_le_nhds] with w hw hfw
      have : (w - z₀) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw)
      simp only [hudef, Function.update_of_ne hw, hfw, smul_eq_mul]
      field_simp
    have h2 : u z₀ = v z₀ := by simp [hudef]
    exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE h1 h2
  refine ⟨u, fun w => ?_, by rw [huv.eq_of_nhds]; exact hv0, hfu⟩
  by_cases hw : w = z₀
  · subst hw
    exact hva.differentiableAt.congr_of_eventuallyEq huv
  · have h3 : u =ᶠ[𝓝 w] fun w => f w / (w - z₀) ^ m := by
      filter_upwards [isOpen_ne.mem_nhds hw] with y hy
      simp [hudef, Function.update_of_ne hy]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ h3
    exact (hf w).div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.mpr hw))

lemma ed_finite_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : ∃ z, f z ≠ 0) (r : ℝ) :
    {z : ℂ | f z = 0 ∧ ‖z‖ ≤ r}.Finite := by
  obtain ⟨x, hx⟩ := hf0
  have h1 : f ⁻¹' {0}ᶜ ∈ codiscrete ℂ :=
    AnalyticOnNhd.preimage_zero_mem_codiscrete (fun z _ => hf.analyticAt z) hx
  have h2 : f ⁻¹' {0}ᶜ ∈ codiscreteWithin (closedBall (0 : ℂ) r) :=
    codiscreteWithin_mono (Set.subset_univ _) h1
  have h3 := (isCompact_closedBall (0 : ℂ) r).finite_sdiff_of_mem_codiscreteWithin h2
  refine h3.subset ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  simp [hz.1, hz.2]

lemma ed_tendsto_iteratedDeriv {ι : Type*} {φ : Filter ι} (k : ℕ) :
    ∀ {F : ι → ℂ → ℂ} {g : ℂ → ℂ}, (∀ i, Differentiable ℂ (F i)) →
    TendstoLocallyUniformlyOn F g φ Set.univ →
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv k (F i)) (iteratedDeriv k g) φ
      Set.univ := by
  induction k with
  | zero => intro F g _ hg; simpa using hg
  | succ k ih =>
    intro F g hF hg
    have h1 := hg.deriv (Eventually.of_forall fun i => (hF i).differentiableOn) isOpen_univ
    have h2 := ih (F := deriv ∘ F) (g := deriv g) (fun i => (hF i).deriv) h1
    simpa [iteratedDeriv_succ'] using h2

lemma ed_local {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ → ℕ → ℂ) {z₀ : ℂ}
    (hfin : analyticOrderAt f z₀ ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ k : ℕ, (k : ℕ∞) < analyticOrderAt f z₀ → iteratedDeriv k G z₀ = c z₀ k) ∧
      (∀ z, z ≠ z₀ → analyticOrderAt f z ≤ analyticOrderAt G z) ∧
      (z₀ ≠ 0 → ∀ w, ‖w‖ ≤ ‖z₀‖ / 2 → ‖G w‖ ≤ ε) := by
  set m := analyticOrderNatAt f z₀ with hmdef
  have hm : analyticOrderAt f z₀ = m := (Nat.cast_analyticOrderNatAt hfin).symm
  obtain ⟨u, hu, hu0, hfu⟩ := ed_exists_factor hf hm
  set J : ℂ → ℂ := fun w => ∑ j ∈ Finset.range m, c z₀ j / j.factorial * (w - z₀) ^ j
    with hJdef
  set h : ℂ → ℂ := fun w => J w / u w with hhdef
  set P : ℂ → ℂ := fun w =>
    ∑ j ∈ Finset.range m, iteratedDeriv j h z₀ / j.factorial * (w - z₀) ^ j with hPdef
  have hJ : Differentiable ℂ J := by fun_prop
  have hP : Differentiable ℂ P := by fun_prop
  have hha : AnalyticAt ℂ h z₀ := (hJ.analyticAt z₀).div (hu.analyticAt z₀) hu0
  have hPh : (m : ℕ∞) ≤ analyticOrderAt (P - h) z₀ := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hP.analyticAt z₀).sub hha)]
    intro i hi
    rw [iteratedDeriv_sub (hP.analyticAt z₀).contDiffAt hha.contDiffAt, hPdef,
      ed_iteratedDeriv_taylor _ _ _ _ hi, sub_self]
  have huPJ : (m : ℕ∞) ≤ analyticOrderAt (u * P - J) z₀ := by
    have heq : (u * P - J) =ᶠ[𝓝 z₀] u * (P - h) := by
      filter_upwards [hu.continuous.continuousAt.eventually_ne hu0] with w hw
      simp only [Pi.sub_apply, Pi.mul_apply, hhdef]
      field_simp
    rw [analyticOrderAt_congr heq, analyticOrderAt_mul (hu.analyticAt z₀)
      ((hP.analyticAt z₀).sub hha)]
    exact hPh.trans le_add_self
  have key : ∀ E : ℂ → ℂ, Differentiable ℂ E → (m : ℕ∞) ≤ analyticOrderAt (E - 1) z₀ →
      (∀ k : ℕ, (k : ℕ∞) < analyticOrderAt f z₀ → iteratedDeriv k (u * P * E) z₀ = c z₀ k) ∧
      (∀ z, z ≠ z₀ → analyticOrderAt f z ≤ analyticOrderAt (u * P * E) z) := by
    intro E hE hE1
    have huP : Differentiable ℂ (u * P) := hu.mul hP
    constructor
    · intro k hk
      have h1 : (m : ℕ∞) ≤ analyticOrderAt (u * P * E - J) z₀ := by
        have heq : u * P * E - J = u * P * (E - 1) + (u * P - J) := by ring
        rw [heq]
        refine le_trans (le_min ?_ huPJ) le_analyticOrderAt_add
        have hE1a : AnalyticAt ℂ (E - 1) z₀ := (hE.analyticAt z₀).sub analyticAt_const
        rw [analyticOrderAt_mul (huP.analyticAt z₀) hE1a]
        exact hE1.trans le_add_self
      have h2 := ed_iteratedDeriv_eq_zero_of_lt
        (((huP.mul hE).analyticAt z₀).sub (hJ.analyticAt z₀)) (hm ▸ hk) h1
      rw [iteratedDeriv_sub ((huP.mul hE).analyticAt z₀).contDiffAt
        (hJ.analyticAt z₀).contDiffAt, sub_eq_zero] at h2
      have hk' : k < m := by exact_mod_cast hm ▸ hk
      rw [h2, hJdef, ed_iteratedDeriv_taylor _ _ _ _ hk']
    · intro z hz
      have h1 : analyticOrderAt f z = analyticOrderAt u z := by
        have : f = (fun w => (w - z₀) ^ m) * u := funext hfu
        rw [this, analyticOrderAt_mul (by fun_prop) (hu.analyticAt z)]
        have : analyticOrderAt (fun w => (w - z₀) ^ m) z = 0 := by
          rw [analyticOrderAt_eq_zero]
          right; exact pow_ne_zero _ (sub_ne_zero.mpr hz)
        rw [this, zero_add]
      rw [h1, mul_assoc, analyticOrderAt_mul (hu.analyticAt z) ((hP.mul hE).analyticAt z)]
      exact le_self_add
  by_cases hz0 : z₀ = 0
  · obtain ⟨h1, h2⟩ := key 1 (differentiable_const 1) (by
      have : analyticOrderAt ((1 : ℂ → ℂ) - 1) z₀ = ⊤ :=
        analyticOrderAt_eq_top.mpr (Eventually.of_forall fun _ => by simp)
      rw [this]; exact le_top)
    exact ⟨u * P * 1, (hu.mul hP).mul (differentiable_const _), h1, h2,
      fun h => absurd hz0 h⟩
  · obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) (‖z₀‖/2)).exists_bound_of_continuousOn
      (hu.mul hP).continuous.continuousOn
    set B : ℝ := |M| * (m * 2 ^ m) + 1 with hBdef
    have hB : 0 < B := by positivity
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hB) (by norm_num : (1/2 : ℝ) < 1)
    set E : ℂ → ℂ := fun w => 1 - (1 - (w / z₀) ^ N) ^ m with hEdef
    have hE : Differentiable ℂ E := by fun_prop
    have hE1 : (m : ℕ∞) ≤ analyticOrderAt (E - 1) z₀ := by
      have heq : E - 1 = -((fun w => 1 - (w / z₀) ^ N) ^ m) := by
        funext w; simp [hEdef]
      rw [heq, analyticOrderAt_neg, analyticOrderAt_pow (by fun_prop)]
      have : 1 ≤ analyticOrderAt (fun w => 1 - (w / z₀) ^ N) z₀ := by
        rw [Order.one_le_iff_ne_zero,
          (show AnalyticAt ℂ (fun w => 1 - (w / z₀) ^ N) z₀ by fun_prop).analyticOrderAt_ne_zero]
        simp [hz0]
      calc (m : ℕ∞) = m • (1 : ℕ∞) := by simp
        _ ≤ _ := nsmul_le_nsmul_right this m
    obtain ⟨h1, h2⟩ := key E hE hE1
    refine ⟨u * P * E, (hu.mul hP).mul hE, h1, h2, fun _ w hw => ?_⟩
    have hw' : ‖w / z₀‖ ≤ 1/2 := by
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hz0)]; linarith
    set q := (w / z₀) ^ N with hqdef
    have hq : ‖q‖ ≤ (1/2) ^ N := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hw' N
    have hq1 : ‖q‖ ≤ 1 := hq.trans (pow_le_one₀ (by norm_num) (by norm_num))
    have hEw : E w = q * ∑ i ∈ Finset.range m, (1 - q) ^ i := by
      have := geom_sum_mul (1 - q) m
      simp only [hEdef]
      linear_combination this
    have hsum : ‖∑ i ∈ Finset.range m, (1 - q) ^ i‖ ≤ m * 2 ^ m := by
      calc _ ≤ ∑ i ∈ Finset.range m, ‖(1 - q) ^ i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range m, (2:ℝ) ^ m := by
          apply Finset.sum_le_sum; intro i hi
          rw [norm_pow]
          have : ‖1 - q‖ ≤ 2 := (norm_sub_le _ _).trans (by simp; linarith)
          calc ‖1 - q‖ ^ i ≤ 2 ^ i := pow_le_pow_left₀ (norm_nonneg _) this i
            _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hi).le
        _ = m * 2 ^ m := by simp
    have hMw : ‖(u * P) w‖ ≤ |M| := (hM w (by simpa using hw)).trans (le_abs_self M)
    have hNB : (1/2 : ℝ) ^ N * B < ε := (lt_div_iff₀ hB).mp hN
    have hpos : (0:ℝ) ≤ (1/2) ^ N := by positivity
    calc ‖(u * P * E) w‖ = ‖(u * P) w‖ * (‖q‖ * ‖∑ i ∈ Finset.range m, (1 - q) ^ i‖) := by
          rw [Pi.mul_apply (u * P) E w, norm_mul, hEw, norm_mul]
      _ ≤ |M| * ((1/2) ^ N * (m * 2 ^ m)) := by gcongr
      _ ≤ (1/2) ^ N * B := by rw [hBdef]; nlinarith
      _ ≤ ε := hNB.le

theorem solution (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : ∃ z : ℂ, f z ≠ 0) (c : ℂ → ℕ → ℂ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z : ℂ, ∀ m : ℕ, (m : ℕ∞) < analyticOrderAt f z → iteratedDeriv m g z = c z m := by
  have hfin : ∀ z, analyticOrderAt f z ≠ ⊤ := by
    intro z hz
    obtain ⟨x, hx⟩ := hf0
    have := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z (fun w => hf.analyticAt w)).mp hz
    exact hx (by rw [this]; rfl)
  set Z : Set ℂ := {z | f z = 0} with hZdef
  have hZc : Z.Countable := by
    have : Z = ⋃ n : ℕ, {z : ℂ | f z = 0 ∧ ‖z‖ ≤ n} := by
      ext z
      simp only [hZdef, Set.mem_ofPred_eq, Set.mem_iUnion]
      exact ⟨fun h => ⟨_, h, Nat.le_ceil _⟩, fun ⟨_, h, _⟩ => h⟩
    rw [this]
    exact Set.countable_iUnion fun n => (ed_finite_zeros hf hf0 n).countable
  have : Countable Z := hZc.to_subtype
  obtain ⟨e, he⟩ := exists_injective_nat Z
  set ε : Z → ℝ := fun i => (1/2 : ℝ) ^ (e i) with hεdef
  have hεpos : ∀ i, 0 < ε i := fun i => by positivity
  have hεsum : Summable ε := summable_geometric_two.comp_injective he
  choose G hGd hGjet hGord hGbd using fun i : Z => ed_local hf c (hfin i) (hεpos i)
  set F : Finset Z → ℂ → ℂ := fun t w => ∑ i ∈ t, G i w with hFdef
  set g : ℂ → ℂ := fun w => ∑' i : Z, G i w with hgdef
  have hFd : ∀ t, Differentiable ℂ (F t) := fun t => Differentiable.fun_sum fun i _ => hGd i
  have hconv : TendstoLocallyUniformlyOn F g atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    set R' := max R 0 + 1 with hR'def
    have hR' : 0 < R' := by positivity
    apply tendstoUniformlyOn_tsum_of_cofinite_eventually hεsum
    rw [Filter.eventually_cofinite]
    have hfinR : {i : Z | ‖(i : ℂ)‖ ≤ 2 * R'}.Finite := by
      have := (ed_finite_zeros hf hf0 (2 * R')).preimage
        (Subtype.val_injective (p := fun z : ℂ => z ∈ Z)).injOn
      refine this.subset ?_
      intro i hi; exact ⟨i.2, hi⟩
    refine hfinR.subset ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi ⊢
    by_contra hlt
    push Not at hlt
    apply hi
    intro x hx
    have hx' : ‖x‖ ≤ R' := by
      have := hR hx
      rw [mem_closedBall, dist_zero_right] at this
      linarith [le_max_left R 0]
    apply hGbd i (by intro h0; rw [h0, norm_zero] at hlt; linarith) x
    linarith
  have hg : Differentiable ℂ g := by
    have := hconv.differentiableOn (Eventually.of_forall fun t => (hFd t).differentiableOn)
      isOpen_univ
    exact differentiableOn_univ.mp this
  refine ⟨g, hg, fun z k hk => ?_⟩
  have hz : f z = 0 :=
    apply_eq_zero_of_analyticOrderAt_ne_zero (by intro h; simp [h] at hk)
  set i₀ : Z := ⟨z, hz⟩
  have hlim := (ed_tendsto_iteratedDeriv k hFd hconv).tendsto_at (Set.mem_univ z)
  have hev : ∀ᶠ t in (atTop : Filter (Finset Z)), iteratedDeriv k (F t) z = c z k := by
    filter_upwards [eventually_ge_atTop {i₀}] with t ht
    have hi₀ : i₀ ∈ t := ht (Finset.mem_singleton_self _)
    rw [hFdef]
    rw [iteratedDeriv_fun_sum (fun i _ => (hGd i).contDiff.contDiffAt)]
    rw [Finset.sum_eq_single_of_mem i₀ hi₀]
    · exact hGjet i₀ k hk
    · intro i _ hi
      apply ed_iteratedDeriv_eq_zero_of_lt ((hGd i).analyticAt z) hk
      apply hGord i z
      intro h; apply hi; exact Subtype.ext h.symm
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm))
