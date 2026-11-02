-- Prove2me | solution 1 for FKZAvg.WStar.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T15:57:08.265312+00:00
-- url     : https://prove2.me/submissions/f404cb24-4f3a-4871-93cf-37b0a515ac1a

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_SchalAvg_AvgOpt_Model
import Definitions.Def_FKZAvg_WStar_Assumptions
import Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_ii
import Theorems.Thm_FKZAvg_WStar_lemma_3_lsc
import Theorems.Thm_FKZAvg_WStar_theorem_2

open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter SchalAvg.AvgOpt FKZAvg.WStar

set_option linter.unusedSectionVars false

namespace FKZL67

open FeinbergLiang.ACOE

/-- `f ≤ liminf u` and `g ≤ liminf v` give `f + g ≤ liminf (u + v)` in `[0, ∞]`. -/
theorem add_le_liminf {f g : ℝ≥0∞} {u v : ℕ → ℝ≥0∞}
    (hf : f ≤ liminf u atTop) (hg : g ≤ liminf v atTop) :
    f + g ≤ liminf (fun n => u n + v n) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun z hz => ?_
  refine le_liminf_of_le (by isBoundedDefault) ?_
  rcases eq_or_ne f 0 with h0 | h0
  · rw [h0, zero_add] at hz
    exact (eventually_lt_of_lt_liminf (lt_of_lt_of_le hz hg)).mono fun n hn =>
      hn.le.trans le_add_self
  rcases eq_or_ne g 0 with h0' | h0'
  · rw [h0', add_zero] at hz
    exact (eventually_lt_of_lt_liminf (lt_of_lt_of_le hz hf)).mono fun n hn =>
      hn.le.trans le_self_add
  obtain ⟨y', hy', z', hz', hl⟩ := ENNReal.exists_lt_add_of_lt_add hz h0 h0'
  exact ((eventually_lt_of_lt_liminf (lt_of_lt_of_le hy' hf)).and
    (eventually_lt_of_lt_liminf (lt_of_lt_of_le hz' hg))).mono fun n hn =>
      hl.le.trans (add_le_add hn.1.le hn.2.le)


/-! ### Abelian lemma (as in the accepted proof of Theorem 1) -/

lemma tail_geom (b : ℝ≥0∞) (t : ℕ) :
    ∑' N : ℕ, (if t ≤ N then b ^ N else 0) = b ^ t * (1 - b)⁻¹ := by
  rw [← Summable.sum_add_tsum_nat_add' (k := t) ENNReal.summable]
  have h1 : ∑ i ∈ Finset.range t, (if t ≤ i then b ^ i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [Finset.mem_range] at hi
    simp [show ¬ t ≤ i by omega]
  rw [h1, zero_add]
  simp only [le_add_iff_nonneg_left, zero_le, if_true, pow_add]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]

lemma abel_ident (a : ℕ → ℝ≥0∞) (b : ℝ≥0∞) (hb : b < 1) :
    ∑' t, b ^ t * a t = (1 - b) * ∑' N : ℕ, b ^ N * ∑ t ∈ Finset.range (N + 1), a t := by
  have e : ∀ N : ℕ, b ^ N * ∑ t ∈ Finset.range (N + 1), a t =
      ∑' t, a t * (if t ≤ N then b ^ N else 0) := by
    intro N
    rw [sum_eq_tsum_indicator, ← ENNReal.tsum_mul_left]
    congr 1; ext t
    by_cases h : t ≤ N
    · simp [Set.indicator, Finset.mem_range, Nat.lt_succ_iff.mpr h, h, mul_comm]
    · simp [Set.indicator, Finset.mem_range, h, show ¬ t < N + 1 by omega]
  simp_rw [e]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, tail_geom]
  rw [← ENNReal.tsum_mul_left]
  congr 1; ext t
  have h0 : (1 - b) ≠ 0 := (tsub_pos_of_lt hb).ne'
  have ht : (1 - b) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  calc b ^ t * a t = b ^ t * a t * ((1 - b) * (1 - b)⁻¹) := by
        rw [ENNReal.mul_inv_cancel h0 ht, mul_one]
    _ = (1 - b) * (a t * (b ^ t * (1 - b)⁻¹)) := by ring

lemma abel_core (a : ℕ → ℝ≥0∞) (C L' : ℝ≥0∞)
    (hS : ∀ N : ℕ, ∑ t ∈ Finset.range N, a t ≤ C + N * L') (b : ℝ≥0∞) (hb : b < 1) :
    (1 - b) * ∑' t, b ^ t * a t ≤ (1 - b) * C + L' := by
  have h0 : (1 - b) ≠ 0 := (tsub_pos_of_lt hb).ne'
  have ht : (1 - b) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hone := abel_ident (fun _ => (1 : ℝ≥0∞)) b hb
  simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_mul] at hone
  rw [ENNReal.tsum_geometric] at hone
  push_cast at hone
  rw [abel_ident a b hb]
  set k := (1 - b)⁻¹ with hk
  set s := ∑' N : ℕ, b ^ N * ((N : ℝ≥0∞) + 1) with hs
  have hk1 : (1 - b) * k = 1 := ENNReal.mul_inv_cancel h0 ht
  have hsplit : ∑' N : ℕ, b ^ N * (C + ((N + 1 : ℕ) : ℝ≥0∞) * L') = C * k + L' * s := by
    have e : ∀ N : ℕ, b ^ N * (C + ((N + 1 : ℕ) : ℝ≥0∞) * L') =
        C * b ^ N + L' * (b ^ N * ((N : ℝ≥0∞) + 1)) := fun N => by push_cast; ring
    simp_rw [e]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  calc (1 - b) * ((1 - b) * ∑' N : ℕ, b ^ N * ∑ t ∈ Finset.range (N + 1), a t)
      ≤ (1 - b) * ((1 - b) * ∑' N : ℕ, b ^ N * (C + ((N + 1 : ℕ) : ℝ≥0∞) * L')) := by
        gcongr with N
        exact hS (N + 1)
    _ = (1 - b) * C * ((1 - b) * k) + L' * ((1 - b) * ((1 - b) * s)) := by
        rw [hsplit]; ring
    _ = (1 - b) * C + L' := by
        rw [← hone, hk1, mul_one, mul_one]

lemma abel (a : ℕ → ℝ≥0∞) :
    limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * ∑' t, ENNReal.ofReal (β ^ t) * a t) (𝓝[<] 1)
      ≤ limsup (fun N : ℕ => (N : ℝ≥0∞)⁻¹ * ∑ t ∈ Finset.range N, a t) atTop := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro L' hL'
  rcases eq_or_ne L' ⊤ with rfl | hLt
  · exact le_top
  have hev := Filter.eventually_lt_of_limsup_lt hL'
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hev
  set N1 := max N0 1
  set S := fun N => ∑ t ∈ Finset.range N, a t
  have hbig : ∀ N ≥ N1, S N ≤ N * L' := by
    intro N hN
    have hN1 : (N : ℝ≥0∞) ≠ 0 := by
      have : 1 ≤ N := le_trans (le_max_right _ _) hN
      exact_mod_cast (show N ≠ 0 by omega)
    have := (hN0 N (le_trans (le_max_left _ _) hN)).le
    calc S N = N * ((N : ℝ≥0∞)⁻¹ * S N) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hN1 (ENNReal.natCast_ne_top N), one_mul]
      _ ≤ N * L' := by gcongr
  have hS : ∀ N : ℕ, S N ≤ S N1 + N * L' := by
    intro N
    rcases le_or_gt N N1 with h | h
    · exact le_add_right (Finset.sum_le_sum_of_subset (Finset.range_mono h))
    · exact le_add_left (hbig N h.le)
  have hCfin : S N1 ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hLt) (hbig N1 le_rfl)
  have hlim : Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β) * S N1 + L') (𝓝[<] 1) (𝓝 L') := by
    have h1 : Tendsto (fun β : ℝ => ENNReal.ofReal (1 - β)) (𝓝[<] 1) (𝓝 0) := by
      have : Tendsto (fun β : ℝ => 1 - β) (𝓝 (1 : ℝ)) (𝓝 0) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (1 : ℝ)))
        simpa using this
      have := (ENNReal.tendsto_ofReal this).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1 : ℝ)))
      simpa using this
    have := (ENNReal.Tendsto.mul_const h1 (Or.inr hCfin)).add_const L'
    simpa using this
  rw [← hlim.limsup_eq]
  apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with β hβ
  have hb : ENNReal.ofReal β < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hβ.2
  have e1 : ENNReal.ofReal (1 - β) = 1 - ENNReal.ofReal β := by
    rw [ENNReal.ofReal_sub _ hβ.1.le, ENNReal.ofReal_one]
  have e2 : ∀ t : ℕ, ENNReal.ofReal (β ^ t) = ENNReal.ofReal β ^ t :=
    fun t => ENNReal.ofReal_pow hβ.1.le t
  simp only [e1, e2]
  exact abel_core a (S N1) L' hS _ hb


variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

lemma Jn_eq (M : MDP X A) (hc : Measurable (fun p : X × A => M.cost p.1 p.2))
    (π : Policy X A) (n : ℕ) (x : X) :
    vN M π n 1 x = ∑ t ∈ Finset.range n, ∫⁻ ω, M.cost (ω t).1 (ω t).2 ∂(pathMeasure M π x) := by
  unfold vN
  simp only [one_pow, ENNReal.ofReal_one, one_mul]
  rw [lintegral_finsetSum]
  intro t _
  exact hc.comp (measurable_pi_apply t)

lemma Jb_eq (M : MDP X A) (hc : Measurable (fun p : X × A => M.cost p.1 p.2))
    (π : Policy X A) (β : ℝ) (x : X) :
    vDisc M π β x = ∑' t, ENNReal.ofReal (β ^ t) *
      ∫⁻ ω, M.cost (ω t).1 (ω t).2 ∂(pathMeasure M π x) := by
  unfold vDisc
  rw [lintegral_tsum]
  · congr 1; ext t
    rw [lintegral_const_mul (f := fun ω : ℕ → X × A => M.cost (ω t).1 (ω t).2) _ (hc.comp (measurable_pi_apply t))]
  · intro t
    exact ((hc.comp (measurable_pi_apply t)).const_mul _).aemeasurable

lemma abel_policy (M : Model X A) (π : Policy X A) (x : X) :
    limsup (fun β : ℝ => ENNReal.ofReal (1 - β) * Jbeta M π β x) (𝓝[<] 1) ≤ Phi M π x := by
  unfold Jbeta Phi avgCost
  simp_rw [Jb_eq _ M.cost_meas, Jn_eq _ M.cost_meas]
  exact abel _

/-- `w̄ ≤ w*` (inequality (7) of the paper). -/
lemma gUpper_le_gStar (M : Model X A) : gUpper M ≤ gStar M := by
  refine le_iInf fun x => le_iInf fun π => ?_
  refine le_trans ?_ (abel_policy M π.1 x)
  apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
  exact Eventually.of_forall fun β => mul_le_mul_of_nonneg_left
    ((iInf_le (fun y => vβ M β y) x).trans
      (iInf_le (fun π : {π : Policy X A // Admissible M π} => Jbeta M π.1 β x) π)) zero_le

lemma gUpper_lt_top (M : Model X A) (hB : CondBLow M) : gUpper M < ⊤ :=
  lt_of_le_of_lt (gUpper_le_gStar M) hB.1

/-- `v_α` is nondecreasing in `α ≥ 0`. -/
lemma vβ_mono (M : Model X A) {α β : ℝ} (h0 : 0 ≤ α) (h : α ≤ β) (x : X) :
    vβ M α x ≤ vβ M β x := by
  refine iInf_mono fun π => ?_
  unfold Jbeta vDisc
  refine lintegral_mono fun ω => ENNReal.tsum_le_tsum fun t => ?_
  gcongr

lemma mβ_mono (M : Model X A) {α β : ℝ} (h0 : 0 ≤ α) (h : α ≤ β) : mβ M α ≤ mβ M β :=
  iInf_mono fun x => vβ_mono M h0 h x

/-- There is `α₀ ∈ [0, 1)` with `(1 - α) m_α < w̄ + ε` for `α ∈ [α₀, 1)`. -/
lemma exists_alpha0 (M : Model X A) (hB : CondBLow M) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ α₀ : ℝ, 0 ≤ α₀ ∧ α₀ < 1 ∧
      ∀ α, α₀ ≤ α → α < 1 → ENNReal.ofReal (1 - α) * mβ M α < gUpper M + ε := by
  have hlt : gUpper M < gUpper M + ε := ENNReal.lt_add_right (gUpper_lt_top M hB).ne hε.ne'
  have hev := eventually_lt_of_limsup_lt hlt (by isBoundedDefault)
  obtain ⟨b, hb, hsub⟩ := mem_nhdsLT_iff_exists_Ico_subset.1 hev
  refine ⟨max b 0, le_max_right _ _, max_lt hb one_pos, fun α hα h1 => ?_⟩
  exact hsub ⟨le_trans (le_max_left _ _) hα, h1⟩

/-- `m_α < ∞` for every `α ∈ [0, 1)`. -/
lemma mβ_lt_top (M : Model X A) (hB : CondBLow M) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    mβ M α < ⊤ := by
  obtain ⟨α₀, h00, h01, hα₀⟩ := exists_alpha0 M hB (ε := 1) one_pos
  set β := max α α₀
  have hβ1 : β < 1 := max_lt h1 h01
  have hβ := hα₀ β (le_max_right _ _) hβ1
  have hpos : ENNReal.ofReal (1 - β) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hfin : mβ M β < ⊤ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc, ENNReal.mul_top hpos] at hβ
    exact absurd hβ (not_lt.2 le_top)
  exact lt_of_le_of_lt (mβ_mono M h0 (le_max_left _ _)) hfin

/-- A uniform bound `(1 - α) m_α ≤ ε*` for `α ∈ [0, 1)` ((28) of the paper). -/
lemma exists_eps_star (M : Model X A) (hB : CondBLow M) :
    ∃ E : ℝ≥0∞, E ≠ ⊤ ∧ ∀ α, 0 ≤ α → α < 1 → ENNReal.ofReal (1 - α) * mβ M α ≤ E := by
  obtain ⟨α₀, h00, h01, hα₀⟩ := exists_alpha0 M hB (ε := 1) one_pos
  refine ⟨max (gUpper M + 1) (mβ M α₀), ?_, fun α h0 h1 => ?_⟩
  · exact max_ne_top (ENNReal.add_ne_top.2 ⟨(gUpper_lt_top M hB).ne, ENNReal.one_ne_top⟩)
      (mβ_lt_top M hB h00 h01).ne
  rcases le_or_gt α₀ α with h | h
  · exact (hα₀ α h h1).le.trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    calc ENNReal.ofReal (1 - α) * mβ M α ≤ 1 * mβ M α := by
          gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
      _ = mβ M α := one_mul _
      _ ≤ mβ M α₀ := mβ_mono M h0 h.le

section Topo

variable {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]

omit [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
/-- The lower envelope `x ↦ liminf_{y → x} f y` is lower semicontinuous. -/
lemma lsc_liminf_nhds (f : X → ℝ≥0∞) : LowerSemicontinuous (fun x => liminf f (𝓝 x)) := by
  intro x y hy0
  have hy : y < liminf f (𝓝 x) := hy0
  rw [liminf_eq_iSup_iInf] at hy
  obtain ⟨S, hS⟩ := lt_iSup_iff.1 hy
  obtain ⟨hSx, hS'⟩ := lt_iSup_iff.1 hS
  obtain ⟨U, hUS, hU, hxU⟩ := mem_nhds_iff.1 hSx
  filter_upwards [hU.mem_nhds hxU] with x' hx'
  show y < liminf f (𝓝 x')
  rw [liminf_eq_iSup_iInf]
  refine lt_of_lt_of_le hS' (le_iSup₂_of_le U (hU.mem_nhds hx') (biInf_mono hUS))

omit [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
/-- The joint lower envelope `x ↦ liminf_{i → F, y → x} f (i, y)` is lower semicontinuous. -/
lemma lsc_liminf_prod {ι : Type*} (F : Filter ι) (f : ι × X → ℝ≥0∞) :
    LowerSemicontinuous (fun x => liminf f (F ×ˢ 𝓝 x)) := by
  intro x y hy0
  have hy : y < liminf f (F ×ˢ 𝓝 x) := hy0
  rw [liminf_eq_iSup_iInf] at hy
  obtain ⟨S, hS⟩ := lt_iSup_iff.1 hy
  obtain ⟨hSx, hS'⟩ := lt_iSup_iff.1 hS
  obtain ⟨t, ht, N, hN, htN⟩ := mem_prod_iff.1 hSx
  obtain ⟨U, hUN, hU, hxU⟩ := mem_nhds_iff.1 hN
  filter_upwards [hU.mem_nhds hxU] with x' hx'
  show y < liminf f (F ×ˢ 𝓝 x')
  rw [liminf_eq_iSup_iInf]
  refine lt_of_lt_of_le hS' (le_iSup₂_of_le (t ×ˢ U) (prod_mem_prod ht (hU.mem_nhds hx'))
    (biInf_mono ((Set.prod_mono le_rfl hUN).trans htN)))

lemma UInf_mono (M : Model X A) {b b' : ℝ} (h : b ≤ b') (y : X) :
    UInf M b y ≤ UInf M b' y :=
  biInf_mono fun _ hα => ⟨h.trans hα.1, hα.2⟩

omit [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
lemma liminf_nhds_le_self (f : X → ℝ≥0∞) (x : X) : liminf f (𝓝 x) ≤ f x :=
  liminf_le_of_le (by isBoundedDefault) fun b hb => hb.self_of_nhds

lemma uLow_le_UInf (M : Model X A) (β : ℝ) (x : X) : uLow M β x ≤ UInf M β x :=
  liminf_nhds_le_self _ x

lemma uAvg_le_liminf (M : Model X A) (x : X) :
    uAvg M x ≤ liminf (fun α => wβ M α x) (𝓝[<] 1) := by
  unfold uAvg
  calc liminf (fun p : ℝ × X => wβ M p.1 p.2) ((𝓝[<] (1 : ℝ)) ×ˢ 𝓝 x)
      ≤ liminf (fun p : ℝ × X => wβ M p.1 p.2) ((𝓝[<] (1 : ℝ)) ×ˢ pure x) :=
        liminf_le_liminf_of_le (Filter.prod_mono le_rfl (pure_le_nhds x))
    _ = liminf (fun α => wβ M α x) (𝓝[<] 1) := by
        rw [Filter.prod_pure, ← liminf_comp]; rfl

lemma uAvg_ne_top (M : Model X A) (hB : CondBLow M) (x : X) : uAvg M x ≠ ⊤ :=
  (lt_of_le_of_lt (uAvg_le_liminf M x) (hB.2 x)).ne

/-- Some `α ∈ [β, 1)` has `u_α(x) < ∞`. -/
lemma exists_wβ_lt_top (M : Model X A) (hB : CondBLow M) {β : ℝ} (hβ : β < 1) (x : X) :
    ∃ α ∈ Set.Ico β 1, wβ M α x < ⊤ := by
  have hfreq := frequently_lt_of_liminf_lt (by isBoundedDefault) (hB.2 x)
  have hev : ∀ᶠ α in 𝓝[<] (1 : ℝ), α ∈ Set.Ico β 1 := Ico_mem_nhdsLT hβ
  obtain ⟨α, h1, h2⟩ := (hfreq.and_eventually hev).exists
  exact ⟨α, h2, h1⟩

lemma UInf_lt_top (M : Model X A) (hB : CondBLow M) {β : ℝ} (hβ : β < 1) (x : X) :
    UInf M β x < ⊤ := by
  obtain ⟨α, hα, hlt⟩ := exists_wβ_lt_top M hB hβ x
  exact lt_of_le_of_lt (biInf_le (fun α => wβ M α x) hα) hlt

lemma uLow_le_uAvg (M : Model X A) {β : ℝ} (hβ : β < 1) (x : X) : uLow M β x ≤ uAvg M x := by
  unfold uLow uAvg
  rw [liminf_eq_iSup_iInf, liminf_eq_iSup_iInf]
  refine iSup₂_le fun N hN => le_iSup₂_of_le (Set.Ico β 1 ×ˢ N)
    (prod_mem_prod (Ico_mem_nhdsLT hβ) hN) ?_
  refine le_iInf₂ fun p hp => ?_
  refine (biInf_le (fun y => UInf M β y) hp.2).trans ?_
  unfold UInf
  exact biInf_le (fun α => wβ M α p.2) hp.1

/-- Corollary 1 (lim inf form): along `β_n → 1`, `u ≤ liminf_{n, y → x} u̲_{β_n}(y)`. -/
lemma uAvg_le_liminf_seq (M : Model X A) (βs : ℕ → ℝ) (hβ : Tendsto βs atTop (𝓝 1)) (s : X) :
    uAvg M s ≤ liminf (fun p : ℕ × X => uLow M (βs p.1) p.2) (atTop ×ˢ 𝓝 s) := by
  unfold uAvg
  rw [liminf_eq_iSup_iInf]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨t, ht, N, hN, htN⟩ := mem_prod_iff.1 hS
  obtain ⟨b, hb, hbt⟩ := mem_nhdsLT_iff_exists_Ico_subset.1 ht
  have h1 : ⨅ p ∈ S, wβ M p.1 p.2 ≤ ⨅ y ∈ N, UInf M b y := by
    refine le_iInf₂ fun y hy => ?_
    unfold UInf
    refine le_iInf₂ fun α hα => ?_
    have hmem : ((α, y) : ℝ × X) ∈ S := htN (Set.mk_mem_prod (hbt hα) hy)
    exact iInf₂_le (f := fun (p : ℝ × X) (_ : p ∈ S) => wβ M p.1 p.2) (α, y) hmem
  refine h1.trans (le_liminf_of_le (by isBoundedDefault) ?_)
  have hev1 : ∀ᶠ n in atTop, b ≤ βs n := hβ.eventually (le_mem_nhds hb)
  have hev2 : interior N ∈ 𝓝 s := interior_mem_nhds.2 hN
  filter_upwards [hev1.prod_inl (𝓝 s), prod_mem_prod (univ_mem) hev2] with p hp1 hp2
  have hNp : N ∈ 𝓝 p.2 := mem_interior_iff_mem_nhds.1 hp2.2
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hNp] with y hy
  exact (biInf_le (fun y => UInf M b y) hy).trans (UInf_mono M hp1 y)

lemma vβ_ne_top (M : Model X A) (hB : CondBLow M) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (x : X) :
    vβ M α x ≠ ⊤ := by
  obtain ⟨β, hβ, hlt⟩ := exists_wβ_lt_top M hB h1 x
  have hm := mβ_lt_top M hB (h0.trans hβ.1) hβ.2
  have : vβ M β x < ⊤ := lt_of_le_of_lt le_tsub_add (ENNReal.add_lt_top.2 ⟨hlt, hm⟩)
  exact (lt_of_le_of_lt (vβ_mono M h0 hβ.1 x) this).ne

lemma wβ_ne_top (M : Model X A) (hB : CondBLow M) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (x : X) :
    wβ M α x ≠ ⊤ :=
  ne_top_of_le_ne_top (vβ_ne_top M hB h0 h1 x) tsub_le_self

lemma wβ_lsc (M : Model X A) (hsel : HasSelector M) (hB : CondBLow M) (hW : CondWStar M)
    [StandardBorelSpace X] [StandardBorelSpace A] {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    LowerSemicontinuous (wβ M α) := by
  have hv : LowerSemicontinuous (vβ M α) := (theorem_2 M hsel hW α h0 h1).1.2.1
  exact Continuous.comp_lowerSemicontinuous (g := fun t => t - mβ M α)
    (ENNReal.continuous_sub_right (mβ M α)) hv (fun _ _ h => tsub_le_tsub_right h _)

lemma Wu_WStar (M : Model X A) (hWu : CondWu M) : CondWStar M := by
  refine ⟨?_, ?_, hWu.2⟩
  · intro p hp y hy
    have hyt : y ≠ ⊤ := ne_top_of_lt hy
    have hK := hWu.1 y.toNNReal
    have hKc : IsClosed {q : X × A | q ∈ graphA M ∧ M.toMDP.cost q.1 q.2 ≤ (y.toNNReal : ℝ≥0∞)} :=
      hK.isClosed
    have hpK : p ∉ {q : X × A | q ∈ graphA M ∧ M.toMDP.cost q.1 q.2 ≤ (y.toNNReal : ℝ≥0∞)} := by
      rintro ⟨-, hq⟩
      rw [ENNReal.coe_toNNReal hyt] at hq
      exact absurd hy (not_lt.2 hq)
    have hev := hKc.isOpen_compl.mem_nhds hpK
    filter_upwards [mem_nhdsWithin_of_mem_nhds hev, self_mem_nhdsWithin] with q hq hqg
    by_contra hc
    rw [not_lt] at hc
    exact hq ⟨hqg, by rw [ENNReal.coe_toNNReal hyt]; exact hc⟩
  · intro xs x as hxs has ⟨C, hC⟩
    have hK := hWu.1 C
    obtain ⟨⟨x', a⟩, ⟨haK, -⟩, φ, hφ, hlim⟩ := hK.tendsto_subseq
      (x := fun n => (xs n, as n)) (fun n => ⟨has n, hC n⟩)
    have hx' : x' = x := tendsto_nhds_unique ((continuous_fst.tendsto _).comp hlim)
      (hxs.comp hφ.tendsto_atTop)
    subst hx'
    refine ⟨a, haK, ?_⟩
    exact ((continuous_snd.tendsto _).comp hlim).mapClusterPt.of_comp hφ.tendsto_atTop

/-- `v_0(x) ≤ ε* + u_α(x)` ((28) and (30) of the paper). -/
lemma v0_le_wβ (M : Model X A) (hsel : HasSelector M) (hB : CondBLow M) (hW : CondWStar M)
    [StandardBorelSpace X] [StandardBorelSpace A] {E : ℝ≥0∞}
    (hE : ∀ α, 0 ≤ α → α < 1 → ENNReal.ofReal (1 - α) * mβ M α ≤ E)
    {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (x : X) : vβ M 0 x ≤ E + wβ M α x := by
  set m := mβ M α
  have hmt : m ≠ ⊤ := (mβ_lt_top M hB h0 h1).ne
  have hT0 := (theorem_2 M hsel hW 0 le_rfl one_pos).2.1.1 x
  have hTα := (theorem_2 M hsel hW α h0 h1).2.1.1 x
  have hvm : ∀ y, m ≤ vβ M α y := fun y => iInf_le (fun y => vβ M α y) y
  have hstep : vβ M 0 x + ENNReal.ofReal α * m ≤ vβ M α x := by
    rw [hTα, hT0, ENNReal.iInf_add]
    refine iInf_mono fun a => ?_
    rw [ENNReal.iInf_add]
    refine iInf_mono fun ha => ?_
    simp only [eta, ENNReal.ofReal_zero, zero_mul, add_zero]
    gcongr
    calc m = ∫⁻ _, m ∂(M.toMDP.q (x, a)) := by simp
      _ ≤ ∫⁻ y, vβ M α y ∂(M.toMDP.q (x, a)) := lintegral_mono hvm
  have hsplit : m = ENNReal.ofReal (1 - α) * m + ENNReal.ofReal α * m := by
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith) h0]; simp
  have hv : vβ M α x = wβ M α x + m := (tsub_add_cancel_of_le (hvm x)).symm
  have hfin : ENNReal.ofReal α * m ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt
  have : vβ M 0 x + ENNReal.ofReal α * m ≤
      (ENNReal.ofReal (1 - α) * m + wβ M α x) + ENNReal.ofReal α * m := by
    calc vβ M 0 x + ENNReal.ofReal α * m ≤ wβ M α x + m := hv ▸ hstep
      _ = _ := by
          rw [add_comm (ENNReal.ofReal (1 - α) * m), add_assoc, ← hsplit]
  have h2 := (ENNReal.add_le_add_iff_right hfin).1 this
  calc vβ M 0 x ≤ ENNReal.ofReal (1 - α) * m + wβ M α x := h2
    _ ≤ E + wβ M α x := by gcongr; exact hE α h0 h1

lemma infCompact_of_le (f g : X → ℝ≥0∞) (hf : LowerSemicontinuous f) (hg : InfCompactOn g Set.univ)
    (E : ℝ≥0∞) (hE : E ≠ ⊤) (hle : ∀ x, g x ≤ E + f x) : InfCompactOn f Set.univ := by
  intro l
  refine (hg (E.toNNReal + l)).of_isClosed_subset ?_ ?_
  · have := hf.isClosed_preimage (l : ℝ≥0∞)
    convert this using 1
    ext y; simp
  · rintro y ⟨-, hy⟩
    refine ⟨trivial, ?_⟩
    calc g y ≤ E + f y := hle y
      _ ≤ E + l := by gcongr
      _ = ((E.toNNReal + l : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_add, ENNReal.coe_toNNReal hE]

end Topo

end FKZL67

open FKZL67 in
theorem solution {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (M : Model X A) (hsel : HasSelector M)
    (hW : CondWStar M) (hB : CondBLow M) :
    ∀ x, (∃ a ∈ M.Aset x, eta M (uAvg M) 1 x a = uStar M (uAvg M) x) ∧
      uStar M (uAvg M) x ≤ gUpper M + uAvg M x := by
  intro x
  have huL : LowerSemicontinuous (uAvg M) :=
    lsc_liminf_prod (𝓝[<] (1 : ℝ)) (fun p : ℝ × X => wβ M p.1 p.2)
  have huF : ∀ y, uAvg M y ≠ ⊤ := uAvg_ne_top M hB
  have hL3 := lemma_3_lsc M hsel hW (uAvg M) ⟨huL, x, huF x⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf, hfe⟩ := hL3.2.1
    exact ⟨f x, hf.2 x, (hfe x).symm⟩
  set L := gUpper M with hLdef
  have hLt : L ≠ ⊤ := (gUpper_lt_top M hB).ne
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεE : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  obtain ⟨α₀, h00, h01, hα₀⟩ := exists_alpha0 M hB hεE
  set B : ℝ≥0∞ := L + ε + uAvg M x with hBdef
  have hBt : B ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hLt, ENNReal.coe_ne_top⟩, huF x⟩
  have hlL : ∀ β, LowerSemicontinuous (uLow M β) := fun β => lsc_liminf_nhds (UInf M β)
  -- the scaled functions `β u̲_β`
  set vfun : ℝ → X → ℝ≥0∞ := fun β y => ENNReal.ofReal β * uLow M β y with hvfun
  have hvL : ∀ β, LowerSemicontinuous (vfun β) := fun β =>
    Continuous.comp_lowerSemicontinuous (g := fun t => ENNReal.ofReal β * t)
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top) (hlL β)
      (fun _ _ h => mul_le_mul_right h _)
  have hvF : ∀ β, β < 1 → vfun β x ≠ ⊤ := fun β hβ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lt_of_le_of_lt (uLow_le_UInf M β x) (UInf_lt_top M hB hβ x)).ne
  have hvη : ∀ β y a, eta M (vfun β) 1 y a =
      M.toMDP.cost y a + ENNReal.ofReal β * ∫⁻ z, uLow M β z ∂(M.toMDP.q (y, a)) := by
    intro β y a
    simp only [eta, ENNReal.ofReal_one, one_mul, hvfun]
    rw [lintegral_const_mul _ (hlL β).measurable]
  -- (33): for `β ∈ [α₀, 1)`, `min_a η^β_{u̲_β}(x, a) ≤ w̄ + ε + u(x)`
  have h33 : ∀ β, α₀ ≤ β → β < 1 → uStar M (vfun β) x ≤ B := by
    intro β hβ0 hβ1
    have hβnn : 0 ≤ β := h00.trans hβ0
    -- (30) together with (32)
    have h30 : ∀ α, β ≤ α → α < 1 → ∀ y,
        (⨅ a ∈ M.Aset y, M.toMDP.cost y a + ENNReal.ofReal α *
          ∫⁻ z, wβ M α z ∂(M.toMDP.q (y, a))) ≤ (L + ε) + wβ M α y := by
      intro α hα hα1 y
      have hα0 : 0 ≤ α := hβnn.trans hα
      set m := mβ M α
      have hmt : m ≠ ⊤ := (mβ_lt_top M hB hα0 hα1).ne
      have hvm : ∀ z, vβ M α z = wβ M α z + m := fun z =>
        (tsub_add_cancel_of_le (iInf_le (fun y => vβ M α y) z)).symm
      have hwm : Measurable (wβ M α) := (wβ_lsc M hsel hB hW hα0 hα1).measurable
      have hT := (theorem_2 M hsel hW α hα0 hα1).2.1.1 y
      have hfin : ENNReal.ofReal α * m ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmt
      have hsplit : m = ENNReal.ofReal (1 - α) * m + ENNReal.ofReal α * m := by
        rw [← add_mul, ← ENNReal.ofReal_add (by linarith) hα0]; simp
      have heq : (⨅ a ∈ M.Aset y, M.toMDP.cost y a + ENNReal.ofReal α *
          ∫⁻ z, wβ M α z ∂(M.toMDP.q (y, a))) + ENNReal.ofReal α * m = vβ M α y := by
        rw [hT, ENNReal.iInf_add]
        refine iInf_congr fun a => ?_
        rw [ENNReal.iInf_add]
        refine iInf_congr fun _ => ?_
        simp only [eta]
        have : ∫⁻ z, vβ M α z ∂(M.toMDP.q (y, a)) = ∫⁻ z, wβ M α z ∂(M.toMDP.q (y, a)) + m := by
          simp_rw [hvm]
          rw [lintegral_add_right _ measurable_const]
          simp
        rw [this, mul_add, add_assoc]
      have : (⨅ a ∈ M.Aset y, M.toMDP.cost y a + ENNReal.ofReal α *
          ∫⁻ z, wβ M α z ∂(M.toMDP.q (y, a))) + ENNReal.ofReal α * m ≤
          (ENNReal.ofReal (1 - α) * m + wβ M α y) + ENNReal.ofReal α * m := by
        rw [heq, hvm y, add_comm (ENNReal.ofReal (1 - α) * m), add_assoc, ← hsplit]
      refine ((ENNReal.add_le_add_iff_right hfin).1 this).trans ?_
      gcongr
      exact (hα₀ α (hβ0.trans hα) hα1).le
    -- (34) pointwise: `H(y) ≤ w̄ + ε + U_β(y)`
    have hH : ∀ y, uStar M (vfun β) y ≤ (L + ε) + UInf M β y := by
      intro y
      unfold UInf
      simp only [ENNReal.add_iInf]
      refine le_iInf₂ fun α hα => le_trans ?_ (h30 α hα.1 hα.2 y)
      unfold uStar
      refine iInf₂_mono fun a _ => ?_
      rw [hvη]
      gcongr
      · exact hα.1
      · exact (uLow_le_UInf M β _).trans (biInf_le (fun α => wβ M α _) hα)
    have hGL : LowerSemicontinuous (uStar M (vfun β)) :=
      (lemma_3_lsc M hsel hW (vfun β) ⟨hvL β, x, hvF β hβ1⟩).1
    set k : X → ℝ≥0∞ := fun y => uStar M (vfun β) y - (L + ε)
    have hk : LowerSemicontinuous k :=
      Continuous.comp_lowerSemicontinuous (g := fun t => t - (L + ε))
        (ENNReal.continuous_sub_right _) hGL (fun _ _ h => tsub_le_tsub_right h _)
    have hkU : ∀ y, k y ≤ UInf M β y := fun y => tsub_le_iff_left.2 (hH y)
    have hkx : k x ≤ uLow M β x :=
      (hk.le_liminf x).trans (liminf_le_liminf (Eventually.of_forall hkU))
    calc uStar M (vfun β) x ≤ k x + (L + ε) := le_tsub_add
      _ ≤ uLow M β x + (L + ε) := by gcongr
      _ ≤ uAvg M x + (L + ε) := by gcongr; exact uLow_le_uAvg M hβ1 x
      _ = B := by rw [hBdef]; ring
  -- minimizers along `β_n ↑ 1`
  set βs : ℕ → ℝ := fun n => 1 - (1 - α₀) / ((n : ℝ) + 2) with hβs
  have hβs0 : ∀ n, α₀ ≤ βs n := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have : (1 - α₀) / ((n : ℝ) + 2) ≤ 1 - α₀ := div_le_self (by linarith) (by linarith)
    simp only [hβs]; linarith
  have hβs1 : ∀ n, βs n < 1 := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have : 0 < (1 - α₀) / ((n : ℝ) + 2) := div_pos (by linarith) h2
    simp only [hβs]; linarith
  have hβlim : Tendsto βs atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => (1 - α₀) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := tendsto_const_nhds (x := 1 - α₀) |>.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
      simpa using this
    simpa [hβs] using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  choose f hf hfe using fun n =>
    (lemma_3_lsc M hsel hW (vfun (βs n)) ⟨hvL _, x, hvF _ (hβs1 n)⟩).2.1
  set as : ℕ → A := fun n => f n x
  have has : ∀ n, as n ∈ M.Aset x := fun n => (hf n).2 x
  have hηB : ∀ n, M.toMDP.cost x (as n) + ENNReal.ofReal (βs n) *
      ∫⁻ z, uLow M (βs n) z ∂(M.toMDP.q (x, as n)) ≤ B := by
    intro n
    rw [← hvη, ← hfe n x]
    exact h33 (βs n) (hβs0 n) (hβs1 n)
  have hcB : ∀ n, M.toMDP.cost x (as n) ≤ (B.toNNReal : ℝ≥0∞) := fun n => by
    rw [ENNReal.coe_toNNReal hBt]; exact le_self_add.trans (hηB n)
  obtain ⟨astar, haA, hcl⟩ := hW.2.1 (fun _ => x) x as tendsto_const_nhds has ⟨_, hcB⟩
  obtain ⟨ψ, hψ, hlim⟩ := hcl.tendsto_subseq
  have hgr : Tendsto (fun k => (x, as (ψ k))) atTop (𝓝[graphA M] (x, astar)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.prodMk_nhds hlim,
      Eventually.of_forall fun k => has (ψ k)⟩
  -- lower semicontinuity of the cost
  have hc : M.toMDP.cost x astar ≤ liminf (fun k => M.toMDP.cost x (as (ψ k))) atTop := by
    refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
    have hev := hgr.eventually ((hW.1 (x, astar) haA) y hy)
    exact le_liminf_of_le (by isBoundedDefault) (hev.mono fun k hk => le_of_lt hk)
  -- (36), via Lemma 4 and Corollary 1
  have hI : ∫⁻ z, uAvg M z ∂(M.toMDP.q (x, astar)) ≤
      liminf (fun k => ∫⁻ z, uLow M (βs (ψ k)) z ∂(M.toMDP.q (x, as (ψ k)))) atTop := by
    letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
    let μ : ProbabilityMeasure X := ⟨M.toMDP.q (x, astar), inferInstance⟩
    let μs : ℕ → ProbabilityMeasure X := fun k => ⟨M.toMDP.q (x, as (ψ k)), inferInstance⟩
    have hμ : Tendsto μs atTop (𝓝 μ) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro g
      exact ((hW.2.2 g) (x, astar) haA).tendsto.comp hgr
    have h4 := SchalAvg.AvgOpt.lemma_2_3_ii μ μs hμ (fun k => uLow M (βs (ψ k)))
      (fun k => (hlL _).measurable)
    refine le_trans (lintegral_mono fun z => ?_) h4
    exact uAvg_le_liminf_seq M (βs ∘ ψ) (hβlim.comp hψ.tendsto_atTop) z
  -- conclusion
  have hfinal : M.toMDP.cost x astar + ∫⁻ z, uAvg M z ∂(M.toMDP.q (x, astar)) ≤ B := by
    refine ENNReal.le_of_forall_lt_one_mul_le fun r hr => ?_
    have hrt : r ≠ ⊤ := ne_top_of_lt hr
    have hev : ∀ᶠ k in atTop, r ≤ ENNReal.ofReal (βs (ψ k)) := by
      have h1 : Tendsto (fun k => ENNReal.ofReal (βs (ψ k))) atTop (𝓝 1) := by
        have := (ENNReal.tendsto_ofReal (hβlim.comp hψ.tendsto_atTop))
        simpa using this
      exact (h1.eventually (lt_mem_nhds hr)).mono fun k hk => hk.le
    calc r * (M.toMDP.cost x astar + ∫⁻ z, uAvg M z ∂(M.toMDP.q (x, astar)))
        ≤ M.toMDP.cost x astar + r * ∫⁻ z, uAvg M z ∂(M.toMDP.q (x, astar)) := by
          rw [mul_add]; gcongr; exact mul_le_of_le_one_left' hr.le
      _ ≤ liminf (fun k => M.toMDP.cost x (as (ψ k))) atTop +
          liminf (fun k => r * ∫⁻ z, uLow M (βs (ψ k)) z ∂(M.toMDP.q (x, as (ψ k)))) atTop := by
          rw [ENNReal.liminf_const_mul_of_ne_top hrt]
          gcongr
      _ ≤ liminf (fun k => M.toMDP.cost x (as (ψ k)) +
          r * ∫⁻ z, uLow M (βs (ψ k)) z ∂(M.toMDP.q (x, as (ψ k)))) atTop :=
          add_le_liminf le_rfl le_rfl
      _ ≤ B := by
          refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
          filter_upwards [hev] with k hk
          refine le_trans ?_ (hηB (ψ k))
          gcongr
  calc uStar M (uAvg M) x ≤ eta M (uAvg M) 1 x astar := biInf_le _ haA
    _ = M.toMDP.cost x astar + ∫⁻ z, uAvg M z ∂(M.toMDP.q (x, astar)) := by simp [eta]
    _ ≤ B := hfinal
    _ = L + uAvg M x + ε := by rw [hBdef]; ring
