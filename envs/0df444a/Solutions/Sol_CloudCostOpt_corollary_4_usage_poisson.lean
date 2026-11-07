-- Prove2me | solution 1 for CloudCostOpt.corollary_4_usage_poisson
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T17:06:39.502299+00:00
-- url     : https://prove2.me/submissions/0574075c-3333-4399-9590-2ceb6e5c405e

import Mathlib
import Definitions.Def_CloudCostOpt_piHat
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_rateX
import Definitions.Def_CloudCostOpt_stateAt
import Definitions.Def_CloudCostOpt_sampleMeasure
import Definitions.Def_CloudCostOpt_Standing

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- G1: under a product measure, a function of the coordinates in `T` and a function of the
coordinates outside `T` are independent. -/
theorem g_split {ι α : Type*} [MeasurableSpace α] (μ : ι → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] (a0 : α) (T : Set ι)
    (A B : (ι → α) → ℝ≥0∞) (hA : Measurable A) (hB : Measurable B)
    (hAT : ∀ x y : ι → α, (∀ p ∈ T, x p = y p) → A x = A y)
    (hBT : ∀ x y : ι → α, (∀ p ∉ T, x p = y p) → B x = B y) :
    ∫⁻ x, A x * B x ∂(Measure.infinitePi μ) =
      (∫⁻ x, A x ∂(Measure.infinitePi μ)) * ∫⁻ x, B x ∂(Measure.infinitePi μ) := by
  classical
  let m : ι → MeasurableSpace (ι → α) := fun p =>
    MeasurableSpace.comap (fun x : ι → α => x p) inferInstance
  have hiI : iIndep m (Measure.infinitePi μ) := by
    have := iIndepFun_infinitePi (P := μ) (X := fun _ (u : α) => u) (fun _ => measurable_id)
    exact (iIndepFun_iff_iIndep _ _ _).1 this
  have hI := indep_iSup_of_disjoint (fun p => (measurable_pi_apply p).comap_le) hiI
    (disjoint_compl_right (a := T))
  have hproj : ∀ (T' : Set ι) [DecidablePred (· ∈ T')], Measurable[⨆ p ∈ T', m p]
      (fun x : ι → α => fun p => if p ∈ T' then x p else a0) := by
    intro T' _
    let _ : MeasurableSpace (ι → α) := ⨆ p ∈ T', m p
    refine measurable_pi_lambda _ fun p => ?_
    by_cases h : p ∈ T'
    · simp only [h, if_true]
      exact (comap_measurable (fun x : ι → α => x p)).mono
        (le_iSup₂ (f := fun p (_ : p ∈ T') => m p) p h) le_rfl
    · simp only [h, if_false]; exact measurable_const
  have hle : ∀ T' : Set ι, (⨆ p ∈ T', m p) ≤ MeasurableSpace.pi :=
    fun T' => iSup₂_le fun p _ => (measurable_pi_apply p).comap_le
  have hA' : Measurable[⨆ p ∈ T, m p] A := by
    have : A = A ∘ (fun x : ι → α => fun p => if p ∈ T then x p else a0) :=
      funext fun x => hAT _ _ (fun p hp => by simp [hp])
    rw [this]; exact hA.comp (hproj T)
  have hB' : Measurable[⨆ p ∈ Tᶜ, m p] B := by
    have : B = B ∘ (fun x : ι → α => fun p => if p ∈ Tᶜ then x p else a0) :=
      funext fun x => hBT _ _ (fun p hp => by simp [hp])
    rw [this]; exact hB.comp (hproj Tᶜ)
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (hle T) (hle Tᶜ) hI hA' hB'

/-- G2: functions of distinct coordinates of a product measure: the integral of the product is
the product of the integrals. -/
theorem g_prodq {ι α κ : Type*} [MeasurableSpace α] (μ : ι → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)]
    (a0 : α) (q : κ → ι) (hq : Function.Injective q) (f : κ → α → ℝ≥0∞)
    (hf : ∀ a, Measurable (f a)) (F : Finset κ) :
    ∫⁻ x, ∏ a ∈ F, f a (x (q a)) ∂(Measure.infinitePi μ) =
      ∏ a ∈ F, ∫⁻ v, f a v ∂(μ (q a)) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert b F hb ih =>
    rw [Finset.prod_insert hb, ← ih]
    simp_rw [Finset.prod_insert hb]
    rw [g_split μ a0 {q b} (fun x => f b (x (q b)))
      (fun x => ∏ a ∈ F, f a (x (q a)))
      ((hf b).comp (measurable_pi_apply _))
      (Finset.measurable_prod _ fun a _ => (hf a).comp (measurable_pi_apply _))
      (fun x y h => by rw [h (q b) rfl])
      (fun x y h => Finset.prod_congr rfl fun a ha' => by
        rw [h (q a) (fun hmem => hb (by rw [← hq (Set.mem_singleton_iff.1 hmem)]; exact ha'))])]
    congr 1
    exact (measurePreserving_eval_infinitePi μ (q b)).lintegral_comp (hf b)

/-- G2, i.i.d. form -/
theorem g_prodqh {ι α κ : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (a0 : α) (q : κ → ι) (hq : Function.Injective q) (f : κ → α → ℝ≥0∞)
    (hf : ∀ a, Measurable (f a)) (F : Finset κ) :
    ∫⁻ x, ∏ a ∈ F, f a (x (q a)) ∂(Measure.infinitePi fun _ : ι => ν) =
      ∏ a ∈ F, ∫⁻ v, f a v ∂ν :=
  g_prodq (fun _ : ι => ν) a0 q hq f hf F

/-- the probability generating function of the Poisson law -/
theorem g_pois_pgf (r z : ℝ≥0) :
    ∫⁻ k, (z : ℝ≥0∞) ^ k ∂(poissonMeasure r) = ENNReal.ofReal (Real.exp (r * ((z : ℝ) - 1))) := by
  have e : ∫⁻ k, (z : ℝ≥0∞) ^ k ∂(poissonMeasure r) = ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) * (z : ℝ≥0∞) ^ n := by
    rw [poissonMeasure, lintegral_sum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hs : HasSum (fun n : ℕ => ((r : ℝ) * z) ^ n / (Nat.factorial n : ℝ))
      (Real.exp (r * z)) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have h2 : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) *
      (z : ℝ≥0∞) ^ n
      = ENNReal.ofReal (Real.exp (-r) * (((r : ℝ) * z) ^ n / (Nat.factorial n : ℝ))) := by
    intro n
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; rw [mul_pow]; ring
  rw [e, tsum_congr h2, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hs.summable.mul_left _), tsum_mul_left, hs.tsum_eq, ← Real.exp_add]
  congr 2; ring

/-- index shift on `range m`, multiplicative form -/
theorem g_shift {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∏ l ∈ Finset.range m, (if l = 0 then 1 else f (l - 1)) =
      ∏ l ∈ Finset.range m, (if l + 1 < m then f l else 1) := by
  rcases m with _ | m
  · simp
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, lt_irrefl, mul_one,
    if_true]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [if_pos (by simp only [Finset.mem_range] at hl; omega)]

/-- index shift on `range m`, additive form -/
theorem g_shift_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ l ∈ Finset.range m, (if l = 0 then 0 else f (l - 1)) =
      ∑ l ∈ Finset.range m, (if l + 1 < m then f l else 0) := by
  rcases m with _ | m
  · simp
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, lt_irrefl, add_zero,
    if_true]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [if_pos (by simp only [Finset.mem_range] at hl; omega)]

/-- B: freezing the past.  `X` depends only on the coordinates in `T`; the fresh coordinates
`q c k` lie outside `T` and are distinct. -/
theorem g_freeze {ι α κ : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (a0 : α) (T : Set ι) (C : Finset κ) (X : (ι → α) → κ → ℕ)
    (hX : ∀ c, Measurable fun x => X x c)
    (hXT : ∀ x y : ι → α, (∀ p ∈ T, x p = y p) → ∀ c, X x c = X y c)
    (q : κ → ℕ → ι) (hq : Function.Injective (fun p : κ × ℕ => q p.1 p.2))
    (hqT : ∀ c k, q c k ∉ T)
    (f : κ → α → ℝ≥0∞) (hf : ∀ c, Measurable (f c)) :
    ∫⁻ x, ∏ c ∈ C, ∏ k ∈ Finset.range (X x c), f c (x (q c k))
        ∂(Measure.infinitePi fun _ : ι => ν) =
      ∫⁻ x, ∏ c ∈ C, (∫⁻ v, f c v ∂ν) ^ (X x c) ∂(Measure.infinitePi fun _ : ι => ν) := by
  classical
  let E : (C → ℕ) → (ι → α) → ℝ≥0∞ := fun m x => if (fun c : C => X x c) = m then 1 else 0
  have hXm : Measurable fun x => (fun c : C => X x c) := measurable_pi_lambda _ fun c => hX c
  have hE : ∀ m, Measurable (E m) := fun m =>
    Measurable.ite (hXm (measurableSet_singleton m)) measurable_const measurable_const
  have hexp : ∀ (G : (C → ℕ) → ℝ≥0∞) x, G (fun c : C => X x c) = ∑' m, E m x * G m := by
    intro G x
    rw [tsum_eq_single (fun c : C => X x c) (fun m hm => by simp [E, Ne.symm hm])]
    simp [E]
  have hL : ∀ x, ∏ c ∈ C, ∏ k ∈ Finset.range (X x c), f c (x (q c k)) =
      ∑' m : C → ℕ, E m x * ∏ c : C, ∏ k ∈ Finset.range (m c), f c (x (q c k)) := by
    intro x
    rw [← hexp (fun m => ∏ c : C, ∏ k ∈ Finset.range (m c), f c (x (q c k))) x]
    exact (Finset.prod_coe_sort C (fun c => ∏ k ∈ Finset.range (X x c), f c (x (q c k)))).symm
  have hR : ∀ x, ∏ c ∈ C, (∫⁻ v, f c v ∂ν) ^ (X x c) =
      ∑' m : C → ℕ, E m x * ∏ c : C, (∫⁻ v, f c v ∂ν) ^ (m c) := by
    intro x
    rw [← hexp (fun m => ∏ c : C, (∫⁻ v, f c v ∂ν) ^ (m c)) x]
    exact (Finset.prod_coe_sort C (fun c => (∫⁻ v, f c v ∂ν) ^ (X x c))).symm
  simp_rw [hL, hR]
  have hFm : ∀ m : C → ℕ, Measurable fun x : ι → α =>
      ∏ c : C, ∏ k ∈ Finset.range (m c), f c (x (q c k)) :=
    fun m => Finset.measurable_prod _ fun c _ => Finset.measurable_prod _ fun k _ =>
      (hf c).comp (measurable_pi_apply _)
  rw [lintegral_tsum (f := fun m x => E m x * ∏ c : C, ∏ k ∈ Finset.range (m c), f c (x (q c k)))
      (fun m => ((hE m).mul (hFm m)).aemeasurable),
    lintegral_tsum (f := fun m x => E m x * ∏ c : C, (∫⁻ v, f c v ∂ν) ^ (m c))
      (fun m => ((hE m).mul measurable_const).aemeasurable)]
  refine tsum_congr fun m => ?_
  rw [lintegral_mul_const _ (hE m)]
  rw [g_split (fun _ : ι => ν) a0 T (E m) _ (hE m) (hFm m)
    (fun x y h => by
      have : (fun c : C => X x c) = (fun c : C => X y c) := funext fun c => hXT x y h c
      simp only [E, this])
    (fun x y h => Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun k _ => by
      rw [h (q c k) (hqT c k)])]
  congr 1
  have hsig : ∀ x : ι → α, ∏ c : C, ∏ k ∈ Finset.range (m c), f c (x (q c k)) =
      ∏ p ∈ (Finset.univ : Finset C).sigma (fun c => Finset.range (m c)),
        f p.1 (x (q p.1 p.2)) := fun x =>
    (Finset.prod_sigma (Finset.univ : Finset C) (fun c => Finset.range (m c))
      (fun p => f p.1 (x (q p.1 p.2)))).symm
  simp_rw [hsig]
  rw [g_prodqh ν a0 (fun p : (Σ _ : C, ℕ) => q p.1 p.2) (fun p p' h => by
      obtain ⟨⟨c, hc⟩, k⟩ := p
      obtain ⟨⟨c', hc'⟩, k'⟩ := p'
      have := hq (a₁ := (c, k)) (a₂ := (c', k')) h
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rfl)
    (fun p => f p.1) (fun p => hf p.1), Finset.prod_sigma (Finset.univ : Finset C)
      (fun c => Finset.range (m c)) (fun p => ∫⁻ v, f p.1 v ∂ν)]
  refine Finset.prod_congr rfl fun c _ => ?_
  exact (Finset.prod_const (s := Finset.range (m c)) (∫⁻ v, f c v ∂ν)).trans
    (by rw [Finset.card_range])

/-! ## Part 1: pathwise dynamics of `π*` -/

/-- number of the `x` orders of cell `(i,s,l)` sent to `j` in period `t` whose step succeeds -/
noncomputable def c1Succ (S : System)
    (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval)
    (t : ℕ) (i : Fin S.I) (s l : ℕ) (j : Fin (S.J + 1)) (x : ℕ) : ℕ :=
  ((Finset.range x).filter fun k => ((U (i, t, s, l, j, k) : ℝ) < S.β i j)).card

/-- number of those whose step fails -/
noncomputable def c1Fail (S : System)
    (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval)
    (t : ℕ) (i : Fin S.I) (s l : ℕ) (j : Fin (S.J + 1)) (x : ℕ) : ℕ :=
  ((Finset.range x).filter fun k => ¬ ((U (i, t, s, l, j, k) : ℝ) < S.β i j)).card

theorem c1_cellSucc (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval) (t n : ℕ)
    (h : Fin (n + 1) → State S) (i : Fin S.I) (s l : ℕ) :
    cellSucc S U t i s l ((piStar S sel lam).a n h i s l) =
      c1Succ S U t i s l (sel.jStar i s l) (h (Fin.last n) i s l) := by
  unfold cellSucc c1Succ
  rw [Finset.sum_eq_single (sel.jStar i s l)]
  · simp [piStar, piHat]
  · intro j _ hj
    simp [piStar, piHat, hj]
  · simp

theorem c1_cellFail (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (U : Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ → unitInterval) (t n : ℕ)
    (h : Fin (n + 1) → State S) (i : Fin S.I) (s l : ℕ) :
    cellFail S U t i s l ((piStar S sel lam).a n h i s l) =
      c1Fail S U t i s l (sel.jStar i s l) (h (Fin.last n) i s l) := by
  unfold cellFail
  rw [c1_cellSucc]
  have hsum : ∑ j, (piStar S sel lam).a n h i s l j = h (Fin.last n) i s l := by
    simp [piStar, piHat]
  rw [hsum]
  have := Finset.card_filter_add_card_filter_not
    (s := Finset.range (h (Fin.last n) i s l))
    (fun k => ((U (i, t, s, l, sel.jStar i s l, k) : ℝ) < S.β i (sel.jStar i s l)))
  simp only [Finset.card_range] at this
  unfold c1Succ c1Fail
  omega

theorem c1_st_zero (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S)
    (n : ℕ) (i : Fin S.I) (l : ℕ) :
    stateAt S (piStar S sel lam) ω (n + 1) i 0 l =
      if S.L i ≤ l then 0 else if l = 0 then ω.1 (i, n + 1) else 0 := by
  simp only [stateAt, history, Fin.snoc_last]

theorem c1_st_succ (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S)
    (n : ℕ) (i : Fin S.I) (s l : ℕ) :
    stateAt S (piStar S sel lam) ω (n + 1) i (s + 1) l =
      if S.L i ≤ l then 0 else
        (if l = 0 then 0 else c1Succ S ω.2 (n + 1) i s (l - 1) (sel.jStar i s (l - 1))
            (stateAt S (piStar S sel lam) ω n i s (l - 1))) +
        c1Fail S ω.2 (n + 1) i s l (sel.jStar i s l) (stateAt S (piStar S sel lam) ω n i s l) := by
  simp only [stateAt, history, Fin.snoc_last, c1_cellSucc, c1_cellFail]

theorem c1_st_old (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) :
    ∀ n i s l, n ≤ s → stateAt S (piStar S sel lam) ω n i s l = 0 := by
  intro n
  induction n with
  | zero => intro i s l _; simp [stateAt, history]
  | succ n ih =>
    intro i s l hs
    obtain ⟨s, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    rw [c1_st_succ, ih i s (l - 1) (by omega), ih i s l (by omega)]
    simp [c1Succ, c1Fail]


/-- index type of the uniforms -/
abbrev c1Idx (S : System) : Type := Fin S.I × ℕ × ℕ × ℕ × Fin (S.J + 1) × ℕ

/-- the law of the uniforms -/
noncomputable def c1μU (S : System) : Measure (c1Idx S → unitInterval) :=
  Measure.infinitePi fun _ : c1Idx S => (volume : Measure unitInterval)

/-- the σ-algebra of the uniforms of periods `≤ n` -/
noncomputable def c1MA (S : System) (n : ℕ) : MeasurableSpace (c1Idx S → unitInterval) :=
  ⨆ p ∈ {p : c1Idx S | p.2.1 ≤ n},
    MeasurableSpace.comap (fun U : c1Idx S → unitInterval => U p) inferInstance

theorem c1_meas_natfun {α : Type*} [MeasurableSpace α] {γ : Type*} [MeasurableSpace γ]
    (F : ℕ → α → γ) (hF : ∀ x, Measurable (F x)) (X : α → ℕ) (hX : Measurable X) :
    Measurable fun a => F (X a) a :=
  (measurable_from_prod_countable_left (f := fun p : α × ℕ => F p.2 p.1) fun y => hF y).comp
    (measurable_id.prodMk hX)

theorem c1_meas_cnt (S : System) (q : ℕ → c1Idx S) (P : unitInterval → Prop) [DecidablePred P]
    (hP : MeasurableSet {u | P u}) (X : Omega S → ℕ) (hX : Measurable X) :
    Measurable fun ω : Omega S => ((Finset.range (X ω)).filter fun k => P (ω.2 (q k))).card := by
  refine c1_meas_natfun (fun x (ω : Omega S) => ((Finset.range x).filter fun k => P (ω.2 (q k))).card)
    (fun x => ?_) X hX
  simp only [Finset.card_filter]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.ite (hP.preimage ((measurable_pi_apply (q k)).comp measurable_snd))
    measurable_const measurable_const

theorem c1_meas_st (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    ∀ n i s l, Measurable fun ω : Omega S => stateAt S (piStar S sel lam) ω n i s l := by
  intro n
  induction n with
  | zero => intro i s l; simp only [stateAt, history]; exact measurable_const
  | succ n ih =>
    intro i s l
    rcases s with _ | s
    · by_cases h1 : S.L i ≤ l
      · simp only [c1_st_zero, h1, if_true]; exact measurable_const
      · by_cases h2 : l = 0
        · subst h2
          simp only [c1_st_zero, h1, if_false, if_true]
          exact (measurable_pi_apply _).comp measurable_fst
        · simp only [c1_st_zero, h1, h2, if_false]; exact measurable_const
    · simp only [c1_st_succ]
      by_cases h1 : S.L i ≤ l
      · simp only [h1, if_true]; exact measurable_const
      simp only [h1, if_false]
      refine Measurable.add ?_ ?_
      · by_cases h2 : l = 0
        · simp only [h2, if_true]; exact measurable_const
        · simp only [h2, if_false]
          exact c1_meas_cnt S (fun k => (i, n + 1, s, l - 1, sel.jStar i s (l - 1), k))
            (fun u => (u : ℝ) < S.β i (sel.jStar i s (l - 1)))
            (measurableSet_lt measurable_subtype_coe measurable_const) _ (ih i s (l - 1))
      · exact c1_meas_cnt S (fun k => (i, n + 1, s, l, sel.jStar i s l, k))
          (fun u => ¬ (u : ℝ) < S.β i (sel.jStar i s l))
          (measurableSet_lt measurable_subtype_coe measurable_const).compl _ (ih i s l)

theorem c1Succ_congr (S : System) (U U' : c1Idx S → unitInterval) (t : ℕ) (i : Fin S.I)
    (s l : ℕ) (j : Fin (S.J + 1)) (x : ℕ)
    (h : ∀ k, U (i, t, s, l, j, k) = U' (i, t, s, l, j, k)) :
    c1Succ S U t i s l j x = c1Succ S U' t i s l j x := by
  unfold c1Succ; simp only [h]

theorem c1Fail_congr (S : System) (U U' : c1Idx S → unitInterval) (t : ℕ) (i : Fin S.I)
    (s l : ℕ) (j : Fin (S.J + 1)) (x : ℕ)
    (h : ∀ k, U (i, t, s, l, j, k) = U' (i, t, s, l, j, k)) :
    c1Fail S U t i s l j x = c1Fail S U' t i s l j x := by
  unfold c1Fail; simp only [h]

theorem c1_dep (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    ∀ n (N : Fin S.I × ℕ → ℕ) (U U' : c1Idx S → unitInterval),
      (∀ p : c1Idx S, p.2.1 ≤ n → U p = U' p) →
      ∀ i s l, stateAt S (piStar S sel lam) (N, U) n i s l =
        stateAt S (piStar S sel lam) (N, U') n i s l := by
  intro n
  induction n with
  | zero => intro N U U' _ i s l; simp [stateAt, history]
  | succ n ih =>
    intro N U U' h i s l
    rcases s with _ | s
    · simp only [c1_st_zero]
    · simp only [c1_st_succ]
      rw [ih N U U' (fun p hp => h p (by omega)) i s (l - 1),
        ih N U U' (fun p hp => h p (by omega)) i s l,
        c1Succ_congr S U U' _ i s (l - 1) _ _ (fun k => h _ le_rfl),
        c1Fail_congr S U U' _ i s l _ _ (fun k => h _ le_rfl)]

theorem c1_poisson_mean (r : ℝ≥0) : ∫⁻ k, (k : ℝ≥0∞) ∂(poissonMeasure r) = r := by
  have e : ∫⁻ k, (k : ℝ≥0∞) ∂(poissonMeasure r) = ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) * (n : ℝ≥0∞) := by
    rw [poissonMeasure, lintegral_sum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [e, tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  have h : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) *
      ((n + 1 : ℕ) : ℝ≥0∞)
      = (r : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.factorial_succ]; push_cast
    have : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [tsum_congr h, ENNReal.tsum_mul_left,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hasSum_one_poissonMeasure r).summable,
    (hasSum_one_poissonMeasure r).tsum_eq]
  simp
theorem c1_vol_lt (S : System) (hS : Standing S) (i : Fin S.I) (j : Fin (S.J + 1)) :
    volume {u : unitInterval | (u : ℝ) < S.β i j} = ENNReal.ofReal (S.β i j) := by
  have : {u : unitInterval | (u : ℝ) < S.β i j} =
      Set.Iio (⟨S.β i j, hS.β_nonneg i j, hS.β_le_one i j⟩ : unitInterval) := Set.ext fun u => Iff.rfl
  rw [this, unitInterval.volume_Iio]

theorem c1_vol_nlt (S : System) (hS : Standing S) (i : Fin S.I) (j : Fin (S.J + 1)) :
    volume {u : unitInterval | ¬ (u : ℝ) < S.β i j} = ENNReal.ofReal (1 - S.β i j) := by
  have : {u : unitInterval | ¬ (u : ℝ) < S.β i j} = {u : unitInterval | (u : ℝ) < S.β i j}ᶜ := rfl
  rw [this, prob_compl_eq_one_sub (measurableSet_lt measurable_subtype_coe measurable_const),
    c1_vol_lt S hS, ENNReal.ofReal_sub _ (hS.β_nonneg i j), ENNReal.ofReal_one]
/-! ## Part 8: the policy `π̂`: stability and the closed form (8) of its `ℙ_LB` cost -/

theorem e8_hist (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) :
    ∀ n, history S (piHat S sel) ω n = history S (piStar S sel lam) ω n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [history, ih]; rfl

theorem e8_st (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) (n : ℕ) :
    stateAt S (piHat S sel) ω n = stateAt S (piStar S sel lam) ω n := by
  simp only [stateAt, e8_hist S sel lam ω n]
theorem e8_rateX_zero (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (i : Fin S.I) :
    ∀ s l, s < l → rateX S sel lam i s l = 0 := by
  intro s
  induction s with
  | zero => intro l hl; simp [rateX]; intro _ h; omega
  | succ s ih =>
    intro l hl
    simp only [rateX]
    rw [ih (l - 1) (by omega), ih l (by omega)]
    simp
theorem e8_mu (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (j : Fin S.J) :
    mu S sel lam j = ∑ i, ∑' s, ∑ l ∈ Finset.range (S.L i),
      (if j.succ = sel.jStar i s l then (rateX S sel lam i s l : ℝ≥0∞) else 0) := by
  unfold mu
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (ENNReal.tsum_prod (f := fun s l => if l ≤ s ∧ l < S.L i ∧ sel.jStar i s l = j.succ then
    (rateX S sel lam i s l : ℝ≥0∞) else 0)).trans ?_
  refine tsum_congr fun s => ?_
  rw [tsum_eq_sum (s := Finset.range (S.L i)) (fun l hl => by
    rw [if_neg]; rintro ⟨_, h, _⟩; exact hl (Finset.mem_range.2 h))]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  by_cases hls : l ≤ s
  · by_cases hj : sel.jStar i s l = j.succ
    · rw [if_pos ⟨hls, hl', hj⟩, if_pos hj.symm]
    · rw [if_neg (fun h => hj h.2.2), if_neg (fun h => hj h.symm)]
  · rw [e8_rateX_zero S sel lam i s l (by omega)]
    simp


/-! ## cdeb0e97 part M: the probability generating function of the state under π* -/

/-- a bound for all `Lᵢ` -/
def cdLm (S : System) : ℕ := ∑ i, S.L i

theorem cd_L_le (S : System) (i : Fin S.I) : S.L i ≤ cdLm S :=
  Finset.single_le_sum (f := S.L) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem cd_st_L (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (ω : Omega S) :
    ∀ n i s l, S.L i ≤ l → stateAt S (piStar S sel lam) ω n i s l = 0 := by
  intro n i s l h
  rcases n with _ | n
  · simp [stateAt, history]
  · rcases s with _ | s
    · rw [c1_st_zero, if_pos h]
    · rw [c1_st_succ, if_pos h]

theorem cd_rx_L (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (i : Fin S.I) (s l : ℕ)
    (h : S.L i ≤ l) : rateX S sel lam i s l = 0 := by
  rcases s with _ | s <;> simp [rateX, h]

theorem cd_depN (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    ∀ n (N N' : Fin S.I × ℕ → ℕ) (U : c1Idx S → unitInterval),
      (∀ p : Fin S.I × ℕ, p.2 ≤ n → N p = N' p) →
      ∀ i s l, stateAt S (piStar S sel lam) (N, U) n i s l =
        stateAt S (piStar S sel lam) (N', U) n i s l := by
  intro n
  induction n with
  | zero => intro N N' U _ i s l; simp [stateAt, history]
  | succ n ih =>
    intro N N' U h i s l
    rcases s with _ | s
    · simp only [c1_st_zero, h (i, n + 1) le_rfl]
    · simp only [c1_st_succ]
      rw [ih N N' U (fun p hp => h p (by omega)) i s (l - 1),
        ih N N' U (fun p hp => h p (by omega)) i s l]

/-- the variable at the cell reached by a success -/
noncomputable def cda (S : System) (z : Fin S.I → ℕ → ℕ → ℝ≥0) (i : Fin S.I) (s l : ℕ) : ℝ≥0 :=
  if l + 1 < S.L i then z i (s + 1) (l + 1) else 1

/-- the per-order factor of a cell: success → `cda`, failure → `z (s+1) l` -/
noncomputable def cdh (S : System) (sel : Selection S) (z : Fin S.I → ℕ → ℕ → ℝ≥0)
    (i : Fin S.I) (s l : ℕ) (v : unitInterval) : ℝ≥0∞ :=
  if (v : ℝ) < S.β i (sel.jStar i s l) then (cda S z i s l : ℝ≥0∞) else (z i (s + 1) l : ℝ≥0∞)

/-- its mean `β cda + (1 - β) z(s+1,l)` -/
noncomputable def cdg (S : System) (sel : Selection S) (z : Fin S.I → ℕ → ℕ → ℝ≥0)
    (i : Fin S.I) (s l : ℕ) : ℝ≥0 :=
  (S.β i (sel.jStar i s l)).toNNReal * cda S z i s l +
    (1 - S.β i (sel.jStar i s l)).toNNReal * z i (s + 1) l

theorem cd_meas_h (S : System) (sel : Selection S) (z : Fin S.I → ℕ → ℕ → ℝ≥0)
    (i : Fin S.I) (s l : ℕ) : Measurable (cdh S sel z i s l) :=
  Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const)
    measurable_const measurable_const

theorem cd_int_h (S : System) (hS : Standing S) (sel : Selection S)
    (z : Fin S.I → ℕ → ℕ → ℝ≥0) (i : Fin S.I) (s l : ℕ) :
    ∫⁻ v, cdh S sel z i s l v = (cdg S sel z i s l : ℝ≥0∞) := by
  have hm : MeasurableSet {v : unitInterval | (v : ℝ) < S.β i (sel.jStar i s l)} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have e : ∀ v, cdh S sel z i s l v =
      {v : unitInterval | (v : ℝ) < S.β i (sel.jStar i s l)}.indicator
        (fun _ => (cda S z i s l : ℝ≥0∞)) v +
      {v : unitInterval | ¬ (v : ℝ) < S.β i (sel.jStar i s l)}.indicator
        (fun _ => (z i (s + 1) l : ℝ≥0∞)) v := by
    intro v
    by_cases h : (v : ℝ) < S.β i (sel.jStar i s l)
    · simp [cdh, h, Set.indicator, not_le.mpr h]
    · simp [cdh, h, Set.indicator]
  have hm' : MeasurableSet {v : unitInterval | ¬ (v : ℝ) < S.β i (sel.jStar i s l)} := hm.compl
  simp_rw [e]
  rw [lintegral_add_left (measurable_const.indicator hm), lintegral_indicator_const hm,
    lintegral_indicator_const hm', c1_vol_lt S hS, c1_vol_nlt S hS]
  simp only [cdg, ENNReal.ofReal]
  push_cast
  ring

/-- pathwise one-step identity for the generating product -/
theorem cd_path (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (z : Fin S.I → ℕ → ℕ → ℝ≥0) (ω : Omega S) :
    ∏ i, ∏ s ∈ Finset.range (n + 1), ∏ l ∈ Finset.range (cdLm S),
        (z i s l : ℝ≥0∞) ^ (stateAt S (piStar S sel lam) ω (n + 1) i s l) =
      (∏ i, (z i 0 0 : ℝ≥0∞) ^ (ω.1 (i, n + 1))) *
        ∏ i, ∏ s ∈ Finset.range n, ∏ l ∈ Finset.range (cdLm S),
          ∏ k ∈ Finset.range (stateAt S (piStar S sel lam) ω n i s l),
            cdh S sel z i s l (ω.2 (i, n + 1, s, l, sel.jStar i s l, k)) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hL1 := hS.one_le_L i
  have hLm := cd_L_le S i
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  · rw [Finset.prod_eq_single 0]
    · rw [c1_st_zero, if_neg (by omega), if_pos rfl]
    · intro l _ hl; rw [c1_st_zero]; split_ifs <;> simp
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · refine Finset.prod_congr rfl fun s _ => ?_
    have hR : ∀ l, ∏ k ∈ Finset.range (stateAt S (piStar S sel lam) ω n i s l),
        cdh S sel z i s l (ω.2 (i, n + 1, s, l, sel.jStar i s l, k)) =
        (cda S z i s l : ℝ≥0∞) ^ (c1Succ S ω.2 (n + 1) i s l (sel.jStar i s l)
          (stateAt S (piStar S sel lam) ω n i s l)) *
        (z i (s + 1) l : ℝ≥0∞) ^ (c1Fail S ω.2 (n + 1) i s l (sel.jStar i s l)
          (stateAt S (piStar S sel lam) ω n i s l)) := by
      intro l
      unfold cdh
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      rfl
    have hFl0 : ∀ l, S.L i ≤ l → c1Fail S ω.2 (n + 1) i s l (sel.jStar i s l)
        (stateAt S (piStar S sel lam) ω n i s l) = 0 := by
      intro l hl
      simp only [cd_st_L S sel lam ω n i s l hl, c1Fail, Finset.range_zero,
        Finset.filter_empty, Finset.card_empty]
    have hLx : ∀ l, stateAt S (piStar S sel lam) ω (n + 1) i (s + 1) l =
        (if l = 0 ∨ S.L i ≤ l then 0 else c1Succ S ω.2 (n + 1) i s (l - 1)
          (sel.jStar i s (l - 1)) (stateAt S (piStar S sel lam) ω n i s (l - 1))) +
        c1Fail S ω.2 (n + 1) i s l (sel.jStar i s l) (stateAt S (piStar S sel lam) ω n i s l) := by
      intro l
      rw [c1_st_succ]
      by_cases h1 : S.L i ≤ l
      · rw [if_pos h1, if_pos (Or.inr h1), hFl0 l h1]
      · rw [if_neg h1]
        by_cases h2 : l = 0
        · rw [if_pos h2, if_pos (Or.inl h2)]
        · rw [if_neg h2, if_neg (by tauto)]
    simp_rw [hR, hLx, pow_add, Finset.prod_mul_distrib]
    congr 1
    let F : ℕ → ℝ≥0∞ := fun l' => (z i (s + 1) (l' + 1) : ℝ≥0∞) ^
      (if S.L i ≤ l' + 1 then 0 else c1Succ S ω.2 (n + 1) i s l' (sel.jStar i s l')
        (stateAt S (piStar S sel lam) ω n i s l'))
    have e1 : ∏ l ∈ Finset.range (cdLm S),
        (z i (s + 1) l : ℝ≥0∞) ^ (if l = 0 ∨ S.L i ≤ l then 0 else c1Succ S ω.2 (n + 1) i s (l - 1)
          (sel.jStar i s (l - 1)) (stateAt S (piStar S sel lam) ω n i s (l - 1))) =
        ∏ l ∈ Finset.range (cdLm S), (if l = 0 then 1 else F (l - 1)) := by
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases h2 : l = 0
      · simp [h2]
      · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        simp [F]
    rw [e1, g_shift F]
    refine Finset.prod_congr rfl fun l _ => ?_
    by_cases h3 : l + 1 < S.L i
    · rw [if_pos (by omega)]
      simp [F, cda, h3, show ¬ S.L i ≤ l + 1 by omega]
    · simp only [cda, if_neg h3, ENNReal.coe_one, one_pow]
      split_ifs with h4
      · simp [F, show S.L i ≤ l + 1 by omega]
      · rfl


/-! ## cdeb0e97 part W: the generating function by induction -/

/-- the generating product of the state at time `n` -/
noncomputable def cdPhi (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (z : Fin S.I → ℕ → ℕ → ℝ≥0) (ω : Omega S) : ℝ≥0∞ :=
  ∏ i, ∏ s ∈ Finset.range n, ∏ l ∈ Finset.range (cdLm S),
    (z i s l : ℝ≥0∞) ^ (stateAt S (piStar S sel lam) ω n i s l)

/-- its exponent -/
noncomputable def cdE (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (z : Fin S.I → ℕ → ℕ → ℝ≥0) : ℝ :=
  ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (cdLm S),
    (rateX S sel lam i s l : ℝ) * ((z i s l : ℝ) - 1)

theorem cd_meas_Phi (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (z : Fin S.I → ℕ → ℕ → ℝ≥0) : Measurable (cdPhi S sel lam n z) := by
  unfold cdPhi
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun s _ =>
    Finset.measurable_prod _ fun l _ => ?_
  exact (measurable_from_nat (f := fun k : ℕ => (z i s l : ℝ≥0∞) ^ k)).comp
    (c1_meas_st S sel lam n i s l)

/-- one rate step, summed over `l`, against a weight `w` -/
theorem cd_rate_step (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (i : Fin S.I) (s : ℕ) (w : ℕ → ℝ) :
    ∑ l ∈ Finset.range (cdLm S), (rateX S sel lam i (s + 1) l : ℝ) * w l =
      ∑ l ∈ Finset.range (cdLm S), (rateX S sel lam i s l : ℝ) *
        (S.β i (sel.jStar i s l) * (if l + 1 < S.L i then w (l + 1) else 0) +
          (1 - S.β i (sel.jStar i s l)) * w l) := by
  have hL1 := hS.one_le_L i
  have hLm := cd_L_le S i
  have hb : ∀ l, ((S.β i (sel.jStar i s l)).toNNReal : ℝ) = S.β i (sel.jStar i s l) :=
    fun l => Real.coe_toNNReal _ (hS.β_nonneg _ _)
  have hc : ∀ l, ((1 - S.β i (sel.jStar i s l)).toNNReal : ℝ) = 1 - S.β i (sel.jStar i s l) :=
    fun l => Real.coe_toNNReal _ (sub_nonneg.2 (hS.β_le_one _ _))
  let F : ℕ → ℝ := fun l => if l + 1 < S.L i then
    S.β i (sel.jStar i s l) * (rateX S sel lam i s l : ℝ) * w (l + 1) else 0
  let G : ℕ → ℝ := fun l => (1 - S.β i (sel.jStar i s l)) * (rateX S sel lam i s l : ℝ) * w l
  have e1 : ∀ l, (rateX S sel lam i (s + 1) l : ℝ) * w l =
      (if l = 0 then 0 else F (l - 1)) + G l := by
    intro l
    by_cases h1 : S.L i ≤ l
    · have h0 : l ≠ 0 := by omega
      simp only [rateX, if_pos h1, NNReal.coe_zero, zero_mul, if_neg h0, F, G,
        cd_rx_L S sel lam i s l h1, if_neg (show ¬ (l - 1 + 1 < S.L i) by omega), mul_zero]
      ring
    · by_cases h0 : l = 0
      · subst h0
        simp only [rateX, if_neg h1, ↓reduceIte, zero_add, NNReal.coe_mul, hc, G]
      · have h2 : l - 1 + 1 = l := by omega
        simp only [rateX, if_neg h1, if_neg h0, NNReal.coe_add, NNReal.coe_mul, hb, hc, F, G,
          if_pos (show l - 1 + 1 < S.L i by omega), h2]
        ring
  rw [Finset.sum_congr rfl fun l _ => e1 l, Finset.sum_add_distrib, g_shift_sum F,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h3 : l + 1 < S.L i
  · simp only [F, G, if_pos h3, if_pos (show l + 1 < cdLm S by omega)]
    ring
  · simp only [F, G, if_neg h3]
    split_ifs <;> ring

/-- the exponent recursion -/
theorem cd_expo (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (z : Fin S.I → ℕ → ℕ → ℝ≥0) :
    (∑ i, (lam i : ℝ) * ((z i 0 0 : ℝ) - 1)) + cdE S sel lam n (cdg S sel z) =
      cdE S sel lam (n + 1) z := by
  unfold cdE
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL1 := hS.one_le_L i
  have hLm := cd_L_le S i
  have h0 : ¬ S.L i ≤ 0 := by omega
  conv_rhs => rw [Finset.sum_range_succ', add_comm]
  congr 1
  · rw [Finset.sum_eq_single 0]
    · simp [rateX, h0]
    · intro l _ hl; simp [rateX, hl]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [eq_comm]
    refine (cd_rate_step S hS sel lam i s (fun l => (z i (s + 1) l : ℝ) - 1)).trans ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    have hb : ((S.β i (sel.jStar i s l)).toNNReal : ℝ) = S.β i (sel.jStar i s l) :=
      Real.coe_toNNReal _ (hS.β_nonneg _ _)
    have hc : ((1 - S.β i (sel.jStar i s l)).toNNReal : ℝ) = 1 - S.β i (sel.jStar i s l) :=
      Real.coe_toNNReal _ (sub_nonneg.2 (hS.β_le_one _ _))
    simp only [cdg, cda, NNReal.coe_add, NNReal.coe_mul, hb, hc]
    split_ifs <;> push_cast <;> ring

theorem cd_prob (S : System) (lam : Fin S.I → ℝ≥0) :
    IsProbabilityMeasure (sampleMeasure S lam) := by
  unfold sampleMeasure; infer_instance

attribute [local instance] cd_prob

/-- the probability generating function of the state of `π*` -/
theorem cd_pgf (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0) :
    ∀ n (z : Fin S.I → ℕ → ℕ → ℝ≥0),
      ∫⁻ ω, cdPhi S sel lam n z ω ∂(sampleMeasure S lam) =
        ENNReal.ofReal (Real.exp (cdE S sel lam n z)) := by
  intro n
  induction n with
  | zero =>
    intro z
    simp [cdPhi, cdE]
  | succ n ih =>
    intro z
    set Lm := cdLm S
    let μN := Measure.infinitePi fun p : Fin S.I × ℕ => poissonMeasure (lam p.1)
    let μU := Measure.infinitePi fun _ : c1Idx S => (volume : Measure unitInterval)
    let A : (Fin S.I × ℕ → ℕ) → ℝ≥0∞ := fun N => ∏ i, (z i 0 0 : ℝ≥0∞) ^ (N (i, n + 1))
    let Ψ : Omega S → ℝ≥0∞ := fun ω => ∏ i, ∏ s ∈ Finset.range n, ∏ l ∈ Finset.range Lm,
      ∏ k ∈ Finset.range (stateAt S (piStar S sel lam) ω n i s l),
        cdh S sel z i s l (ω.2 (i, n + 1, s, l, sel.jStar i s l, k))
    have hA : Measurable A := Finset.measurable_prod _ fun i _ =>
      (measurable_from_nat (f := fun k : ℕ => (z i 0 0 : ℝ≥0∞) ^ k)).comp (measurable_pi_apply _)
    have hΨ : Measurable Ψ := by
      refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun s _ =>
        Finset.measurable_prod _ fun l _ => ?_
      exact c1_meas_natfun (fun x (ω : Omega S) => ∏ k ∈ Finset.range x,
          cdh S sel z i s l (ω.2 (i, n + 1, s, l, sel.jStar i s l, k)))
        (fun x => Finset.measurable_prod _ fun k _ =>
          (cd_meas_h S sel z i s l).comp ((measurable_pi_apply _).comp measurable_snd))
        _ (c1_meas_st S sel lam n i s l)
    have hpath : ∀ ω, cdPhi S sel lam (n + 1) z ω = A ω.1 * Ψ ω := fun ω =>
      cd_path S hS sel lam n z ω
    have hC : ∀ F : Fin S.I × ℕ × ℕ → ℝ≥0∞,
        ∏ i, ∏ s ∈ Finset.range n, ∏ l ∈ Finset.range Lm, F (i, s, l) =
          ∏ c ∈ (Finset.univ : Finset (Fin S.I)) ×ˢ (Finset.range n ×ˢ Finset.range Lm), F c := by
      intro F
      rw [Finset.prod_product]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Finset.prod_product]
    -- the inner integral over the uniforms
    have hin : ∀ N, ∫⁻ U, Ψ (N, U) ∂μU = ∫⁻ U, cdPhi S sel lam n (cdg S sel z) (N, U) ∂μU := by
      intro N
      let X : (c1Idx S → unitInterval) → Fin S.I × ℕ × ℕ → ℕ := fun U c =>
        stateAt S (piStar S sel lam) (N, U) n c.1 c.2.1 c.2.2
      let q : Fin S.I × ℕ × ℕ → ℕ → c1Idx S := fun c k =>
        (c.1, n + 1, c.2.1, c.2.2, sel.jStar c.1 c.2.1 c.2.2, k)
      let C := (Finset.univ : Finset (Fin S.I)) ×ˢ (Finset.range n ×ˢ Finset.range Lm)
      have e1 : ∀ U, Ψ (N, U) = ∏ c ∈ C, ∏ k ∈ Finset.range (X U c),
          cdh S sel z c.1 c.2.1 c.2.2 (U (q c k)) := fun U =>
        hC (fun c => ∏ k ∈ Finset.range (X U c), cdh S sel z c.1 c.2.1 c.2.2 (U (q c k)))
      have e2 : ∀ U, cdPhi S sel lam n (cdg S sel z) (N, U) =
          ∏ c ∈ C, (cdg S sel z c.1 c.2.1 c.2.2 : ℝ≥0∞) ^ (X U c) := fun U =>
        hC (fun c => (cdg S sel z c.1 c.2.1 c.2.2 : ℝ≥0∞) ^ (X U c))
      rw [lintegral_congr e1, lintegral_congr e2]
      rw [g_freeze (volume : Measure unitInterval) 0 {p : c1Idx S | p.2.1 ≤ n} C X
        (fun c => (c1_meas_st S sel lam n c.1 c.2.1 c.2.2).comp
          (measurable_const.prodMk measurable_id))
        (fun U U' h c => c1_dep S sel lam n N U U' (fun p hp => h p hp) c.1 c.2.1 c.2.2)
        q (by
          rintro ⟨⟨i, s, l⟩, k⟩ ⟨⟨i', s', l'⟩, k'⟩ h
          simp only [q, Prod.mk.injEq] at h
          obtain ⟨rfl, -, rfl, rfl, -, rfl⟩ := h
          rfl)
        (fun c k => by simp [q])
        (fun c => cdh S sel z c.1 c.2.1 c.2.2) (fun c => cd_meas_h S sel z _ _ _)]
      refine lintegral_congr fun U => Finset.prod_congr rfl fun c _ => ?_
      rw [cd_int_h S hS sel z]
    have hB : Measurable fun N => ∫⁻ U, cdPhi S sel lam n (cdg S sel z) (N, U) ∂μU :=
      (cd_meas_Phi S sel lam n (cdg S sel z)).lintegral_prod_right'
    have hAint : ∫⁻ N, A N ∂μN = ∏ i, ENNReal.ofReal (Real.exp (lam i * ((z i 0 0 : ℝ) - 1))) := by
      rw [← Finset.prod_congr rfl fun i _ => g_pois_pgf (lam i) (z i 0 0)]
      exact g_prodq (fun p : Fin S.I × ℕ => poissonMeasure (lam p.1)) 0 (fun i => (i, n + 1))
        (fun a b h => (Prod.mk.inj h).1) (fun i k => (z i 0 0 : ℝ≥0∞) ^ k)
        (fun i => measurable_from_nat) Finset.univ
    calc ∫⁻ ω, cdPhi S sel lam (n + 1) z ω ∂(sampleMeasure S lam)
        = ∫⁻ ω, A ω.1 * Ψ ω ∂(μN.prod μU) := lintegral_congr hpath
      _ = ∫⁻ N, ∫⁻ U, A N * Ψ (N, U) ∂μU ∂μN :=
          lintegral_prod _ ((hA.comp measurable_fst).mul hΨ).aemeasurable
      _ = ∫⁻ N, A N * ∫⁻ U, cdPhi S sel lam n (cdg S sel z) (N, U) ∂μU ∂μN := by
          refine lintegral_congr fun N => ?_
          rw [lintegral_const_mul (A N) (f := fun U => Ψ (N, U)) (hΨ.comp measurable_prodMk_left), hin N]
      _ = (∫⁻ N, A N ∂μN) * ∫⁻ N, ∫⁻ U, cdPhi S sel lam n (cdg S sel z) (N, U) ∂μU ∂μN :=
          g_split _ 0 {p : Fin S.I × ℕ | n < p.2} A _ hA hB
            (fun x y h => Finset.prod_congr rfl fun i _ => by
              rw [h (i, n + 1) (show n < n + 1 by omega)])
            (fun x y h => lintegral_congr fun U => by
              unfold cdPhi
              refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun s _ =>
                Finset.prod_congr rfl fun l _ => ?_
              rw [cd_depN S sel lam n x y U (fun p hp => h p (not_lt.2 hp)) i s l])
      _ = ENNReal.ofReal (Real.exp (cdE S sel lam (n + 1) z)) := by
          rw [← lintegral_prod _ (cd_meas_Phi S sel lam n (cdg S sel z)).aemeasurable]
          rw [show μN.prod μU = sampleMeasure S lam from rfl, ih, hAint,
            ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, cd_expo S hS sel lam n z]

/-! ## cdeb0e97 part L: from the generating function to the law -/

theorem cd_mgf_of_pgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (u : Ω → ℕ) (ν : ℝ≥0)
    (h : ∀ x : ℝ≥0, ∫⁻ ω, (x : ℝ≥0∞) ^ (u ω) ∂P = ENNReal.ofReal (Real.exp (ν * ((x : ℝ) - 1))))
    (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * u ω)) ∂P =
      ENNReal.ofReal (Real.exp (ν * (Real.exp t - 1))) := by
  have e : ∀ ω, ENNReal.ofReal (Real.exp (t * u ω)) = ((Real.exp t).toNNReal : ℝ≥0∞) ^ (u ω) := by
    intro ω
    rw [mul_comm, Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_pos t).le]
    rfl
  rw [lintegral_congr e, h, Real.coe_toNNReal _ (Real.exp_pos t).le]

theorem cd_mgf_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (u : Ω → ℕ) (hu : Measurable u)
    (ν : ℝ≥0)
    (h : ∀ x : ℝ≥0, ∫⁻ ω, (x : ℝ≥0∞) ^ (u ω) ∂P = ENNReal.ofReal (Real.exp (ν * ((x : ℝ) - 1)))) :
    (∀ t, Integrable (fun ω => Real.exp (t * (u ω : ℝ))) P) ∧
      mgf (fun ω => (u ω : ℝ)) P = fun t => Real.exp (ν * (Real.exp t - 1)) := by
  have hm : ∀ t, Measurable fun ω => Real.exp (t * (u ω : ℝ)) := fun t =>
    (measurable_from_nat (f := fun k : ℕ => Real.exp (t * k))).comp hu
  have hint : ∀ t, Integrable (fun ω => Real.exp (t * (u ω : ℝ))) P := fun t =>
    (lintegral_ofReal_ne_top_iff_integrable (hm t).aestronglyMeasurable
      (ae_of_all _ fun ω => (Real.exp_pos _).le)).1
      (by rw [cd_mgf_of_pgf P u ν h t]; exact ENNReal.ofReal_ne_top)
  refine ⟨hint, funext fun t => ?_⟩
  rw [mgf, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (Real.exp_pos _).le)
    (hm t).aestronglyMeasurable, cd_mgf_of_pgf P u ν h t,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem cd_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : Ω → ℕ) (hu : Measurable u) (ν : ℝ≥0)
    (h : ∀ x : ℝ≥0, ∫⁻ ω, (x : ℝ≥0∞) ^ (u ω) ∂P = ENNReal.ofReal (Real.exp (ν * ((x : ℝ) - 1)))) :
    HasLaw u (poissonMeasure ν) P := by
  have hX : Measurable fun ω => (u ω : ℝ) := (measurable_from_nat (f := (Nat.cast : ℕ → ℝ))).comp hu
  obtain ⟨hiP, hmP⟩ := cd_mgf_eq P u hu ν h
  obtain ⟨-, hmQ⟩ := cd_mgf_eq (poissonMeasure ν) id measurable_id ν (fun x => g_pois_pgf ν x)
  have hset : integrableExpSet (fun ω => (u ω : ℝ)) P = Set.univ :=
    Set.eq_univ_of_forall fun t => hiP t
  have hc : complexMGF (fun ω => (u ω : ℝ)) P =
      complexMGF (fun k : ℕ => ((id k : ℕ) : ℝ)) (poissonMeasure ν) := by
    funext w
    exact eqOn_complexMGF_of_mgf (hmP.trans hmQ.symm) (by simp [hset])
  refine ⟨hu.aemeasurable, ?_⟩
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  rw [Measure.map_map measurable_from_nat hu]
  exact Measure.ext_of_complexMGF_eq hX.aemeasurable
    (measurable_from_nat (f := fun k : ℕ => ((id k : ℕ) : ℝ))).aemeasurable hc

theorem g14_lint_poisson (r : ℝ≥0) (f : ℕ → ℝ≥0∞) :
    ∫⁻ k, f k ∂(poissonMeasure r) =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) * f n := by
  rw [poissonMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem g14_hasSum_first (r : ℝ≥0) :
    HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ))) r := by
  have h0 := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  rw [mul_one] at h0
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  refine h0.congr_fun fun n => ?_
  rw [Nat.factorial_succ]; push_cast
  have : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem g14_hasSum_second (r : ℝ≥0) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)))
      ((r : ℝ) ^ 2 + r) := by
  have h0 := ((g14_hasSum_first r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  rw [show (r : ℝ) * (r + 1) = (r : ℝ) ^ 2 + r by ring] at h0
  refine (hasSum_nat_add_iff' 1).1 ?_
  simp only [Finset.sum_range_one, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_mul, sub_zero]
  refine h0.congr_fun fun n => ?_
  rw [Nat.factorial_succ]; push_cast
  have : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem g14_hasSum_sq (r : ℝ≥0) (b : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-r) * r ^ n / (Nat.factorial n : ℝ)) * ((n : ℝ) - b) ^ 2)
      ((r : ℝ) + ((r : ℝ) - b) ^ 2) := by
  have h := ((g14_hasSum_second r).sub ((g14_hasSum_first r).mul_left (2 * b))).add
    ((hasSum_one_poissonMeasure r).mul_left (b ^ 2))
  rw [show (r : ℝ) + ((r : ℝ) - b) ^ 2 = (r : ℝ) ^ 2 + r - 2 * b * r + b ^ 2 * 1 by ring]
  refine h.congr_fun fun n => ?_
  ring

theorem g14_poisson_sq (r : ℝ≥0) (b : ℝ) :
    ∫⁻ k, ENNReal.ofReal (((k : ℝ) - b) ^ 2) ∂(poissonMeasure r) =
      ENNReal.ofReal ((r : ℝ) + ((r : ℝ) - b) ^ 2) := by
  rw [g14_lint_poisson]
  have hs := g14_hasSum_sq r b
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable]
  refine tsum_congr fun n => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]


theorem cd_mean_var {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : Ω → ℕ) (hu : Measurable u) (ν : ℝ≥0) (hl : HasLaw u (poissonMeasure ν) P) :
    ∫⁻ ω, (u ω : ℝ≥0∞) ∂P = ν ∧ evariance (fun ω => (u ω : ℝ)) P = ν := by
  have hmean : ∫⁻ ω, (u ω : ℝ≥0∞) ∂P = ν := by
    rw [← lintegral_map (f := fun k : ℕ => (k : ℝ≥0∞)) measurable_from_nat hu, hl.map_eq,
      c1_poisson_mean]
  refine ⟨hmean, ?_⟩
  have hE : ∫ ω, (u ω : ℝ) ∂P = ν := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => Nat.cast_nonneg _)
      ((measurable_from_nat (f := (Nat.cast : ℕ → ℝ))).comp hu).aestronglyMeasurable]
    simp_rw [ENNReal.ofReal_natCast]
    rw [hmean]; simp
  rw [evariance_eq_lintegral_ofReal, hE,
    ← lintegral_map (f := fun k : ℕ => ENNReal.ofReal (((k : ℝ) - ν) ^ 2)) measurable_from_nat hu,
    hl.map_eq, g14_poisson_sq]
  simp

/-! ## cdeb0e97 part U: the usage -/

theorem cd_meas_usage (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (j : Fin S.J) :
    Measurable fun ω => usage S sel n (stateAt S (piStar S sel lam) ω n) j := by
  unfold usage
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun l _ =>
    Finset.measurable_sum _ fun s _ => ?_
  split_ifs
  · exact c1_meas_st S sel lam n i s l
  · exact measurable_const

/-- the rate of the usage, over all cells -/
noncomputable def cdNu (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (j : Fin S.J) : ℝ≥0 :=
  ∑ i, ∑ s ∈ Finset.range n, ∑ l ∈ Finset.range (cdLm S),
    if sel.jStar i s l = j.succ then rateX S sel lam i s l else 0

theorem cd_usage_pgf (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (j : Fin S.J) (x : ℝ≥0) :
    ∫⁻ ω, (x : ℝ≥0∞) ^ (usage S sel n (stateAt S (piStar S sel lam) ω n) j)
        ∂(sampleMeasure S lam) =
      ENNReal.ofReal (Real.exp (cdNu S sel lam n j * ((x : ℝ) - 1))) := by
  let z : Fin S.I → ℕ → ℕ → ℝ≥0 := fun i s l => if sel.jStar i s l = j.succ then x else 1
  have hpt : ∀ ω, (x : ℝ≥0∞) ^ (usage S sel n (stateAt S (piStar S sel lam) ω n) j) =
      cdPhi S sel lam n z ω := by
    intro ω
    have e1 : ∀ i s l, (z i s l : ℝ≥0∞) ^ (stateAt S (piStar S sel lam) ω n i s l) =
        (x : ℝ≥0∞) ^ (if sel.jStar i s l = j.succ then
          stateAt S (piStar S sel lam) ω n i s l else 0) := by
      intro i s l
      simp only [z]
      split_ifs <;> simp
    unfold cdPhi
    simp_rw [e1, Finset.prod_pow_eq_pow_sum]
    congr 1
    unfold usage
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (s := Finset.range n)]
    have hLm := cd_L_le S i
    rw [← Finset.sum_subset (Finset.range_subset_range.2 hLm)
      (f := fun l => ∑ s ∈ Finset.range n, if sel.jStar i s l = j.succ then
        stateAt S (piStar S sel lam) ω n i s l else 0)]
    · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun s _ => ?_
      by_cases h : sel.jStar i s l = j.succ
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    · intro l _ hl
      refine Finset.sum_eq_zero fun s _ => ?_
      have : ¬ l < S.L i := fun h => hl (Finset.mem_range.2 h)
      rw [cd_st_L S sel lam ω n i s l (by omega)]
      simp
  rw [lintegral_congr hpt, cd_pgf S hS sel lam n z]
  congr 2
  unfold cdE cdNu
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [z]
  split_ifs <;> simp

/-- the rate in the form of the statement -/
theorem cd_nu_eq (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (j : Fin S.J) :
    cdNu S sel lam n j = ∑ i, ∑ s ∈ Finset.range n,
      ∑ l ∈ Finset.range (min (S.L i - 1) s + 1),
        if sel.jStar i s l = j.succ then rateX S sel lam i s l else 0 := by
  unfold cdNu
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
  have hL1 := hS.one_le_L i
  have hLm := cd_L_le S i
  refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l _ hl => ?_).symm
  have : ¬ l < min (S.L i - 1) s + 1 := fun h => hl (Finset.mem_range.2 h)
  by_cases h1 : S.L i ≤ l
  · rw [cd_rx_L S sel lam i s l h1]; simp
  · rw [e8_rateX_zero S sel lam i s l (by omega)]; simp

theorem cd_main (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (n : ℕ) (j : Fin S.J) :
    HasLaw (fun ω => usage S sel n (stateAt S (piHat S sel) ω n) j)
      (poissonMeasure (cdNu S sel lam n j)) (sampleMeasure S lam) := by
  have e : (fun ω => usage S sel n (stateAt S (piHat S sel) ω n) j) =
      fun ω => usage S sel n (stateAt S (piStar S sel lam) ω n) j :=
    funext fun ω => by rw [e8_st S sel lam]
  rw [e]
  exact cd_law _ _ (cd_meas_usage S sel lam n j) _ (cd_usage_pgf S hS sel lam n j)

theorem cd_meas_usage' (S : System) (sel : Selection S) (lam : Fin S.I → ℝ≥0) (n : ℕ)
    (j : Fin S.J) :
    Measurable fun ω => usage S sel n (stateAt S (piHat S sel) ω n) j := by
  have e : (fun ω => usage S sel n (stateAt S (piHat S sel) ω n) j) =
      fun ω => usage S sel n (stateAt S (piStar S sel lam) ω n) j :=
    funext fun ω => by rw [e8_st S sel lam]
  rw [e]; exact cd_meas_usage S sel lam n j

/-- the limit of the rates -/
theorem cd_nu_tendsto (S : System) (hS : Standing S) (sel : Selection S) (lam : Fin S.I → ℝ≥0)
    (j : Fin S.J) :
    Tendsto (fun t => ((cdNu S sel lam (t - 1) j : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 (mu S sel lam j)) := by
  rw [e8_mu]
  have e : ∀ n, ((cdNu S sel lam n j : ℝ≥0) : ℝ≥0∞) = ∑ i, ∑ s ∈ Finset.range n,
      ∑ l ∈ Finset.range (S.L i),
        (if j.succ = sel.jStar i s l then (rateX S sel lam i s l : ℝ≥0∞) else 0) := by
    intro n
    unfold cdNu
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => ?_
    have hLm := cd_L_le S i
    refine (Finset.sum_subset (Finset.range_subset_range.2 hLm) fun l _ hl => ?_).symm.trans ?_
    · have : ¬ l < S.L i := fun h => hl (Finset.mem_range.2 h)
      rw [cd_rx_L S sel lam i s l (by omega)]; simp
    · refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : sel.jStar i s l = j.succ
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp
  simp_rw [e]
  exact tendsto_finsetSum _ fun i _ =>
    (ENNReal.tendsto_nat_tsum _).comp (tendsto_sub_atTop_nat 1)

end CloudCostOpt

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal CloudCostOpt in
theorem solution (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i) (j : Fin S.J) :
    let P := sampleMeasure S lam
    let u : ℕ → Omega S → ℕ := fun t ω =>
      usage S sel (t - 1) (stateAt S (piHat S sel) ω (t - 1)) j
    let ν : ℕ → ℝ≥0 := fun t => ∑ i, ∑ s ∈ Finset.range (t - 1),
      ∑ l ∈ Finset.range (min (S.L i - 1) s + 1),
        if sel.jStar i s l = j.succ then rateX S sel lam i s l else 0
    (∀ t, 1 ≤ t →
      HasLaw (u t) (poissonMeasure (ν t)) P ∧
      ∫⁻ ω, (u t ω : ℝ≥0∞) ∂P = ν t ∧
      evariance (fun ω => (u t ω : ℝ)) P = ν t) ∧
    Tendsto (fun t => ∫⁻ ω, (u t ω : ℝ≥0∞) ∂P) atTop (𝓝 (mu S sel lam j)) ∧
    Tendsto (fun t => evariance (fun ω => (u t ω : ℝ)) P) atTop (𝓝 (mu S sel lam j)) := by
  intro P u ν
  have : IsProbabilityMeasure P := cd_prob S lam
  have hν : ∀ t, ν t = cdNu S sel lam (t - 1) j := fun t => (cd_nu_eq S hS sel lam (t - 1) j).symm
  have hmv : ∀ t, ∫⁻ ω, (u t ω : ℝ≥0∞) ∂P = ν t ∧
      evariance (fun ω => (u t ω : ℝ)) P = ν t := by
    intro t
    rw [hν]
    exact cd_mean_var P (u t) (cd_meas_usage' S sel lam (t - 1) j) _ (cd_main S hS sel lam (t - 1) j)
  refine ⟨fun t _ => ⟨?_, (hmv t).1, (hmv t).2⟩, ?_, ?_⟩
  · rw [hν]; exact cd_main S hS sel lam (t - 1) j
  · refine (cd_nu_tendsto S hS sel lam j).congr fun t => ?_
    rw [(hmv t).1, hν]
  · refine (cd_nu_tendsto S hS sel lam j).congr fun t => ?_
    rw [(hmv t).2, hν]
