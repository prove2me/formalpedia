-- Prove2me | solution 1 for BauerleRiederMDP.Contracting.theorem_7_3_5
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T12:23:00.589677+00:00
-- url     : https://prove2.me/submissions/bdf67cd1-31c1-4282-be6b-e88669ac0baf

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_BauerleRiederMDP_Contracting_IsClosedInIBb
import Definitions.Def_BauerleRiederMDP_Contracting_Treal

set_option autoImplicit false

-- Inline checked component: Norm

set_option autoImplicit false

open MDPFinance.Contracting

namespace S06P100

theorem ib_sub {E : Type*} [MeasurableSpace E] {b u v : E → ℝ}
    (hu : u ∈ IBb b) (hv : v ∈ IBb b) :
    (fun x => u x - v x) ∈ IBb b := by
  rcases hu with ⟨hum, cu, hcu, hu⟩
  rcases hv with ⟨hvm, cv, hcv, hv⟩
  refine ⟨hum.sub hvm, cu + cv, add_nonneg hcu hcv, ?_⟩
  intro x
  calc
    |u x - v x| ≤ |u x| + |v x| := abs_sub _ _
    _ ≤ cu * b x + cv * b x := add_le_add (hu x) (hv x)
    _ = (cu + cv) * b x := by ring

theorem normb_nonneg {E : Type*} (b : E → ℝ) (hb : ∀ x, 0 ≤ b x)
    (v : E → ℝ) : 0 ≤ normb b v :=
  Real.iSup_nonneg (fun x => div_nonneg (abs_nonneg _) (hb x))

theorem ratio_le_of_bound {E : Type*} (b : E → ℝ) (hb : ∀ x, 0 ≤ b x)
    (v : E → ℝ) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |v x| ≤ C * b x)
    (x : E) : |v x| / b x ≤ C := by
  by_cases hzero : b x = 0
  · simpa only [hzero, div_zero] using hC
  · exact (div_le_iff₀ (lt_of_le_of_ne (hb x) (Ne.symm hzero))).2 (hbound x)

theorem normb_le_of_bound {E : Type*} (b : E → ℝ) (hb : ∀ x, 0 ≤ b x)
    (v : E → ℝ) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |v x| ≤ C * b x) :
    normb b v ≤ C :=
  Real.iSup_le (ratio_le_of_bound b hb v hC hbound) hC

theorem ratios_bddAbove {E : Type*} [MeasurableSpace E]
    (b : E → ℝ) (hb : ∀ x, 0 ≤ b x) (v : E → ℝ) (hv : v ∈ IBb b) :
    BddAbove (Set.range (fun x => |v x| / b x)) := by
  rcases hv with ⟨_, C, hC, hbound⟩
  refine ⟨C, ?_⟩
  rintro z ⟨x, rfl⟩
  exact ratio_le_of_bound b hb v hC hbound x

theorem abs_le_normb_mul {E : Type*} [MeasurableSpace E]
    (b : E → ℝ) (hb : ∀ x, 0 ≤ b x) (v : E → ℝ) (hv : v ∈ IBb b)
    (x : E) : |v x| ≤ normb b v * b x := by
  by_cases hzero : b x = 0
  · rcases hv with ⟨_, C, _, hbound⟩
    simpa only [hzero, mul_zero] using hbound x
  · have hdiv : |v x| / b x ≤ normb b v := le_ciSup (ratios_bddAbove b hb v hv) x
    exact (div_le_iff₀ (lt_of_le_of_ne (hb x) (Ne.symm hzero))).1 hdiv

theorem normb_sub_comm {E : Type*} (b u v : E → ℝ) :
    normb b (fun x => u x - v x) = normb b (fun x => v x - u x) := by
  simp only [normb, abs_sub_comm]

end S06P100


-- Inline checked component: Verification

/-!
Adapted from the accepted Prove2Me verification proof for theorem
68971fc3-4632-4c92-b75d-69fd9d1a84b9, submission
45ebf4c1-f69b-4903-854e-660f06662371.
Original source SHA256:
64a1eaefb55937e8ac489048f89ba16ba83782c794254f15b1ee6fa9bafaa60b.
The Ver734Aux helper declarations below are unchanged. The verification theorem
has been renamed and its final, already proved finite-horizon convergence is
returned explicitly instead of being used only to identify the limsup.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open MDPFinance.Contracting

namespace Ver734Aux

lemma toENNReal_coe_sup (t : ℝ) : ((t : EReal) ⊔ 0).toENNReal = ENNReal.ofReal t := by
  rcases le_total t 0 with h | h
  · rw [sup_of_le_right (by exact_mod_cast h)]; simp [ENNReal.ofReal_of_nonpos h]
  · rw [sup_of_le_left (by exact_mod_cast h), EReal.toENNReal_of_ne_top (EReal.coe_ne_top t)]
    simp

lemma erealIntegral_mono {E : Type*} [MeasurableSpace E] (μ : Measure E) {f g : E → EReal}
    (h : ∀ x, f x ≤ g x) : erealIntegral μ f ≤ erealIntegral μ g := by
  unfold erealIntegral
  apply add_le_add
  · apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) _)
  · apply EReal.neg_le_neg_iff.2
    apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    apply lintegral_mono
    intro x
    exact EReal.toENNReal_le_toENNReal (sup_le_sup_right (EReal.neg_le_neg_iff.2 (h x)) _)

lemma erealIntegral_coe {E : Type*} [MeasurableSpace E] (μ : Measure E) {g : E → ℝ}
    (hg : Integrable g μ) :
    erealIntegral μ (fun y => (g y : EReal)) = ((∫ y, g y ∂μ : ℝ) : EReal) := by
  unfold erealIntegral
  have h1 : ∀ y, ((g y : EReal) ⊔ 0).toENNReal = ENNReal.ofReal (g y) :=
    fun y => toENNReal_coe_sup _
  have h2 : ∀ y, ((-(g y : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-g y) := by
    intro y; rw [← EReal.coe_neg]; exact toENNReal_coe_sup _
  simp only [h1, h2]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  have f1 : ∫⁻ a, ENNReal.ofReal (g a) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (le_abs_self (g a)))
      (by simpa [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm g).1 hg.2)).ne
  have f2 : ∫⁻ a, ENNReal.ofReal (-g a) ∂μ ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono fun a => ENNReal.ofReal_le_ofReal (neg_le_abs (g a)))
      (by simpa [Real.norm_eq_abs] using (hasFiniteIntegral_iff_norm g).1 hg.2)).ne
  rw [← EReal.coe_ennreal_toReal f1, ← EReal.coe_ennreal_toReal f2, ← EReal.coe_neg,
    ← EReal.coe_add, sub_eq_add_neg]

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

lemma b_integrable (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D) :
    Integrable b (M.Q xa) := by
  refine ⟨hb.hb_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hb.hb_nonneg)]
  exact lt_of_le_of_lt (hb.hQ xa hxa) ENNReal.ofReal_lt_top

lemma b_int_le (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D) :
    ∫ y, b y ∂(M.Q xa) ≤ αb * b xa.1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hb.hb_nonneg)
    hb.hb_meas.aestronglyMeasurable]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb.hQ xa hxa)
  rwa [ENNReal.toReal_ofReal (mul_nonneg hb.hαb (hb.hb_nonneg _))] at this

lemma v_integrable (M : MarkovDecisionModel E A) {b : E → ℝ} {cr αb : ℝ}
    (hb : IsBoundingFunction M b cr αb) {xa : E × A} (hxa : xa ∈ M.D)
    {v : E → ℝ} (hv : Measurable v) {c : ℝ} (hc : ∀ x, |v x| ≤ c * b x) :
    Integrable v (M.Q xa) :=
  Integrable.mono' ((b_integrable M hb hxa).const_mul c) hv.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hc y)

end Ver734Aux

open Ver734Aux in
theorem S06P100.verification_with_tendsto {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb : M.β * αb < 1)
    (v : E → ℝ) (hvIBb : v ∈ IBb b) (hvfix : ∀ x, T M (fun y => (v y : EReal)) x = (v x : EReal))
    (fstar : E → A) (hfstar : IsMaximizerOf M (fun y => (v y : EReal)) fstar) :
    (∀ x, (v x : EReal) = Jinf M x) ∧ (∀ x, (v x : EReal) = Jlim M x) ∧
      (∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) ∧
      ∀ x, Tendsto (fun n => Jn M M.r n x) atTop (𝓝 (v x : EReal)) := by
  obtain ⟨hvm, c, hc0, hc⟩ := hvIBb
  have hβ0 := M.hβ0
  have hq0 : 0 ≤ M.β * αb := mul_nonneg hβ0.le hb.hαb
  set ε : ℕ → ℝ := fun n => (M.β * αb) ^ n * c with hε
  have hε0 : ∀ n, 0 ≤ ε n := fun n => mul_nonneg (pow_nonneg hq0 n) hc0
  have hεs : ∀ n, ε (n + 1) = M.β * αb * ε n := fun n => by simp only [hε]; ring
  -- integral of v + t * b
  have hint : ∀ xa ∈ M.D, ∀ t : ℝ,
      erealIntegral (M.Q xa) (fun y => ((v y + t * b y : ℝ) : EReal)) =
        (((∫ y, v y ∂(M.Q xa)) + t * ∫ y, b y ∂(M.Q xa) : ℝ) : EReal) := by
    intro xa hxa t
    have hI : Integrable (fun y => v y + t * b y) (M.Q xa) :=
      (v_integrable M hb hxa hvm hc).add ((b_integrable M hb hxa).const_mul t)
    rw [erealIntegral_coe _ hI, integral_add (v_integrable M hb hxa hvm hc)
      ((b_integrable M hb hxa).const_mul t), integral_const_mul]
  have hLv : ∀ xa ∈ M.D, L M (fun y => (v y : EReal)) xa =
      ((M.r xa + M.β * ∫ y, v y ∂(M.Q xa) : ℝ) : EReal) := by
    intro xa hxa
    unfold L
    rw [erealIntegral_coe _ (v_integrable M hb hxa hvm hc)]
    simp only [EReal.coe_add, EReal.coe_mul]
  -- real Bellman inequality
  have hLle : ∀ x a, (x, a) ∈ M.D → M.r (x, a) + M.β * ∫ y, v y ∂(M.Q (x, a)) ≤ v x := by
    intro x a hxa
    have h1 : L M (fun y => (v y : EReal)) (x, a) ≤ T M (fun y => (v y : EReal)) x := by
      unfold T
      exact le_biSup (fun a => L M (fun y => (v y : EReal)) (x, a)) (show a ∈ M.Dx x from hxa)
    rw [hvfix, hLv _ hxa] at h1
    exact_mod_cast h1
  have hfeq : ∀ x, M.r (x, fstar x) + M.β * ∫ y, v y ∂(M.Q (x, fstar x)) = v x := by
    intro x
    have h1 := congrFun hfstar.2 x
    rw [hvfix, hLv _ (hfstar.1.2 x)] at h1
    exact_mod_cast h1
  -- upper bound for all policies
  have hup : ∀ n (π : ℕ → E → A), IsPolicyOf M π → ∀ x,
      Jnpi M M.r π n x ≤ ((v x + ε n * b x : ℝ) : EReal) := by
    intro n
    induction n with
    | zero =>
      intro π _ x
      simp only [Jnpi]
      have := hc x
      have : (0 : ℝ) ≤ v x + ε 0 * b x := by
        simp only [hε, pow_zero, one_mul]; linarith [neg_abs_le (v x)]
      exact_mod_cast this
    | succ n ih =>
      intro π hπ x
      have hxa : (x, π 0 x) ∈ M.D := (hπ 0).2 x
      have hσ : IsPolicyOf M (fun k => π (k + 1)) := fun k => hπ (k + 1)
      simp only [Jnpi]
      have h1 := erealIntegral_mono (M.Q (x, π 0 x)) (ih _ hσ)
      rw [hint _ hxa] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : EReal) ≤ (M.β : EReal) by
        exact_mod_cast hβ0.le)
      refine le_trans (add_le_add_right h2 _) ?_
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h3 := hLle x _ hxa
      have h4 := b_int_le M hb hxa
      have h5 := mul_le_mul_of_nonneg_left h4 (hε0 n)
      rw [hεs]
      nlinarith
  -- lower bound for fstar
  have hlow : ∀ n x, (((v x - ε n * b x : ℝ)) : EReal) ≤ Jnpi M M.r (fun _ => fstar) n x := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [Jnpi]
      have := hc x
      have : v x - ε 0 * b x ≤ 0 := by
        simp only [hε, pow_zero, one_mul]; linarith [le_abs_self (v x)]
      exact_mod_cast this
    | succ n ih =>
      intro x
      have hxa : (x, fstar x) ∈ M.D := hfstar.1.2 x
      simp only [Jnpi]
      have h1 := erealIntegral_mono (M.Q (x, fstar x))
        (g := Jnpi M M.r (fun _ => fstar) n)
        (f := fun y => ((v y + (-ε n) * b y : ℝ) : EReal)) (fun y => by
          have := ih y; rw [show v y + -ε n * b y = v y - ε n * b y by ring]; exact this)
      rw [hint _ hxa] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : EReal) ≤ (M.β : EReal) by
        exact_mod_cast hβ0.le)
      refine le_trans ?_ (add_le_add_right h2 _)
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h3 := hfeq x
      have h4 := b_int_le M hb hxa
      have h5 := mul_le_mul_of_nonneg_left h4 (hε0 n)
      rw [hεs]
      nlinarith
  -- limits
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hαb).mul_const c
    simpa [hε] using this
  have hTup : ∀ x, Tendsto (fun n => ((v x + ε n * b x : ℝ) : EReal)) atTop (𝓝 (v x : EReal)) := by
    intro x
    have : Tendsto (fun n => v x + ε n * b x) atTop (𝓝 (v x)) := by
      simpa using tendsto_const_nhds.add (hεt.mul_const (b x))
    exact (continuous_coe_real_ereal.tendsto _).comp this
  have hTlow : ∀ x, Tendsto (fun n => ((v x - ε n * b x : ℝ) : EReal)) atTop (𝓝 (v x : EReal)) := by
    intro x
    have : Tendsto (fun n => v x - ε n * b x) atTop (𝓝 (v x)) := by
      simpa using tendsto_const_nhds.sub (hεt.mul_const (b x))
    exact (continuous_coe_real_ereal.tendsto _).comp this
  have hfpol : IsPolicyOf M (fun _ => fstar) := fun _ => hfstar.1
  have hfstarT : ∀ x, Tendsto (fun n => Jnpi M M.r (fun _ => fstar) n x) atTop
      (𝓝 (v x : EReal)) := fun x =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le (hTlow x) (hTup x) (fun n => hlow n x)
      (fun n => hup n _ hfpol x)
  have hfstarInf : ∀ x, Jinfpi M M.r (fun _ => fstar) x = (v x : EReal) := fun x =>
    (hfstarT x).limsup_eq
  have hJinf : ∀ x, (v x : EReal) = Jinf M x := by
    intro x
    apply le_antisymm
    · rw [← hfstarInf x]
      exact le_biSup (fun π => Jinfpi M M.r π x) (show (fun _ => fstar) ∈
        {π : ℕ → E → A | IsPolicyOf M π} from hfpol)
    · apply iSup₂_le
      intro π hπ
      rw [← (hTup x).limsup_eq]
      exact limsup_le_limsup (Eventually.of_forall fun n => hup n π hπ x)
  have hJn : ∀ x, Tendsto (fun n => Jn M M.r n x) atTop (𝓝 (v x : EReal)) := by
    intro x
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hfstarT x) (hTup x) (fun n => ?_)
      (fun n => ?_)
    · exact le_biSup (fun π => Jnpi M M.r π n x) (show (fun _ => fstar) ∈
        {π : ℕ → E → A | IsPolicyOf M π} from hfpol)
    · exact iSup₂_le fun π hπ => hup n π hπ x
  exact ⟨hJinf, fun x => (hJn x).limsup_eq.symm,
    (fun x => by rw [hfstarInf, hJinf]), hJn⟩


-- Inline checked component: Contraction

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open MDPFinance.Contracting BauerleRiederMDP.Contracting

namespace S06P100

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

theorem Treal_spec (M : MarkovDecisionModel E A) (S : Set (E → ℝ))
    (hT : ∀ v ∈ S, ∃ w ∈ S,
      T M (fun y => (v y : EReal)) = fun y => (w y : EReal))
    {v : E → ℝ} (hv : v ∈ S) :
    Treal M v ∈ S ∧ ∀ x, T M (fun y => (v y : EReal)) x = (Treal M v x : EReal) := by
  obtain ⟨w, hw, hEq⟩ := hT v hv
  have he : Treal M v = w := by
    funext x
    unfold Treal
    rw [hEq]
    simp
  rw [he]
  exact ⟨hw, fun x => congrFun hEq x⟩

theorem IBb_integrable (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) {v : E → ℝ} (hv : v ∈ IBb b)
    {xa : E × A} (hxa : xa ∈ M.D) : Integrable v (M.Q xa) := by
  obtain ⟨hm, c, _, hc⟩ := hv
  exact Ver734Aux.v_integrable M hb hxa hm hc

theorem L_coe (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) {v : E → ℝ} (hv : v ∈ IBb b)
    {xa : E × A} (hxa : xa ∈ M.D) :
    L M (fun y => (v y : EReal)) xa =
      ((M.r xa + M.β * ∫ y, v y ∂(M.Q xa) : ℝ) : EReal) := by
  unfold L
  rw [Ver734Aux.erealIntegral_coe _ (IBb_integrable M b cr αb hb hv hxa)]
  simp only [EReal.coe_add, EReal.coe_mul]

theorem Treal_action_le (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (S : Set (E → ℝ)) (hsub : S ⊆ IBb b)
    (hT : ∀ v ∈ S, ∃ w ∈ S,
      T M (fun y => (v y : EReal)) = fun y => (w y : EReal))
    {v : E → ℝ} (hv : v ∈ S) (x : E) (a : A) (hxa : (x, a) ∈ M.D) :
    M.r (x, a) + M.β * ∫ y, v y ∂(M.Q (x, a)) ≤ Treal M v x := by
  have h : L M (fun y => (v y : EReal)) (x, a) ≤ T M (fun y => (v y : EReal)) x := by
    unfold T
    exact le_biSup (fun a => L M (fun y => (v y : EReal)) (x, a)) hxa
  rw [L_coe M b cr αb hb (hsub hv) hxa, (Treal_spec M S hT hv).2 x] at h
  exact_mod_cast h

theorem Treal_action_eq (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (S : Set (E → ℝ)) (hsub : S ⊆ IBb b)
    (hT : ∀ v ∈ S, ∃ w ∈ S,
      T M (fun y => (v y : EReal)) = fun y => (w y : EReal))
    {v : E → ℝ} (hv : v ∈ S) {f : E → A}
    (hf : IsMaximizerOf M (fun y => (v y : EReal)) f) (x : E) :
    Treal M v x = M.r (x, f x) + M.β * ∫ y, v y ∂(M.Q (x, f x)) := by
  have h := congrFun hf.2 x
  rw [L_coe M b cr αb hb (hsub hv) (hf.1.2 x), (Treal_spec M S hT hv).2 x] at h
  exact_mod_cast h.symm

theorem integral_sub_le_of_bound (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb)
    {u v : E → ℝ} (hu : u ∈ IBb b) (hv : v ∈ IBb b)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, u y - v y ≤ C * b y)
    {xa : E × A} (hxa : xa ∈ M.D) :
    (∫ y, u y ∂(M.Q xa)) - (∫ y, v y ∂(M.Q xa)) ≤ C * (αb * b xa.1) := by
  have huI := IBb_integrable M b cr αb hb hu hxa
  have hvI := IBb_integrable M b cr αb hb hv hxa
  rw [← integral_sub huI hvI]
  calc
    (∫ y, u y - v y ∂(M.Q xa)) ≤ ∫ y, C * b y ∂(M.Q xa) :=
      integral_mono (huI.sub hvI) ((Ver734Aux.b_integrable M hb hxa).const_mul C) hbound
    _ = C * ∫ y, b y ∂(M.Q xa) := integral_const_mul C b
    _ ≤ C * (αb * b xa.1) :=
      mul_le_mul_of_nonneg_left (Ver734Aux.b_int_le M hb hxa) hC

theorem Treal_sub_le_of_bound (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb)
    (S : Set (E → ℝ)) (hsub : S ⊆ IBb b)
    (hT : ∀ v ∈ S, ∃ w ∈ S,
      T M (fun y => (v y : EReal)) = fun y => (w y : EReal))
    (hmax : ∀ v ∈ S, ∃ f, IsMaximizerOf M (fun y => (v y : EReal)) f)
    {u v : E → ℝ} (hu : u ∈ S) (hv : v ∈ S)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, u y - v y ≤ C * b y) (x : E) :
    Treal M u x - Treal M v x ≤ (M.β * αb) * C * b x := by
  obtain ⟨f, hf⟩ := hmax u hu
  have he := Treal_action_eq M b cr αb hb S hsub hT hu hf x
  have hle := Treal_action_le M b cr αb hb S hsub hT hv x (f x) (hf.1.2 x)
  have hint := integral_sub_le_of_bound M b cr αb hb (hsub hu) (hsub hv) hC hbound (hf.1.2 x)
  calc
    Treal M u x - Treal M v x ≤
        (M.r (x, f x) + M.β * ∫ y, u y ∂(M.Q (x, f x))) -
          (M.r (x, f x) + M.β * ∫ y, v y ∂(M.Q (x, f x))) := by
      rw [he]
      exact sub_le_sub_left hle _
    _ = M.β * ((∫ y, u y ∂(M.Q (x, f x))) - (∫ y, v y ∂(M.Q (x, f x)))) := by ring
    _ ≤ M.β * (C * (αb * b x)) := mul_le_mul_of_nonneg_left hint M.hβ0.le
    _ = (M.β * αb) * C * b x := by ring

theorem Treal_weighted_lipschitz (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb)
    (S : Set (E → ℝ)) (hsub : S ⊆ IBb b)
    (hT : ∀ v ∈ S, ∃ w ∈ S,
      T M (fun y => (v y : EReal)) = fun y => (w y : EReal))
    (hmax : ∀ v ∈ S, ∃ f, IsMaximizerOf M (fun y => (v y : EReal)) f)
    {u v : E → ℝ} (hu : u ∈ S) (hv : v ∈ S)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y, |u y - v y| ≤ C * b y) (x : E) :
    |Treal M u x - Treal M v x| ≤ (M.β * αb) * C * b x := by
  have huv := Treal_sub_le_of_bound M b cr αb hb S hsub hT hmax hu hv hC
    (fun y => (le_abs_self _).trans (hbound y)) x
  have hvu := Treal_sub_le_of_bound M b cr αb hb S hsub hT hmax hv hu hC
    (fun y => (le_abs_self _).trans ((abs_sub_comm (v y) (u y)).trans_le (hbound y))) x
  exact abs_le.mpr ⟨by linarith, huv⟩

theorem Treal_mono (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb)
    (S : Set (E → ℝ)) (hsub : S ⊆ IBb b)
    (hT : ∀ v ∈ S, ∃ w ∈ S,
      T M (fun y => (v y : EReal)) = fun y => (w y : EReal))
    (hmax : ∀ v ∈ S, ∃ f, IsMaximizerOf M (fun y => (v y : EReal)) f)
    {u v : E → ℝ} (hu : u ∈ S) (hv : v ∈ S) (hle : ∀ y, u y ≤ v y) (x : E) :
    Treal M u x ≤ Treal M v x := by
  have h := Treal_sub_le_of_bound M b cr αb hb S hsub hT hmax hu hv
    (C := 0) le_rfl (fun y => by simpa only [zero_mul] using sub_nonpos.mpr (hle y)) x
  simpa only [mul_zero, zero_mul, sub_nonpos] using h

end S06P100


-- Inline checked component: Minimality

set_option autoImplicit false

open Filter Topology

namespace S06P100

theorem superharmonic_iterates {E : Type*}
    (F : (E → ℝ) → (E → ℝ)) (S : Set (E → ℝ))
    (hF : ∀ u ∈ S, F u ∈ S)
    (hmono : ∀ u ∈ S, ∀ v ∈ S, (∀ x, u x ≤ v x) → ∀ x, F u x ≤ F v x)
    {g : E → ℝ} (hg : g ∈ S) (hFg : ∀ x, F g x ≤ g x) :
    ∀ n : ℕ, F^[n] g ∈ S ∧ ∀ x, F^[n] g x ≤ g x := by
  intro n
  induction n with
  | zero => exact ⟨hg, fun _ => le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨hF _ ih.1, ?_⟩
    intro x
    exact (hmono _ ih.1 g hg ih.2 x).trans (hFg x)

theorem iterate_le_of_superharmonic {E : Type*}
    (F : (E → ℝ) → (E → ℝ)) (S : Set (E → ℝ))
    (hF : ∀ u ∈ S, F u ∈ S)
    (hmono : ∀ u ∈ S, ∀ v ∈ S, (∀ x, u x ≤ v x) → ∀ x, F u x ≤ F v x)
    {g : E → ℝ} (hg : g ∈ S) (hFg : ∀ x, F g x ≤ g x) (n : ℕ) (x : E) :
    F^[n] g x ≤ g x :=
  (superharmonic_iterates F S hF hmono hg hFg n).2 x

theorem limit_le_of_superharmonic {E : Type*}
    (F : (E → ℝ) → (E → ℝ)) (S : Set (E → ℝ))
    (hF : ∀ u ∈ S, F u ∈ S)
    (hmono : ∀ u ∈ S, ∀ v ∈ S, (∀ x, u x ≤ v x) → ∀ x, F u x ≤ F v x)
    {g v : E → ℝ} (hg : g ∈ S) (hFg : ∀ x, F g x ≤ g x)
    (hlim : ∀ x, Tendsto (fun n : ℕ => F^[n] g x) atTop (𝓝 (v x))) :
    ∀ x, v x ≤ g x := by
  intro x
  exact le_of_tendsto' (hlim x) (fun n => iterate_le_of_superharmonic F S hF hmono hg hFg n x)

end S06P100


-- Inline checked component: Picard

set_option autoImplicit false

open MeasureTheory Filter Topology MDPFinance.Contracting BauerleRiederMDP.Contracting

namespace S06P100

lemma geometric_weighted_limit {E : Type*} (u : ℕ → E → ℝ)
    (b : E → ℝ) (q C : ℝ) (hq : q < 1)
    (hstep : ∀ n x, |u (n + 1) x - u n x| ≤ q ^ n * C * b x) :
    ∃ v : E → ℝ, (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x))) ∧
      ∀ n x, |u n x - v x| ≤ q ^ n / (1 - q) * C * b x := by
  have hdist (x : E) (n : ℕ) :
      dist (u n x) (u (n + 1) x) ≤ (C * b x) * q ^ n := by
    simpa [Real.dist_eq, abs_sub_comm, mul_assoc, mul_left_comm, mul_comm] using hstep n x
  have hex (x : E) : ∃ z : ℝ, Tendsto (fun n => u n x) atTop (𝓝 z) :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q (C * b x) hq (hdist x))
  choose v hv using hex
  refine ⟨v, hv, ?_⟩
  intro n x
  calc
    |u n x - v x| = dist (u n x) (v x) := (Real.dist_eq _ _).symm
    _ ≤ (C * b x) * q ^ n / (1 - q) :=
      dist_le_of_le_geometric_of_tendsto q (C * b x) hq (hdist x) (hv x) n
    _ = q ^ n / (1 - q) * C * b x := by ring

theorem weighted_picard {E : Type*} [MeasurableSpace E]
    (b : E → ℝ) (hb : ∀ x, 0 ≤ b x)
    (S : Set (E → ℝ)) (hsub : S ⊆ IBb b) (hclosed : IsClosedInIBb b S)
    (F : (E → ℝ) → (E → ℝ)) (hF : ∀ u ∈ S, F u ∈ S)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ u ∈ S, ∀ v ∈ S, ∀ C : ℝ, 0 ≤ C →
      (∀ x, |u x - v x| ≤ C * b x) → ∀ x, |F u x - F v x| ≤ q * C * b x)
    (g : E → ℝ) (hg : g ∈ S) :
    ∃ v, v ∈ S ∧ F v = v ∧
      (∀ x, Tendsto (fun n => (F^[n] g) x) atTop (𝓝 (v x))) ∧
      Tendsto (fun n => normb b (fun x => (F^[n] g) x - v x)) atTop (𝓝 0) ∧
      ∀ n, normb b (fun x => v x - (F^[n] g) x) ≤
        q ^ n / (1 - q) * normb b (fun x => F g x - g x) := by
  have hmem : ∀ n : ℕ, F^[n] g ∈ S := by
    intro n
    induction n with
    | zero => simpa using hg
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hF _ ih
  let C := normb b (fun x => F g x - g x)
  have hC : 0 ≤ C := normb_nonneg b hb _
  have hinit : ∀ x, |F g x - g x| ≤ C * b x :=
    abs_le_normb_mul b hb _ (ib_sub (hsub (hF g hg)) (hsub hg))
  have hstep : ∀ n x, |(F^[n + 1] g) x - (F^[n] g) x| ≤ q ^ n * C * b x := by
    intro n
    induction n with
    | zero => simpa using hinit
    | succ n ih =>
      intro x
      have h := hcontract (F^[n + 1] g) (hmem (n + 1))
        (F^[n] g) (hmem n) (q ^ n * C) (mul_nonneg (pow_nonneg hq0 _) hC) ih x
      simpa only [Function.iterate_succ_apply', pow_succ, mul_assoc,
        mul_left_comm, mul_comm] using h
  obtain ⟨v, hvlim, herr⟩ := geometric_weighted_limit (fun n => F^[n] g) b q C hq1 hstep
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have herrC (n : ℕ) : 0 ≤ q ^ n / (1 - q) * C :=
    mul_nonneg (div_nonneg (pow_nonneg hq0 _) hden.le) hC
  have hvmeas : Measurable v := measurable_of_tendsto_metrizable
    (fun n => (hsub (hmem n)).1) (tendsto_pi_nhds.mpr hvlim)
  obtain ⟨_, Cg, hCg, hgbound⟩ := hsub hg
  have hvb : v ∈ IBb b := by
    refine ⟨hvmeas, 1 / (1 - q) * C + Cg,
      add_nonneg (by simpa using herrC 0) hCg, ?_⟩
    intro x
    have h0 : |v x - g x| ≤ (1 / (1 - q) * C) * b x := by
      simpa only [Function.iterate_zero_apply, pow_zero, abs_sub_comm] using herr 0 x
    calc
      |v x| ≤ |v x - g x| + |g x| := by
        simpa only [sub_add_cancel] using abs_add_le (v x - g x) (g x)
      _ ≤ (1 / (1 - q) * C) * b x + Cg * b x := add_le_add h0 (hgbound x)
      _ = (1 / (1 - q) * C + Cg) * b x := by ring
  have hnorm (n : ℕ) : normb b (fun x => (F^[n] g) x - v x) ≤
      q ^ n / (1 - q) * C := normb_le_of_bound b hb _ (herrC n) (herr n)
  have hdecay : Tendsto (fun n : ℕ => q ^ n / (1 - q) * C) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).div_const (1 - q)).mul_const C
  have hnormlim : Tendsto (fun n => normb b (fun x => (F^[n] g) x - v x))
      atTop (𝓝 0) := squeeze_zero (fun n => normb_nonneg b hb _) hnorm hdecay
  have hvS : v ∈ S := hclosed (fun n => F^[n] g) v hmem hvb hnormlim
  have hfix : F v = v := by
    funext x
    have hnext : Tendsto (fun n => (F^[n + 1] g) x) atTop (𝓝 (F v x)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      have hbound (n : ℕ) : dist ((F^[n + 1] g) x) (F v x) ≤
          q * (q ^ n / (1 - q) * C) * b x := by
        have h := hcontract (F^[n] g) (hmem n) v hvS
          (q ^ n / (1 - q) * C) (herrC n) (herr n) x
        simpa only [Real.dist_eq, Function.iterate_succ_apply'] using h
      have hboundlim : Tendsto (fun n : ℕ => q * (q ^ n / (1 - q) * C) * b x)
          atTop (𝓝 0) := by
        simpa using (hdecay.const_mul q).mul_const (b x)
      exact squeeze_zero (fun n => dist_nonneg) hbound hboundlim
    exact tendsto_nhds_unique hnext ((hvlim x).comp (tendsto_add_atTop_nat 1))
  refine ⟨v, hvS, hfix, hvlim, hnormlim, ?_⟩
  intro n
  rw [normb_sub_comm b v (F^[n] g)]
  exact hnorm n

end S06P100


-- Inline checked component: Assembly

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open MDPFinance.Contracting BauerleRiederMDP.Contracting

namespace S06P100

theorem structure_of_picard {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hβαb : M.β * αb < 1)
    (IM : Set (E → ℝ)) (hIMsub : IM ⊆ IBb b) (hIMclosed : IsClosedInIBb b IM)
    (Δ : Set (E → A)) (hΔ : ∀ f ∈ Δ, IsDecisionRuleOf M f)
    (h0 : (0 : E → ℝ) ∈ IM)
    (hT : ∀ v ∈ IM, ∃ w ∈ IM, T M (fun y => (v y : EReal)) = fun y => (w y : EReal))
    (hmax : ∀ v ∈ IM, ∃ f ∈ Δ, IsMaximizerOf M (fun y => (v y : EReal)) f)
    (hpicard : ∀ g ∈ IM, ∃ v, v ∈ IM ∧ Treal M v = v ∧
      (∀ x, Tendsto (fun n : ℕ => ((Treal M)^[n] g) x) atTop (𝓝 (v x))) ∧
      Tendsto (fun n : ℕ => normb b (fun x => ((Treal M)^[n] g) x - v x))
        atTop (𝓝 0) ∧
      ∀ n : ℕ, normb b (fun x => v x - ((Treal M)^[n] g) x) ≤
        (M.β * αb)^n / (1 - M.β * αb) * normb b (fun x => Treal M g x - g x)) :
    -- a) Value iteration
    ((∀ x, Jinf M x = (((Jinf M x).toReal : ℝ) : EReal)) ∧
        (fun x => (Jinf M x).toReal) ∈ IM ∧
        T M (Jinf M) = Jinf M ∧
        ∀ x, Tendsto (fun n => Jn M M.r n x) atTop (𝓝 (Jinf M x))) ∧
      -- b) unique fixed point of T in IM
      (∀ v ∈ IM, T M (fun y => (v y : EReal)) = (fun y => (v y : EReal)) →
        ∀ x, (v x : EReal) = Jinf M x) ∧
      -- c) smallest r-superharmonic function in IM
      (∀ v ∈ IM, (∀ x, T M (fun y => (v y : EReal)) x ≤ (v x : EReal)) →
        ∀ x, Jinf M x ≤ (v x : EReal)) ∧
      -- d) a-posteriori error bound
      (∀ g ∈ IM, ∀ n : ℕ,
        normb b (fun x => (Jinf M x).toReal - (Treal M)^[n] g x) ≤
          (M.β * αb) ^ n / (1 - M.β * αb) * normb b (fun x => Treal M g x - g x)) ∧
      -- e) maximizers of J_∞ and optimal stationary policies
      ((∃ f ∈ Δ, IsMaximizerOf M (Jinf M) f) ∧
        ∀ fstar : E → A, IsMaximizerOf M (Jinf M) fstar →
          ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by
  have hF : ∀ u ∈ IM, Treal M u ∈ IM := fun u hu => (Treal_spec M IM hT hu).1
  have hmax' : ∀ u ∈ IM, ∃ f, IsMaximizerOf M (fun y => (u y : EReal)) f := by
    intro u hu
    obtain ⟨f, _, hf⟩ := hmax u hu
    exact ⟨f, hf⟩
  have hmono : ∀ u ∈ IM, ∀ v ∈ IM, (∀ x, u x ≤ v x) →
      ∀ x, Treal M u x ≤ Treal M v x := by
    intro u hu v hv hle
    exact Treal_mono M b cr αb hb IM hIMsub hT hmax' hu hv hle
  have fixcast (u : E → ℝ) (hu : u ∈ IM) (hfix : Treal M u = u) :
      ∀ x, T M (fun y => (u y : EReal)) x = (u x : EReal) := by
    intro x
    simpa only [hfix] using (Treal_spec M IM hT hu).2 x
  have identify (u : E → ℝ) (hu : u ∈ IM) (hfix : Treal M u = u) :
      (∀ x, (u x : EReal) = Jinf M x) ∧
      ∀ x, Tendsto (fun n => Jn M M.r n x) atTop (𝓝 (Jinf M x)) := by
    obtain ⟨f, hf⟩ := hmax' u hu
    have h := verification_with_tendsto M b cr αb hb hβαb u (hIMsub hu)
      (fixcast u hu hfix) f hf
    refine ⟨h.1, ?_⟩
    intro x
    simpa only [h.1 x] using h.2.2.2 x
  obtain ⟨v, hv, hvfix, hvconv, hvnorm, hverr⟩ := hpicard 0 h0
  have hid := identify v hv hvfix
  have hvJ : (fun x => (v x : EReal)) = Jinf M := funext hid.1
  have hvreal : (fun x => (Jinf M x).toReal) = v := by
    funext x
    rw [← hid.1 x]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, hid.2⟩
    · intro x
      rw [← hid.1 x]
      simp
    · rw [hvreal]
      exact hv
    · calc
        T M (Jinf M) = T M (fun x => (v x : EReal)) := congrArg (T M) hvJ.symm
        _ = (fun x => (v x : EReal)) := funext (fixcast v hv hvfix)
        _ = Jinf M := hvJ
  · intro u hu huEq
    have huFix : Treal M u = u := by
      funext x
      unfold Treal
      rw [huEq]
      simp
    exact (identify u hu huFix).1
  · intro u hu hsuper
    obtain ⟨w, hw, hwfix, hwconv, hwnorm, hwerr⟩ := hpicard u hu
    have hsuperR : ∀ x, Treal M u x ≤ u x := by
      intro x
      have h := hsuper x
      rw [(Treal_spec M IM hT hu).2 x] at h
      exact_mod_cast h
    have hwle := limit_le_of_superharmonic (Treal M) IM hF hmono hu hsuperR hwconv
    intro x
    rw [← (identify w hw hwfix).1 x]
    exact_mod_cast hwle x
  · intro g hg n
    obtain ⟨w, hw, hwfix, hwconv, hwnorm, hwerr⟩ := hpicard g hg
    have hwreal : ∀ x, (Jinf M x).toReal = w x := by
      intro x
      rw [← (identify w hw hwfix).1 x]
      simp
    simpa only [hwreal] using hwerr n
  · constructor
    · obtain ⟨f, hfΔ, hf⟩ := hmax v hv
      exact ⟨f, hfΔ, by simpa only [hvJ] using hf⟩
    · intro fstar hfstar
      have hf : IsMaximizerOf M (fun y => (v y : EReal)) fstar := by
        simpa only [hvJ] using hfstar
      exact (verification_with_tendsto M b cr αb hb hβαb v (hIMsub hv)
        (fixcast v hv hvfix) fstar hf).2.2.1

end S06P100


open MeasureTheory ProbabilityTheory Filter Topology
open MDPFinance.Contracting BauerleRiederMDP.Contracting

theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hβαb : M.β * αb < 1)
    (IM : Set (E → ℝ)) (hIMsub : IM ⊆ IBb b) (hIMclosed : IsClosedInIBb b IM)
    (Δ : Set (E → A)) (hΔ : ∀ f ∈ Δ, IsDecisionRuleOf M f)
    (h0 : (0 : E → ℝ) ∈ IM)
    (hT : ∀ v ∈ IM, ∃ w ∈ IM, T M (fun y => (v y : EReal)) = fun y => (w y : EReal))
    (hmax : ∀ v ∈ IM, ∃ f ∈ Δ, IsMaximizerOf M (fun y => (v y : EReal)) f) :
    -- a) Value iteration
    ((∀ x, Jinf M x = (((Jinf M x).toReal : ℝ) : EReal)) ∧
        (fun x => (Jinf M x).toReal) ∈ IM ∧
        T M (Jinf M) = Jinf M ∧
        ∀ x, Tendsto (fun n => Jn M M.r n x) atTop (𝓝 (Jinf M x))) ∧
      -- b) unique fixed point of T in IM
      (∀ v ∈ IM, T M (fun y => (v y : EReal)) = (fun y => (v y : EReal)) →
        ∀ x, (v x : EReal) = Jinf M x) ∧
      -- c) smallest r-superharmonic function in IM
      (∀ v ∈ IM, (∀ x, T M (fun y => (v y : EReal)) x ≤ (v x : EReal)) →
        ∀ x, Jinf M x ≤ (v x : EReal)) ∧
      -- d) a-posteriori error bound
      (∀ g ∈ IM, ∀ n : ℕ,
        normb b (fun x => (Jinf M x).toReal - (Treal M)^[n] g x) ≤
          (M.β * αb) ^ n / (1 - M.β * αb) * normb b (fun x => Treal M g x - g x)) ∧
      -- e) maximizers of J_∞ and optimal stationary policies
      ((∃ f ∈ Δ, IsMaximizerOf M (Jinf M) f) ∧
        ∀ fstar : E → A, IsMaximizerOf M (Jinf M) fstar →
          ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by
  have hmax' : ∀ v ∈ IM, ∃ f, IsMaximizerOf M (fun y => (v y : EReal)) f := by
    intro v hv
    obtain ⟨f, _, hf⟩ := hmax v hv
    exact ⟨f, hf⟩
  apply S06P100.structure_of_picard M b cr αb hb hβαb IM hIMsub hIMclosed
    Δ hΔ h0 hT hmax
  intro g hg
  apply S06P100.weighted_picard b hb.hb_nonneg IM hIMsub hIMclosed
    (Treal M) (fun u hu => (S06P100.Treal_spec M IM hT hu).1)
    (M.β * αb) (mul_nonneg M.hβ0.le hb.hαb) hβαb ?_ g hg
  intro u hu v hv C hC hbound x
  exact S06P100.Treal_weighted_lipschitz M b cr αb hb IM hIMsub hT hmax'
    hu hv hC hbound x

#print axioms solution
