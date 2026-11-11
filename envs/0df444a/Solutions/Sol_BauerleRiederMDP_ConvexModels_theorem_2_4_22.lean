-- Prove2me | solution 1 for BauerleRiederMDP.ConvexModels.theorem_2_4_22
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T09:45:11.198814+00:00
-- url     : https://prove2.me/submissions/5396c79e-58e5-44d2-ab7f-82f6eb5dec6f

import Mathlib.Tactic.Ring
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_BauerleRiederMDP_ConvexModels_ConvexOnVia
import Definitions.Def_BauerleRiederMDP_ConvexModels_StructureAssumption

open MeasureTheory ProbabilityTheory
open MDPFinance.StructuredModels

namespace S01.P063

variable {E A X : Type*} [MeasurableSpace E] [MeasurableSpace A]
  [MeasurableSpace X] {N : ℕ}

/-- The published extended integral is measurable in its kernel parameter. -/
theorem measurable_erealIntegral (K : Kernel X E) [IsSFiniteKernel K] {v : E → EReal}
    (hv : Measurable v) : Measurable (fun x => erealIntegral (K x) v) := by
  unfold erealIntegral
  exact ((hv.sup measurable_const).ereal_toENNReal.lintegral_kernel).coe_ereal_ennreal.add
    (((hv.neg.sup measurable_const).ereal_toENNReal.lintegral_kernel).coe_ereal_ennreal.neg)

/-- A positive-part bound passes through the nonnegative kernel integral. -/
theorem positiveIntegral_le (M : MarkovDecisionModel E A N) (b : E → ℝ)
    {cr cg αb : ℝ} (hb : IsUpperBoundingFunction M b cr cg αb)
    {n : ℕ} (hn : n < N) {v : E → EReal} {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ x, v x ⊔ 0 ≤ (c * b x : ℝ)) {xa : E × A} (hxa : xa ∈ M.D n) :
    (∫⁻ x, (v x ⊔ 0).toENNReal ∂M.Q n xa) ≤ ENNReal.ofReal (c * αb * b xa.1) := by
  calc
    (∫⁻ x, (v x ⊔ 0).toENNReal ∂M.Q n xa)
        ≤ ∫⁻ x, ENNReal.ofReal (c * b x) ∂M.Q n xa := by
      apply lintegral_mono
      intro x
      simpa only [EReal.real_coe_toENNReal] using EReal.toENNReal_le_toENNReal (hv x)
    _ = ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (b x) ∂M.Q n xa := by
      simp_rw [ENNReal.ofReal_mul hc]
      exact lintegral_const_mul _ hb.hb_meas.ennreal_ofReal
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (αb * b xa.1) :=
      mul_le_mul_of_nonneg_left (hb.hQ n hn xa hxa) zero_le
    _ = ENNReal.ofReal (c * αb * b xa.1) := by
      rw [← ENNReal.ofReal_mul hc, mul_assoc]

/-- The positive part is integrable even when the negative part is infinite. -/
theorem positiveIntegral_ne_top (M : MarkovDecisionModel E A N) (b : E → ℝ)
    {cr cg αb : ℝ} (hb : IsUpperBoundingFunction M b cr cg αb)
    {n : ℕ} (hn : n < N) {v : E → EReal} (hv : v ∈ IBbPlus b)
    {xa : E × A} (hxa : xa ∈ M.D n) :
    (∫⁻ x, (v x ⊔ 0).toENNReal ∂M.Q n xa) ≠ ⊤ := by
  obtain ⟨c, hc, hvc⟩ := hv.2.2
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (positiveIntegral_le M b hb hn hc hvc hxa)

/-- The extended integral is bounded above by the integral of its positive part. -/
theorem erealIntegral_le_positive (μ : Measure E) (v : E → EReal) :
    erealIntegral μ v ≤ (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) := by
  unfold erealIntegral
  exact le_trans (add_le_add le_rfl (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _)))
    (le_of_eq (add_zero _))

/-- The fixed-action Bellman value has a uniform finite upper bound. -/
theorem L_le (M : MarkovDecisionModel E A N) (b : E → ℝ)
    {cr cg αb : ℝ} (hb : IsUpperBoundingFunction M b cr cg αb)
    {n : ℕ} (hn : n < N) {v : E → EReal} {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ x, v x ⊔ 0 ≤ (c * b x : ℝ)) {xa : E × A} (hxa : xa ∈ M.D n) :
    L M n v xa ≤ (((cr + c * αb) * b xa.1 : ℝ) : EReal) := by
  have hi : erealIntegral (M.Q n xa) v ≤ ((c * αb * b xa.1 : ℝ) : EReal) := by
    refine (erealIntegral_le_positive _ _).trans ?_
    have hh := EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (positiveIntegral_le M b hb hn hc hv hxa)
    simpa only [EReal.coe_ennreal_ofReal, max_eq_left (mul_nonneg (mul_nonneg hc hb.hαb) (hb.hb_nonneg _))] using hh
  have hr : ((M.r n xa : ℝ) : EReal) ≤ ((cr * b xa.1 : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr ((le_max_left _ _).trans (hb.hr n hn xa hxa))
  refine (add_le_add hr hi).trans_eq ?_
  simp only [← EReal.coe_add]
  congr 1
  ring

/-- A measurable maximizer makes the Bellman operator measurable, with the
same one-sided weighted bound. No integrability of the negative part is needed. -/
theorem T_mem_IBbPlus (M : MarkovDecisionModel E A N) (b : E → ℝ)
    {cr cg αb : ℝ} (hb : IsUpperBoundingFunction M b cr cg αb)
    {n : ℕ} (hn : n < N) {v : E → EReal} (hv : v ∈ IBbPlus b)
    {f : E → A} (hf : IsMaximizer M n v f) : T M n v ∈ IBbPlus b := by
  obtain ⟨c, hc, hvc⟩ := hv.2.2
  have hT (x : E) : T M n v x ≤ (((cr + c * αb) * b x : ℝ) : EReal) := by
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact L_le M b hb hn hc hvc ha
  have hc' : 0 ≤ cr + c * αb := add_nonneg hb.hcr (mul_nonneg hc hb.hαb)
  refine ⟨?_, ?_, cr + c * αb, hc', ?_⟩
  · let : IsMarkovKernel (M.Q n) := ⟨M.hQ_prob n hn⟩
    have hL : Measurable (L M n v) :=
      (M.hr_meas n hn).coe_real_ereal.add (measurable_erealIntegral (M.Q n) hv.1)
    rw [← hf.2]
    exact hL.comp (measurable_id.prodMk hf.1.1)
  · intro x
    exact ne_of_lt ((hT x).trans_lt (EReal.coe_lt_top _))
  · intro x
    exact sup_le (hT x) (EReal.coe_nonneg.mpr (mul_nonneg hc' (hb.hb_nonneg x)))

/-- Convexity is preserved by addition for the published extended-real convention. -/
theorem convex_add {Y W : Type*} [AddCommGroup W] [Module ℝ W]
    (ι : Y → W) (D : Set Y) {f g : Y → EReal}
    (hf : BauerleRiederMDP.ConvexModels.ConvexOnVia ι D f)
    (hg : BauerleRiederMDP.ConvexModels.ConvexOnVia ι D g) :
    BauerleRiederMDP.ConvexModels.ConvexOnVia ι D (fun x => f x + g x) := by
  intro p hp q hq z hz α β hα hβ hαβ heq
  calc
    f z + g z ≤ ((α : EReal) * f p + (β : EReal) * f q) +
        ((α : EReal) * g p + (β : EReal) * g q) :=
      add_le_add (hf hp hq hz hα hβ hαβ heq) (hg hp hq hz hα hβ hαβ heq)
    _ = (α : EReal) * (f p + g p) + (β : EReal) * (f q + g q) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hα)
          (EReal.coe_ne_top α),
        EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hβ)
          (EReal.coe_ne_top β)]
      ac_rfl

/-- The Bellman supremum preserves convexity when every action is available at
all states. The action type need not carry a convexity structure. -/
theorem T_convex {d : ℕ} {SE : Set (Fin d → ℝ)}
    (M : MarkovDecisionModel SE A N) {n : ℕ} (hD : M.D n = Set.univ)
    {v : SE → EReal}
    (hQ : ∀ a : A, BauerleRiederMDP.ConvexModels.ConvexOnVia Subtype.val Set.univ
      (fun x => erealIntegral (M.Q n (x, a)) v))
    (hr : ∀ a : A, BauerleRiederMDP.ConvexModels.ConvexOnVia Subtype.val Set.univ
      (fun x => (M.r n (x, a) : EReal))) :
    BauerleRiederMDP.ConvexModels.ConvexOnVia Subtype.val Set.univ (T M n v) := by
  intro p hp q hq z hz α β hα hβ hαβ heq
  apply iSup_le
  intro a
  apply iSup_le
  intro ha
  have hLp : L M n v (p, a) ≤ T M n v p :=
    le_iSup_of_le a (le_iSup_of_le (show a ∈ M.Dx n p by simp [MarkovDecisionModel.Dx, hD]) le_rfl)
  have hLq : L M n v (q, a) ≤ T M n v q :=
    le_iSup_of_le a (le_iSup_of_le (show a ∈ M.Dx n q by simp [MarkovDecisionModel.Dx, hD]) le_rfl)
  have hL := convex_add Subtype.val Set.univ (hr a) (hQ a)
  exact (hL hp hq hz hα hβ hαβ heq).trans
    (add_le_add (mul_le_mul_of_nonneg_left hLp (EReal.coe_nonneg.mpr hα))
      (mul_le_mul_of_nonneg_left hLq (EReal.coe_nonneg.mpr hβ)))

end S01.P063

open MeasureTheory ProbabilityTheory
open MDPFinance.StructuredModels
open BauerleRiederMDP.ConvexModels

/-- The unchanged published root, assembled from local definition-only helpers. -/
theorem solution {d m N : ℕ} {SE : Set (Fin d → ℝ)} {SA : Set (Fin m → ℝ)}
    (hSE : MeasurableSet SE) (hSA : MeasurableSet SA)
    (M : MarkovDecisionModel SE SA N) (b : SE → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb)
    (Δ : ℕ → Set (SE → SA)) (hΔ : ∀ n < N, Δ n ⊆ {f | IsDecisionRule M n f})
    (hE : Convex ℝ SE) (hD : ∀ n < N, M.D n = Set.univ)
    (hQ : ∀ n < N, ∀ v ∈ IBbPlus b, ConvexOnVia Subtype.val Set.univ v →
      ∀ a : SA, ConvexOnVia Subtype.val Set.univ (fun x => erealIntegral (M.Q n (x, a)) v))
    (hr : ∀ n < N, ∀ a : SA, ConvexOnVia Subtype.val Set.univ (fun x => (M.r n (x, a) : EReal)))
    (hg : ConvexOnVia Subtype.val Set.univ (fun x => (M.g x : EReal)))
    (hmax : ∀ n < N, ∀ v ∈ IBbPlus b, ConvexOnVia Subtype.val Set.univ v →
      ∃ f ∈ Δ n, IsMaximizer M n v f) :
    StructureAssumption M (fun _ => {v ∈ IBbPlus b | ConvexOnVia Subtype.val Set.univ v}) Δ := by
  refine ⟨?_, hΔ, ?_, ?_, ?_⟩
  · intro n hn v hv
    exact ⟨hv.1.1, hv.1.2.1⟩
  · refine ⟨⟨M.hg_meas.coe_real_ereal, fun x => EReal.coe_ne_top _, cg, hb.hcg, ?_⟩, hg⟩
    intro x
    exact sup_le
      (EReal.coe_le_coe_iff.mpr ((le_max_left _ _).trans (hb.hg x)))
      (EReal.coe_nonneg.mpr (mul_nonneg hb.hcg (hb.hb_nonneg x)))
  · intro n hn v hv
    obtain ⟨f, hf, hfm⟩ := hmax n hn v hv.1 hv.2
    refine ⟨?_, S01.P063.T_mem_IBbPlus M b hb hn hv.1 hfm,
      S01.P063.T_convex M (hD n hn) (hQ n hn v hv.1 hv.2) (hr n hn)⟩
    intro xa hxa
    exact Or.inl (S01.P063.positiveIntegral_ne_top M b hb hn hv.1 hxa)
  · intro n hn v hv
    exact hmax n hn v hv.1 hv.2

#print axioms solution
