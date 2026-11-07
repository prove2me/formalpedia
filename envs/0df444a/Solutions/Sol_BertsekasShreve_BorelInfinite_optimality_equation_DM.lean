-- Prove2me | solution 1 for BertsekasShreve.BorelInfinite.optimality_equation_DM
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:57:41.53981+00:00
-- url     : https://prove2.me/submissions/84e7e8de-7e9e-4bc5-9758-dab4fc125d03

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels
import Definitions.Def_BertsekasShreve_BorelInfinite_DetModel
import Theorems.Thm_BertsekasShreve_AnalyticSelection_analytic_universallyMeasurable

open MeasureTheory ProbabilityTheory
open BertsekasShreve.AnalyticSelection

namespace BSSignAux

universe u v

lemma secondCountable_of_isBorel {X : Type u} [TopologicalSpace X] [IsBorelSpace X] :
    SecondCountableTopology X := by
  obtain ⟨Z, _, _, _, B, _, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  exact e.isEmbedding.secondCountableTopology

lemma isBorel_prod {X : Type u} {Y : Type v} [TopologicalSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [IsBorelSpace Y] : IsBorelSpace (X × Y) := by
  obtain ⟨Z, i1, i2, i3, B, hB, ⟨e⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := X)
  obtain ⟨Z', j1, j2, j3, B', hB', ⟨e'⟩⟩ := IsBorelSpace.exists_homeomorph_borel (X := Y)
  letI := i1; letI := j1
  refine ⟨⟨Z × Z', inferInstance, inferInstance, inferInstance, B ×ˢ B', ?_, ⟨?_⟩⟩⟩
  · letI : MeasurableSpace Z := borel Z
    haveI : BorelSpace Z := ⟨rfl⟩
    letI : MeasurableSpace Z' := borel Z'
    haveI : BorelSpace Z' := ⟨rfl⟩
    have h := hB.prod hB'
    rwa [(Prod.borelSpace (α := Z) (β := Z')).measurable_eq] at h
  · exact (e.prodCongr e').trans (Homeomorph.Set.prod B B').symm

lemma um_of_analyticallyMeasurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (hA : ∀ A : Set X, AnalyticSet A → IsUniversallyMeasurable A)
    (E : Set X) (hE : IsAnalyticallyMeasurable E) : IsUniversallyMeasurable E := by
  unfold IsAnalyticallyMeasurable analyticSigmaAlgebra at hE
  induction hE with
  | basic s hs => exact hA s hs
  | empty => intro p _; exact nullMeasurableSet_empty
  | compl s _ ih => intro p hp; exact (ih p hp).compl
  | iUnion f _ ih => intro p hp; exact NullMeasurableSet.iUnion fun i => ih i p hp

end BSSignAux


open BertsekasShreve.BorelInfinite BertsekasShreve.FiniteHorizon

namespace BSDMAux

lemma badd_coe (u v : ENNReal) : badd (u : EReal) (v : EReal) = ((u + v : ENNReal) : EReal) := by
  unfold badd
  by_cases hu : u = ⊤
  · simp [hu]
  by_cases hv : v = ⊤
  · simp [hv]
  rw [if_neg (by simp [hu, hv]), EReal.coe_ennreal_add]

lemma badd_neg_coe (u v : ENNReal) :
    badd (-(u : EReal)) (-(v : EReal)) = -((u + v : ENNReal) : EReal) := by
  unfold badd
  rw [if_neg (by simp [EReal.neg_eq_top_iff, EReal.coe_ennreal_ne_bot]),
    EReal.coe_ennreal_add, EReal.neg_add (Or.inl (EReal.coe_ennreal_ne_bot u))
      (Or.inr (EReal.coe_ennreal_ne_bot v)), sub_eq_add_neg]

lemma bsub_zero (X : ENNReal) : bsub X 0 = (X : EReal) := by
  unfold bsub; split_ifs with h
  · simp [h]
  · simp

lemma zero_bsub (Y : ENNReal) : bsub 0 Y = -(Y : EReal) := by
  unfold bsub; rw [if_neg ENNReal.zero_ne_top, EReal.coe_ennreal_zero, zero_sub]

lemma mul_coe {α : ℝ} (hα : 0 ≤ α) (X : ENNReal) :
    (α : EReal) * (X : EReal) = ((ENNReal.ofReal α * X : ENNReal) : EReal) := by
  rw [EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hα]

lemma tsum_shift (α : ℝ) (hα : 0 ≤ α) (a : ℕ → ENNReal) :
    ∑' k : ℕ, ENNReal.ofReal (α ^ k) * a k =
      a 0 + ENNReal.ofReal α * ∑' k : ℕ, ENNReal.ofReal (α ^ k) * a (k + 1) := by
  rw [tsum_eq_zero_add' ENNReal.summable, ← ENNReal.tsum_mul_left]
  congr 1
  · simp
  · refine tsum_congr fun k => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul hα, pow_succ, mul_comm α]

/-- The abstract one-step decomposition of the cost `Σ α^k (a_k − b_k)`. -/
lemma decomp (α : ℝ) (hα : 0 < α) (a b : ℕ → ENNReal)
    (hcase : (∀ k, b k = 0) ∨ (∀ k, a k = 0) ∨
      (α < 1 ∧ ∃ B : ℝ, ∀ k, a k ≤ ENNReal.ofReal B ∧ b k ≤ ENNReal.ofReal B)) :
    bsub (∑' k : ℕ, ENNReal.ofReal (α ^ k) * a k) (∑' k : ℕ, ENNReal.ofReal (α ^ k) * b k) =
      badd (if a 0 = ⊤ then ⊤ else (a 0 : EReal) - (b 0 : EReal))
        ((α : EReal) * bsub (∑' k : ℕ, ENNReal.ofReal (α ^ k) * a (k + 1))
          (∑' k : ℕ, ENNReal.ofReal (α ^ k) * b (k + 1))) := by
  rw [tsum_shift α hα.le a, tsum_shift α hα.le b]
  set X := ∑' k : ℕ, ENNReal.ofReal (α ^ k) * a (k + 1)
  set Y := ∑' k : ℕ, ENNReal.ofReal (α ^ k) * b (k + 1)
  rcases hcase with hb | ha | ⟨hα1, B, hB⟩
  · have hY : Y = 0 := by simp [Y, hb]
    rw [hY, hb 0, mul_zero, add_zero, bsub_zero, bsub_zero, mul_coe hα.le]
    have : (if a 0 = ⊤ then ⊤ else (a 0 : EReal) - ((0 : ENNReal) : EReal)) = (a 0 : EReal) := by
      split_ifs with h
      · simp [h]
      · simp
    rw [this, badd_coe]
  · have hX : X = 0 := by simp [X, ha]
    rw [hX, ha 0, mul_zero, add_zero, zero_bsub, zero_bsub, mul_neg, mul_coe hα.le]
    rw [if_neg ENNReal.zero_ne_top, EReal.coe_ennreal_zero, zero_sub, badd_neg_coe]
  · -- bounded case: all quantities are finite
    have hgeo : ∑' k : ℕ, ENNReal.ofReal (α ^ k) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hα.le k)
        (summable_geometric_of_lt_one hα.le hα1)]
      exact ENNReal.ofReal_ne_top
    have fin : ∀ c : ℕ → ENNReal, (∀ k, c k ≤ ENNReal.ofReal B) →
        ∑' k : ℕ, ENNReal.ofReal (α ^ k) * c k ≠ ⊤ := by
      intro c hc
      refine ne_top_of_le_ne_top (b := ∑' k : ℕ, ENNReal.ofReal (α ^ k) * ENNReal.ofReal B) ?_
        (ENNReal.tsum_le_tsum fun k => by gcongr; exact hc k)
      rw [ENNReal.tsum_mul_right]
      exact ENNReal.mul_ne_top hgeo ENNReal.ofReal_ne_top
    have hX : X ≠ ⊤ := fin _ fun k => (hB (k + 1)).1
    have hY : Y ≠ ⊤ := fin _ fun k => (hB (k + 1)).2
    have ha0 : a 0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB 0).1
    have hb0 : b 0 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB 0).2
    have hαX : ENNReal.ofReal α * X ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX
    have hαY : ENNReal.ofReal α * Y ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY
    unfold bsub
    rw [if_neg (ENNReal.add_ne_top.mpr ⟨ha0, hαX⟩), if_neg hX, if_neg ha0]
    rw [← EReal.coe_ennreal_toReal (ENNReal.add_ne_top.mpr ⟨ha0, hαX⟩),
      ← EReal.coe_ennreal_toReal (ENNReal.add_ne_top.mpr ⟨hb0, hαY⟩),
      ← EReal.coe_ennreal_toReal hX, ← EReal.coe_ennreal_toReal hY,
      ← EReal.coe_ennreal_toReal ha0, ← EReal.coe_ennreal_toReal hb0]
    rw [ENNReal.toReal_add ha0 hαX, ENNReal.toReal_add hb0 hαY, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le]
    have cs : ∀ x y : ℝ, (x : EReal) - (y : EReal) = ((x - y : ℝ) : EReal) :=
      fun x y => (EReal.coe_sub x y).symm
    have cm : ∀ x y : ℝ, (x : EReal) * (y : EReal) = ((x * y : ℝ) : EReal) :=
      fun x y => (EReal.coe_mul x y).symm
    have ca : ∀ x y : ℝ, (x : EReal) + (y : EReal) = ((x + y : ℝ) : EReal) :=
      fun x y => (EReal.coe_add x y).symm
    rw [cs, cs, cs, cm]
    unfold badd
    rw [if_neg (by simp only [EReal.coe_ne_top, or_self, not_false_eq_true]), ca]
    congr 1
    ring

end BSDMAux


open BertsekasShreve.BorelInfinite BertsekasShreve.FiniteHorizon

namespace BSDMAux

lemma badd_real (r α t : ℝ) : badd (r : EReal) ((α : EReal) * (t : EReal)) = ((r + α * t : ℝ) : EReal) := by
  unfold badd
  rw [← EReal.coe_mul, if_neg (by simp only [EReal.coe_ne_top, or_self, not_false_eq_true]),
    ← EReal.coe_add]

lemma phi_mono (c : EReal) {α : ℝ} (hα : 0 < α) : Monotone (fun x : EReal => badd c ((α : EReal) * x)) := by
  intro x y hxy
  have hm : (α : EReal) * x ≤ (α : EReal) * y :=
    mul_le_mul_of_nonneg_left hxy (by exact_mod_cast hα.le)
  simp only
  unfold badd
  by_cases hc : c = ⊤
  · simp [hc]
  by_cases hy : (α : EReal) * y = ⊤
  · simp [hy]
  have hx : (α : EReal) * x ≠ ⊤ := ne_top_of_le_ne_top hy hm
  rw [if_neg (by simp [hc, hx]), if_neg (by simp [hc, hy])]
  exact add_le_add_right hm c

lemma phi_usc (c : EReal) {α : ℝ} (hα : 0 < α) (x y : EReal)
    (h : badd c ((α : EReal) * x) < y) : ∃ x', x < x' ∧ badd c ((α : EReal) * x') < y := by
  have hy : y ≠ ⊥ := ne_bot_of_gt h
  induction c using EReal.rec with
  | top => simp [badd] at h
  | bot =>
    induction x using EReal.rec with
    | top => simp [badd, EReal.coe_mul_top_of_pos hα] at h
    | bot =>
      refine ⟨((1 : ℝ) : EReal), EReal.bot_lt_coe 1, ?_⟩
      unfold badd; rw [← EReal.coe_mul, if_neg (by simp), EReal.bot_add]
      exact Ne.bot_lt hy
    | coe t =>
      refine ⟨((t + 1 : ℝ) : EReal), by exact_mod_cast (by linarith : t < t + 1), ?_⟩
      unfold badd; rw [← EReal.coe_mul, if_neg (by simp only [bot_ne_top, EReal.coe_ne_top, or_self, not_false_eq_true]), EReal.bot_add]
      exact Ne.bot_lt hy
  | coe r =>
    induction y using EReal.rec with
    | bot => exact absurd rfl hy
    | top =>
      induction x using EReal.rec with
      | top => simp [badd, EReal.coe_mul_top_of_pos hα] at h
      | bot => exact ⟨((0 : ℝ) : EReal), EReal.bot_lt_coe 0, by rw [badd_real]; exact EReal.coe_lt_top _⟩
      | coe t => exact ⟨((t + 1 : ℝ) : EReal), by exact_mod_cast (by linarith : t < t + 1),
          by rw [badd_real]; exact EReal.coe_lt_top _⟩
    | coe s =>
      induction x using EReal.rec with
      | top => simp [badd, EReal.coe_mul_top_of_pos hα] at h
      | bot =>
        refine ⟨(((s - r - 1) / α : ℝ) : EReal), EReal.bot_lt_coe _, ?_⟩
        rw [badd_real]
        exact_mod_cast (by field_simp; linarith : r + α * ((s - r - 1) / α) < s)
      | coe t =>
        rw [badd_real] at h
        have h' : r + α * t < s := by exact_mod_cast h
        refine ⟨((t + (s - r - α * t) / (2 * α) : ℝ) : EReal), ?_, ?_⟩
        · have : 0 < (s - r - α * t) / (2 * α) := div_pos (by linarith) (by linarith)
          exact_mod_cast (by linarith : t < t + (s - r - α * t) / (2 * α))
        · rw [badd_real]
          have e : r + α * (t + (s - r - α * t) / (2 * α)) = (r + α * t + s) / 2 := by
            field_simp; ring
          rw [e]; exact_mod_cast (by linarith : (r + α * t + s) / 2 < s)

lemma phi_iInf (c : EReal) {α : ℝ} (hα : 0 < α) {ι : Sort*} (f : ι → EReal) :
    ⨅ i, badd c ((α : EReal) * f i) = badd c ((α : EReal) * ⨅ i, f i) := by
  apply le_antisymm
  · by_contra hcon
    rw [not_le] at hcon
    obtain ⟨x', hx', hlt⟩ := phi_usc c hα _ _ hcon
    obtain ⟨i, hi⟩ := iInf_lt_iff.mp hx'
    have := (phi_mono c hα hi.le).trans_lt hlt
    exact absurd (iInf_le (fun i => badd c ((α : EReal) * f i)) i) (not_le.mpr this)
  · exact le_iInf fun i => phi_mono c hα (iInf_le f i)

end BSDMAux


open MeasureTheory ProbabilityTheory
open BertsekasShreve.AnalyticSelection BertsekasShreve.BorelInfinite BertsekasShreve.FiniteHorizon

namespace BSDMAux

variable {S C W : Type*}
    [TopologicalSpace S] [IsBorelSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [IsBorelSpace C] [MeasurableSpace C] [BorelSpace C]
    [MeasurableSpace W]

lemma measurable_t (M : Model S C W) : Measurable M.t := by
  haveI := M.p_markov
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hf : Measurable (fun zw : (S × C) × W => M.f (zw.1.1, zw.1.2, zw.2)) :=
    M.f_measurable.comp (by fun_prop)
  have key : (fun z => M.t z s) =
      fun z => M.p z (Prod.mk z ⁻¹' ((fun zw : (S × C) × W => M.f (zw.1.1, zw.1.2, zw.2)) ⁻¹' s)) := by
    funext z
    simp only [Model.t]
    have hz : Measurable (fun w => M.f (z.1, z.2, w)) := M.f_measurable.comp (by fun_prop)
    rw [Measure.map_apply hz hs]
    rfl
  rw [key]
  exact Kernel.measurable_kernel_prodMk_left (hf hs)

lemma fbar_isProb (M : Model S C W) (q : Measure (S × C)) [IsProbabilityMeasure q] :
    IsProbabilityMeasure (M.fbar q) := by
  haveI := M.p_markov
  constructor
  simp only [Model.fbar]
  rw [Measure.bind_apply MeasurableSet.univ (measurable_t M).aemeasurable]
  have : ∀ z, M.t z Set.univ = 1 := by
    intro z
    simp only [Model.t]
    have hf : Measurable (fun w => M.f (z.1, z.2, w)) := M.f_measurable.comp (by fun_prop)
    rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ, measure_univ]
  simp [this]

lemma ae_Γ_of_Ubar (M : Model S C W) (p : Measure S) (q : Measure (S × C)) (hq : q ∈ M.Ubar p) :
    ∀ᵐ z ∂q, z ∈ M.Γ := by
  haveI : SecondCountableTopology S := BSSignAux.secondCountable_of_isBorel
  haveI : SecondCountableTopology C := BSSignAux.secondCountable_of_isBorel
  haveI : IsBorelSpace (S × C) := BSSignAux.isBorel_prod
  haveI : IsProbabilityMeasure q := hq.1
  have hn : NullMeasurableSet M.Γ q :=
    analytic_universallyMeasurable _ M.graph_analytic q inferInstance
  rw [ae_iff]
  show q M.Γᶜ = 0
  rw [measure_compl₀ hn (measure_ne_top _ _), hq.2.1, measure_univ, tsub_self]

lemma traj (M : Model S C W) (π : M.DPolicy) (p : Measure S) [IsProbabilityMeasure p] :
    ∀ k, IsProbabilityMeasure (π.state p k) ∧ π.ctrl p k ∈ M.Ubar (π.state p k) := by
  intro k
  induction k with
  | zero =>
    exact ⟨by simpa [Model.DPolicy.state] using (inferInstance : IsProbabilityMeasure p),
      π.admissible 0 _ (by simpa [Model.DPolicy.state] using (inferInstance : IsProbabilityMeasure p))⟩
  | succ k ih =>
    have h1 : IsProbabilityMeasure (π.state p (k + 1)) := by
      haveI : IsProbabilityMeasure (π.ctrl p k) := ih.2.1
      exact fbar_isProb M (π.ctrl p k)
    exact ⟨h1, π.admissible (k + 1) _ h1⟩

/-- the shifted sequences -/
lemma ctrl_succ (M : Model S C W) (π π' : M.DPolicy) (p : Measure S)
    (h : ∀ k, π.μ (k + 1) = π'.μ k) :
    ∀ k, π.ctrl p (k + 1) = π'.ctrl (M.fbar (π.ctrl p 0)) k := by
  have hs : ∀ k, π.state p (k + 1) = π'.state (M.fbar (π.ctrl p 0)) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show M.fbar (π.μ (k + 1) (π.state p (k + 1))) = M.fbar (π'.μ k (π'.state _ k))
      rw [h k, ih]
  intro k
  show π.μ (k + 1) (π.state p (k + 1)) = π'.μ k (π'.state _ k)
  rw [h k, hs k]

/-- the case condition on the sequences `∫ g⁺ dq_k`, `∫ g⁻ dq_k` along a trajectory -/
lemma seq_case (M : Model S C W) (hcase : M.CaseP ∨ M.CaseN ∨ M.CaseD) (π : M.DPolicy)
    (p : Measure S) [IsProbabilityMeasure p] :
    (∀ k, ∫⁻ z, (-(M.g z.1 z.2)).toENNReal ∂(π.ctrl p k) = 0) ∨
    (∀ k, ∫⁻ z, (M.g z.1 z.2).toENNReal ∂(π.ctrl p k) = 0) ∨
    (M.α < 1 ∧ ∃ B : ℝ, ∀ k, ∫⁻ z, (M.g z.1 z.2).toENNReal ∂(π.ctrl p k) ≤ ENNReal.ofReal B ∧
      ∫⁻ z, (-(M.g z.1 z.2)).toENNReal ∂(π.ctrl p k) ≤ ENNReal.ofReal B) := by
  have hae : ∀ k, ∀ᵐ z ∂(π.ctrl p k), z ∈ M.Γ := fun k =>
    ae_Γ_of_Ubar M _ _ (traj M π p k).2
  rcases hcase with hP | hN | ⟨hα1, b, hb⟩
  · left; intro k
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hae k] with z hz
    rw [EReal.toENNReal_eq_zero_iff, EReal.neg_le, neg_zero]
    exact hP z.1 z.2 hz
  · right; left; intro k
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hae k] with z hz
    rw [EReal.toENNReal_eq_zero_iff]
    exact hN z.1 z.2 hz
  · right; right
    refine ⟨hα1, max b 0, fun k => ?_⟩
    haveI : IsProbabilityMeasure (π.ctrl p k) := (traj M π p k).2.1
    have bnd : ∀ G : S × C → EReal, (∀ z ∈ M.Γ, G z ≤ ((max b 0 : ℝ) : EReal)) →
        ∫⁻ z, (G z).toENNReal ∂(π.ctrl p k) ≤ ENNReal.ofReal (max b 0) := by
      intro G hG
      calc ∫⁻ z, (G z).toENNReal ∂(π.ctrl p k) ≤ ∫⁻ _, ENNReal.ofReal (max b 0) ∂(π.ctrl p k) := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae k] with z hz
            simpa using EReal.toENNReal_le_toENNReal (hG z hz)
        _ = ENNReal.ofReal (max b 0) := by simp
    refine ⟨bnd _ fun z hz => (hb z.1 z.2 hz).2.trans (by exact_mod_cast le_max_left b 0),
      bnd _ fun z hz => ?_⟩
    have := (hb z.1 z.2 hz).1
    rw [EReal.neg_le] at this
    exact this.trans (by exact_mod_cast le_max_left b 0)

end BSDMAux


open MeasureTheory ProbabilityTheory
open BertsekasShreve.AnalyticSelection BertsekasShreve.BorelInfinite BertsekasShreve.FiniteHorizon

namespace BSDMAux

variable {S C W : Type*}
    [TopologicalSpace S] [IsBorelSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [IsBorelSpace C] [MeasurableSpace C] [BorelSpace C]
    [MeasurableSpace W]

lemma cost_decomp (M : Model S C W) (hcase : M.CaseP ∨ M.CaseN ∨ M.CaseD) (π π' : M.DPolicy)
    (p : Measure S) [IsProbabilityMeasure p] (h : ∀ k, π.μ (k + 1) = π'.μ k) :
    π.cost p = badd (M.gbar (π.ctrl p 0)) ((M.α : EReal) * π'.cost (M.fbar (π.ctrl p 0))) := by
  have hc := seq_case M hcase π p
  have hd := decomp M.α M.α_pos (fun k => ∫⁻ z, (M.g z.1 z.2).toENNReal ∂(π.ctrl p k))
    (fun k => ∫⁻ z, (-(M.g z.1 z.2)).toENNReal ∂(π.ctrl p k)) (by tauto)
  unfold Model.DPolicy.cost
  rw [hd]
  simp only [ctrl_succ M π π' p h]
  rfl

/-- the shifted policy `(μ̄₁, μ̄₂, …)` -/
def shiftP {M : Model S C W} (π : M.DPolicy) : M.DPolicy :=
  ⟨fun k => π.μ (k + 1), fun k => π.admissible (k + 1)⟩

open Classical in
/-- first-stage map of `consP` -/
noncomputable def consμ0 {M : Model S C W} (p : Measure S) (q : Measure (S × C))
    (π' : M.DPolicy) : Measure S → Measure (S × C) :=
  fun p' => if p' = p then q else π'.μ 0 p'

lemma consμ0_self {M : Model S C W} (p : Measure S) (q : Measure (S × C)) (π' : M.DPolicy) :
    consμ0 p q π' p = q := by simp [consμ0]

lemma consμ0_mem {M : Model S C W} (p : Measure S) (q : Measure (S × C)) (hq : q ∈ M.Ubar p)
    (π' : M.DPolicy) (p' : Measure S) (hp' : IsProbabilityMeasure p') :
    consμ0 p q π' p' ∈ M.Ubar p' := by
  unfold consμ0
  split_ifs with he
  · subst he; exact hq
  · exact π'.admissible 0 p' hp'

/-- the policy using `q` at `p` in the first stage, then `π'` -/
noncomputable def consP {M : Model S C W} (p : Measure S) (q : Measure (S × C)) (hq : q ∈ M.Ubar p)
    (π' : M.DPolicy) : M.DPolicy where
  μ := fun k => match k with
    | 0 => consμ0 p q π'
    | j + 1 => π'.μ j
  admissible := by
    intro k p' hp'
    cases k with
    | zero => exact consμ0_mem p q hq π' p' hp'
    | succ j => exact π'.admissible j p' hp'

end BSDMAux

open BSDMAux in
theorem solution {S C W : Type*}
    [TopologicalSpace S] [BertsekasShreve.AnalyticSelection.IsBorelSpace S] [MeasurableSpace S] [BorelSpace S] [Nonempty S]
    [TopologicalSpace C] [BertsekasShreve.AnalyticSelection.IsBorelSpace C] [MeasurableSpace C] [BorelSpace C] [Nonempty C]
    [TopologicalSpace W] [BertsekasShreve.AnalyticSelection.IsBorelSpace W] [MeasurableSpace W] [BorelSpace W] [Nonempty W]
    (M : Model S C W)
    (hcase : M.CaseP ∨ M.CaseN ∨ M.CaseD) (p : Measure S) [IsProbabilityMeasure p] :
    M.Jbarstar p = M.Tbar M.Jbarstar p := by
  apply le_antisymm
  · refine le_iInf₂ fun q hq => ?_
    haveI : IsProbabilityMeasure q := hq.1
    have h1 : M.Jbarstar p ≤ ⨅ π' : M.DPolicy, (consP p q hq π').cost p :=
      le_iInf fun π' => iInf_le _ _
    have h2 : ∀ π' : M.DPolicy, (consP p q hq π').cost p =
        badd (M.gbar q) ((M.α : EReal) * π'.cost (M.fbar q)) := by
      intro π'
      have hq0 : (consP p q hq π').ctrl p 0 = q := by
        exact consμ0_self p q π'
      rw [cost_decomp M hcase _ π' p (fun k => rfl), hq0]
    simp only [h2] at h1
    rw [phi_iInf _ M.α_pos] at h1
    exact h1
  · refine le_iInf fun π => ?_
    have hq0 : π.ctrl p 0 ∈ M.Ubar p := (traj M π p 0).2
    calc M.Tbar M.Jbarstar p
        ≤ badd (M.gbar (π.ctrl p 0)) ((M.α : EReal) * M.Jbarstar (M.fbar (π.ctrl p 0))) :=
          iInf₂_le (f := fun q _ => badd (M.gbar q) ((M.α : EReal) * M.Jbarstar (M.fbar q))) _ hq0
      _ ≤ badd (M.gbar (π.ctrl p 0)) ((M.α : EReal) * (shiftP π).cost (M.fbar (π.ctrl p 0))) :=
          phi_mono _ M.α_pos (iInf_le _ _)
      _ = π.cost p := (cost_decomp M hcase π (shiftP π) p (fun k => rfl)).symm
