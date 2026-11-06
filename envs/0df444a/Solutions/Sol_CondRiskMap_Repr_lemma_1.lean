-- Prove2me | solution 1 for CondRiskMap.Repr.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:33:20.2894+00:00
-- url     : https://prove2.me/submissions/1f344447-9c4c-4079-b430-6092549cef44

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Setting

open CondRiskMap.Repr MeasureTheory

namespace CRMLemma1Counter

universe u v w

def Ω0 : Type u := ULift.{u} (ℕ → Bool)

instance : MeasurableSpace Ω0.{u} := ⊤
instance : MeasurableSingletonClass Ω0.{u} := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
instance : Nonempty Ω0.{u} := ⟨ULift.up fun _ => false⟩

abbrev Ωb : Type := ℕ → Bool

def up (t : Ωb) : Ω0.{u} := ULift.up t
def dn (x : Ω0.{u}) : Ωb := ULift.down x

lemma ms (s : Set Ω0) : MeasurableSet s := MeasurableSpace.measurableSet_top

/-- weighted sum `∑ μ(t) X(t)` -/
noncomputable def ip {α : Type*} (X : α → ℝ) (μ : α →₀ ℝ) : ℝ := μ.sum fun t a => a * X t

noncomputable def toM : (Ω0 →₀ ℝ) →ₗ[ℝ] SignedMeasure Ω0 :=
  Finsupp.linearCombination ℝ (fun t => (Measure.dirac t).toSignedMeasure)

lemma ip_add_right {α : Type*} (X : α → ℝ) (μ ν : α →₀ ℝ) : ip X (μ + ν) = ip X μ + ip X ν := by
  unfold ip
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma ip_single {α : Type*} (X : α → ℝ) (t : α) (a : ℝ) : ip X (Finsupp.single t a) = a * X t := by
  unfold ip; exact Finsupp.sum_single_index (zero_mul _)

lemma toM_apply (μ : Ω0 →₀ ℝ) (A : Set Ω0) : toM μ A = ip (A.indicator 1) μ := by
  induction μ using Finsupp.induction_linear with
  | zero => simp [ip]
  | add f g hf hg => rw [map_add, VectorMeasure.add_apply, hf, hg, ip_add_right]
  | single t a =>
    rw [ip_single]
    simp only [toM, Finsupp.linearCombination_single, VectorMeasure.smul_apply, smul_eq_mul]
    rw [Measure.toSignedMeasure_apply_measurable (ms A)]
    congr 1
    by_cases h : t ∈ A <;> simp [h, Measure.real]

noncomputable def Pm (μ : Ω0 →₀ ℝ) : Measure Ω0 :=
  ∑ t ∈ μ.support, (μ t).toNNReal • Measure.dirac t

noncomputable def Nm (μ : Ω0 →₀ ℝ) : Measure Ω0 :=
  ∑ t ∈ μ.support, (-μ t).toNNReal • Measure.dirac t

lemma Pm_apply (μ : Ω0 →₀ ℝ) (A : Set Ω0) :
    Pm μ A = ∑ t ∈ μ.support, ((μ t).toNNReal : ENNReal) * A.indicator 1 t := by
  simp only [Pm, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ (ms A),
    ENNReal.smul_def, smul_eq_mul]

lemma Nm_apply (μ : Ω0 →₀ ℝ) (A : Set Ω0) :
    Nm μ A = ∑ t ∈ μ.support, ((-μ t).toNNReal : ENNReal) * A.indicator 1 t := by
  simp only [Nm, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply' _ (ms A),
    ENNReal.smul_def, smul_eq_mul]

instance (μ : Ω0 →₀ ℝ) : IsFiniteMeasure (Pm μ) := ⟨by
  rw [Pm_apply]
  exact ENNReal.sum_lt_top.mpr fun t _ => ENNReal.mul_lt_top ENNReal.coe_lt_top
    (by by_cases h : t ∈ (Set.univ : Set Ω0) <;> simp)⟩

instance (μ : Ω0 →₀ ℝ) : IsFiniteMeasure (Nm μ) := ⟨by
  rw [Nm_apply]
  exact ENNReal.sum_lt_top.mpr fun t _ => ENNReal.mul_lt_top ENNReal.coe_lt_top
    (by by_cases h : t ∈ (Set.univ : Set Ω0) <;> simp)⟩


lemma ip_eq {α : Type*} (X : α → ℝ) (μ : α →₀ ℝ) : ip X μ = ∑ t ∈ μ.support, μ t * X t := rfl

lemma toM_eq (μ : Ω0 →₀ ℝ) : toM μ = (Pm μ).toSignedMeasure - (Nm μ).toSignedMeasure := by
  ext A hA
  rw [VectorMeasure.sub_apply, Measure.toSignedMeasure_apply_measurable hA,
    Measure.toSignedMeasure_apply_measurable hA, toM_apply, ip_eq, Measure.real, Measure.real,
    Pm_apply, Nm_apply, ENNReal.toReal_sum (fun t _ => by
      by_cases h : t ∈ A <;> simp [h]),
    ENNReal.toReal_sum (fun t _ => by by_cases h : t ∈ A <;> simp [h]), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : t ∈ A
  · simp only [h, Set.indicator_of_mem, Pi.one_apply, mul_one, ENNReal.coe_toReal,
      Real.coe_toNNReal']
    exact (max_zero_sub_max_neg_zero_eq_self (μ t)).symm
  · simp [h]

lemma ms_PN (μ : Ω0 →₀ ℝ) : Pm μ ⟂ₘ Nm μ := by
  refine ⟨{t | μ t ≤ 0}, ms _, ?_, ?_⟩
  · rw [Pm_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases h : μ t ≤ 0
    · simp [Real.toNNReal_of_nonpos h]
    · simp [Set.indicator_of_notMem (show t ∉ {t | μ t ≤ 0} from h)]
  · rw [Nm_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases h : μ t ≤ 0
    · have : t ∉ {t | μ t ≤ 0}ᶜ := by simpa using h
      simp [Set.indicator_of_notMem this]
    · push_neg at h
      simp [Real.toNNReal_of_nonpos (by linarith : -μ t ≤ 0)]

noncomputable def jd (μ : Ω0 →₀ ℝ) : JordanDecomposition Ω0 where
  posPart := Pm μ
  negPart := Nm μ
  mutuallySingular := ms_PN μ

lemma toJD (μ : Ω0 →₀ ℝ) : (toM μ).toJordanDecomposition = jd μ :=
  SignedMeasure.toJordanDecomposition_eq (toM_eq μ)

lemma int_dirac_combo (μ : Ω0 →₀ ℝ) (c : Ω0 → NNReal) (f : Ω0 → ℝ) :
    ∫ x, f x ∂(∑ t ∈ μ.support, c t • Measure.dirac t) = ∑ t ∈ μ.support, (c t : ℝ) * f t := by
  rw [integral_finsetSum_measure (fun t _ => (integrable_dirac (by simp)).smul_measure_nnreal)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_smul_nnreal_measure, integral_dirac]
  rfl

lemma pair_toM (μ : Ω0 →₀ ℝ) (f : Ω0 → ℝ) : pair (toM μ) f = ip f μ := by
  unfold pair
  rw [toJD]
  change ∫ x, f x ∂(Pm μ) - ∫ x, f x ∂(Nm μ) = _
  rw [Pm, Nm, int_dirac_combo, int_dirac_combo, ip_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Real.coe_toNNReal', Real.coe_toNNReal', ← sub_mul, max_zero_sub_max_neg_zero_eq_self]



def bdd : Submodule ℝ (Ωb → ℝ) where
  carrier := {f | ∃ C, ∀ t, |f t| ≤ C}
  add_mem' := by
    rintro f g ⟨C1, h1⟩ ⟨C2, h2⟩
    exact ⟨C1 + C2, fun t => (abs_add_le _ _).trans (add_le_add (h1 t) (h2 t))⟩
  zero_mem' := ⟨0, fun t => by simp⟩
  smul_mem' := by
    rintro c f ⟨C, h⟩
    exact ⟨|c| * C, fun t => by
      rw [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (h t) (abs_nonneg c)⟩

noncomputable def B : bdd →ₗ[ℝ] (Ωb →₀ ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X μ => ip X μ)
    (fun X Y μ => by
      simp only [ip_eq, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c X μ => by
      simp only [ip_eq, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => by ring)
    (fun X μ ν => ip_add_right _ μ ν)
    (fun c X μ => by
      unfold ip
      rw [Finsupp.sum_smul_index (fun _ => zero_mul _), smul_eq_mul, Finsupp.mul_sum]
      refine Finset.sum_congr rfl fun t _ => by ring)

noncomputable def B2 : ULift.{v} bdd →ₗ[ℝ] ULift.{w} (Ωb →₀ ℝ) →ₗ[ℝ] ℝ :=
  (B.compl₂ (ULift.moduleEquiv : ULift.{w} (Ωb →₀ ℝ) ≃ₗ[ℝ] _).toLinearMap).comp
    (ULift.moduleEquiv : ULift.{v} bdd ≃ₗ[ℝ] _).toLinearMap

abbrev XX := WeakBilin B2.{v, w}
abbrev YY := WeakBilin B2.{v, w}.flip

lemma B2_apply (X : XX.{v, w}) (μ : YY.{v, w}) :
    B2 X μ = ∑ s ∈ μ.down.support, μ.down s * X.down.1 s := rfl

noncomputable def oneB : bdd := ⟨fun _ => 1, ⟨1, fun t => by simp⟩⟩

noncomputable def toFunX : XX.{v, w} →ₗ[ℝ] (Ω0.{u} → ℝ) :=
  (LinearMap.funLeft ℝ ℝ dn.{u}) ∘ₗ bdd.subtype ∘ₗ
    (ULift.moduleEquiv : ULift.{v} bdd ≃ₗ[ℝ] _).toLinearMap

noncomputable def toMY : YY.{v, w} →ₗ[ℝ] SignedMeasure Ω0.{u} :=
  toM ∘ₗ Finsupp.lmapDomain ℝ ℝ up.{u} ∘ₗ
    (ULift.moduleEquiv : ULift.{w} (Ωb →₀ ℝ) ≃ₗ[ℝ] _).toLinearMap

lemma toFunX_apply (X : XX.{v, w}) (t : Ω0.{u}) : toFunX X t = X.down.1 (dn t) := rfl

lemma ip_mapDomain (f : Ω0.{u} → ℝ) (μ : Ωb →₀ ℝ) :
    ip f (Finsupp.mapDomain up μ) = ip (fun s => f (up s)) μ := by
  unfold ip
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma pair_toMY (μ : YY.{v, w}) (X : XX.{v, w}) : pair (toMY.{u} μ) (toFunX X) = B2 X μ := by
  show pair (toM (Finsupp.mapDomain up μ.down)) (toFunX X) = _
  rw [pair_toM, ip_mapDomain]; rfl

lemma toMY_apply (μ : YY.{v, w}) (A : Set Ω0.{u}) :
    toMY μ A = ip (fun s => A.indicator 1 (up s)) μ.down := by
  show toM (Finsupp.mapDomain up μ.down) A = _
  rw [toM_apply, ip_mapDomain]

lemma ip_singleton (t : Ωb) (κ : Ωb →₀ ℝ) :
    ip (fun s => ({up.{u} t} : Set Ω0).indicator 1 (up s)) κ = κ t := by
  induction κ using Finsupp.induction_linear with
  | zero => simp [ip]
  | add f g hf hg => rw [ip_add_right, hf, hg]; rfl
  | single s a =>
    rw [ip_single]
    by_cases hs : s = t
    · subst hs; rw [Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, mul_one]
      simp
    · have : up.{u} s ≠ up t := fun h => hs (congrArg dn h)
      rw [Set.indicator_of_notMem (fun h => this (Set.mem_singleton_iff.mp h)), mul_zero]
      simp [hs]

noncomputable def S : PairedSpaces Ω0.{u} XX.{v, w} YY.{v, w} where
  toFun := toFunX
  toFun_injective := fun a b h => ULift.ext _ _ (Subtype.ext (funext fun s =>
    congrFun h (up s)))
  measurable := fun _ => measurable_from_top
  toMeasure := toMY
  toMeasure_injective := by
    intro μ ν h
    apply ULift.ext
    apply Finsupp.ext
    intro t
    have := congrArg (fun m : SignedMeasure Ω0 => m {up t}) h
    simp only [toMY_apply] at this
    exact (ip_singleton t μ.down).symm.trans (this.trans (ip_singleton t ν.down))
  integrable := by
    intro μ X
    obtain ⟨C, hC⟩ := X.down.2
    exact Integrable.of_bound measurable_from_top.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hC (dn t))
  continuous_pair_X := fun μ =>
    (WeakBilin.eval_continuous B2 μ).congr fun X => (pair_toMY μ X).symm
  dual_rep_X := by
    intro ℓ
    obtain ⟨y, hy⟩ := LinearMap.dualEmbedding_surjective B2 ℓ
    exact ⟨y, fun X => by rw [← hy]; exact (pair_toMY y X).symm⟩
  continuous_pair_Y := fun X =>
    (WeakBilin.eval_continuous B2.flip X).congr fun μ => (pair_toMY μ X).symm
  dual_rep_Y := by
    intro ℓ
    obtain ⟨y, hy⟩ := LinearMap.dualEmbedding_surjective B2.flip ℓ
    exact ⟨y, fun μ => by rw [← hy]; exact (pair_toMY μ y).symm⟩
  F₁ := ⊥
  F₁_le := bot_le
  X₁ := Submodule.span ℝ {(ULift.up oneB : XX.{v, w})}
  X₁_measurable := by
    intro Y hY
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hY
    have : toFunX.{u} Y = fun _ => c := by
      rw [← hc]; funext t; exact mul_one c
    rw [this]; exact measurable_const

lemma bddX (X : XX.{v, w}) : BddAbove (Set.range fun s => X.down.1 s) := by
  obtain ⟨C, hC⟩ := X.down.2
  exact ⟨C, by rintro _ ⟨t, rfl⟩; exact (le_abs_self _).trans (hC t)⟩

noncomputable def supX (X : XX.{v, w}) : ℝ := ⨆ s, X.down.1 s

noncomputable def oneX : XX.{v, w} := ULift.up oneB

noncomputable def ρ0 (X : XX.{v, w}) : XX.{v, w} := supX X • oneX

lemma down_add_smul (a b : ℝ) (X Y : XX.{v, w}) (s : Ωb) :
    (a • X + b • Y).down.1 s = a * X.down.1 s + b * Y.down.1 s := rfl

lemma down_smul_one (a : ℝ) (s : Ωb) : (a • oneX.{v, w}).down.1 s = a := mul_one a

lemma ρω_eq (ω : Ω0.{u}) (X : XX.{v, w}) : ρω S ρ0 ω X = supX X := down_smul_one _ _

lemma mem_X₁_iff (Y : XX.{v, w}) : Y ∈ S.{u}.X₁ ↔ ∃ c : ℝ, c • oneX = Y :=
  Submodule.mem_span_singleton

lemma hCond : CondC S.{u, v, w} := by
  intro μ hμ
  by_contra hcon
  push_neg at hcon
  apply hμ
  rw [VectorMeasure.le_iff]
  intro A hA
  rw [zero_apply]
  show 0 ≤ toMY μ A
  rw [toMY_apply, ip_eq]
  refine Finset.sum_nonneg fun t _ => mul_nonneg ?_ ?_
  · let Xt : XX.{v, w} := ULift.up ⟨({t} : Set Ωb).indicator 1, ⟨1, fun s => by
      by_cases h : s = t <;> simp [h]⟩⟩
    have h1 := hcon Xt (fun s => by
      show 0 ≤ ({t} : Set Ωb).indicator 1 (dn s)
      by_cases h : dn s = t <;> simp [h])
    change 0 ≤ pair (toMY μ) (toFunX Xt) at h1
    rw [pair_toMY, B2_apply] at h1
    have h2 : ∑ s ∈ μ.down.support, μ.down s * Xt.down.1 s = μ.down t := by
      rw [Finset.sum_eq_single t]
      · show μ.down t * ({t} : Set Ωb).indicator 1 t = _
        simp
      · intro b _ hb
        show μ.down b * ({t} : Set Ωb).indicator 1 b = 0
        simp [hb]
      · intro ht; rw [Finsupp.notMem_support_iff.mp ht, zero_mul]
    rw [h2] at h1
    exact h1
  · show 0 ≤ A.indicator 1 (up t)
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma hCond' : CondC' S.{u, v, w} := by
  intro B hB
  rcases MeasurableSpace.measurableSet_bot_iff.mp hB with rfl | rfl
  · exact ⟨0, (S.{u, v, w}).X₁.zero_mem, by rw [map_zero]; funext t; simp⟩
  · refine ⟨oneX, Submodule.mem_span_singleton_self _, ?_⟩
    funext t; change (oneX : XX.{v, w}).down.1 (dn t) = _; simp [oneX, oneB]

lemma hRisk : IsCondRiskMapping S.{u, v, w} ρ0 := by
  refine ⟨fun X => Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_, ?_, ?_⟩
  · intro a ha0 ha1 X Y ω
    simp only [ρω_eq]
    unfold supX
    refine ciSup_le fun t => ?_
    rw [down_add_smul]
    have h1 := le_ciSup (bddX X) t
    have h2 := le_ciSup (bddX Y) t
    have : 0 ≤ 1 - a := by linarith
    nlinarith
  · intro X Y hXY ω
    simp only [ρω_eq]
    exact ciSup_mono (bddX Y) fun s => hXY (up s)
  · intro Y hY X
    obtain ⟨c, rfl⟩ := (mem_X₁_iff.{u} Y).mp hY
    unfold ρ0
    have : supX (X + c • oneX) = supX X + c := by
      unfold supX
      have : ∀ s, (X + c • oneX.{v, w}).down.1 s = X.down.1 s + c := fun s => by
        show X.down.1 s + c * 1 = _; rw [mul_one]
      simp only [this]
      exact (ciSup_add (bddX X) c).symm
    rw [this, add_smul]

lemma hPH : PosHomogeneous ρ0.{v, w} := by
  intro a X ha
  unfold ρ0
  have : supX (a • X) = a * supX X := by
    unfold supX
    rw [Real.mul_iSup_of_nonneg ha.le]
    rfl
  rw [this, smul_smul]

lemma hLsc : IsLsc S.{u, v, w} ρ0 := by
  intro ω
  have : ρω S ρ0 ω = fun X => ⨆ s, X.down.1 s := by funext X; exact ρω_eq ω X
  rw [this]
  refine lowerSemicontinuous_ciSup bddX fun s => ?_
  have hc : Continuous fun X : XX.{v, w} => X.down.1 s := by
    refine (WeakBilin.eval_continuous B2 (ULift.up (Finsupp.single s 1))).congr fun X => ?_
    show ip _ (Finsupp.single s 1) = _
    rw [ip_single, one_mul]; rfl
  exact hc.lowerSemicontinuous


/-! ### Separability of `𝒳` -/

def restr (N : ℕ) (t : Ωb) : Fin N → Bool := fun i => t i

noncomputable def mkN (N : ℕ) (g : (Fin N → Bool) → ℝ) : XX.{v, w} :=
  ULift.up ⟨fun t => g (restr N t), ⟨∑ s, |g s|, fun t =>
    Finset.single_le_sum (f := fun s => |g s|) (fun s _ => abs_nonneg _) (Finset.mem_univ _)⟩⟩

lemma cont_mkN (N : ℕ) : Continuous (mkN.{v, w} N) := by
  refine WeakBilin.continuous_of_continuous_eval B2 fun y => ?_
  show Continuous fun g : (Fin N → Bool) → ℝ =>
    ∑ t ∈ y.down.support, y.down t * g (restr N t)
  exact continuous_finset_sum _ fun t _ => continuous_const.mul (continuous_apply _)

lemma separate (F : Finset Ωb) :
    ∃ N, ∀ t ∈ F, ∀ t' ∈ F, restr N t = restr N t' → t = t' := by
  classical
  have hex : ∀ p : Ωb × Ωb, p.1 ≠ p.2 → ∃ n, p.1 n ≠ p.2 n := fun p hp =>
    Function.ne_iff.mp hp
  let n : Ωb × Ωb → ℕ := fun p => if h : p.1 ≠ p.2 then Classical.choose (hex p h) else 0
  refine ⟨(F ×ˢ F).sup fun p => n p + 1, fun t ht t' ht' heq => ?_⟩
  by_contra hne
  have hn : t (n (t, t')) ≠ t' (n (t, t')) := by
    simp only [n, dif_pos hne]; exact Classical.choose_spec (hex (t, t') hne)
  have hlt : n (t, t') < (F ×ˢ F).sup fun p => n p + 1 :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Finset.le_sup (f := fun p => n p + 1) (Finset.mem_product.mpr ⟨ht, ht'⟩))
  exact hn (congrFun heq ⟨_, hlt⟩)

lemma interpolate (X : XX.{v, w}) (F : Finset Ωb) :
    ∃ N g, ∀ t ∈ F, (mkN.{v, w} N g).down.1 t = X.down.1 t := by
  classical
  obtain ⟨N, hN⟩ := separate F
  refine ⟨N, fun s => if h : ∃ t ∈ F, restr N t = s then X.down.1 (Classical.choose h) else 0,
    fun t ht => ?_⟩
  have h : ∃ t' ∈ F, restr N t' = restr N t := ⟨t, ht, rfl⟩
  show (if h : ∃ t' ∈ F, restr N t' = restr N t then X.down.1 (Classical.choose h) else 0) = _
  rw [dif_pos h]
  have := Classical.choose_spec h
  rw [hN _ this.1 t ht this.2]

lemma dense_mk (X : XX.{v, w}) : X ∈ closure (⋃ N, Set.range (mkN.{v, w} N)) := by
  classical
  rw [mem_closure_iff_nhds]
  intro U hU
  have hU' : U ∈ Filter.comap (fun x : XX.{v, w} => fun y => B2 x y)
      (nhds (fun y => B2 X y)) := by
    rw [← nhds_induced]; exact hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU'
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hIV⟩ := hV
  obtain ⟨N, g, hg⟩ := interpolate X (I.biUnion fun y => y.down.support)
  refine ⟨mkN N g, hVU (hIV fun y hy => ?_), Set.mem_iUnion.mpr ⟨N, g, rfl⟩⟩
  have : B2 (mkN.{v, w} N g) y = B2 X y := by
    show ∑ s ∈ y.down.support, y.down s * (mkN N g).down.1 s =
      ∑ s ∈ y.down.support, y.down s * X.down.1 s
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [hg s (Finset.mem_biUnion.mpr ⟨y, Finset.mem_coe.mp hy, hs⟩)]
  show B2 (mkN.{v, w} N g) y ∈ t y
  rw [this]
  exact mem_of_mem_nhds (ht y)

instance : TopologicalSpace.SeparableSpace XX.{v, w} := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  exact ((TopologicalSpace.IsSeparable.iUnion fun N =>
    TopologicalSpace.isSeparable_range (cont_mkN N)).closure).mono fun X _ => dense_mk X

/-! ### A point outside a countable set -/

lemma exists_not_mem (C : Set Ωb) (hC : C.Countable) : ∃ t, t ∉ C := by
  obtain ⟨e, he⟩ := (hC.union (Set.countable_singleton (fun _ => false))).exists_eq_range
    ⟨_, Or.inr rfl⟩
  refine ⟨fun n => !(e n n), fun hmem => ?_⟩
  have : (fun n => !(e n n)) ∈ Set.range e := he ▸ Or.inl hmem
  obtain ⟨n, hn⟩ := this
  have := congrFun hn n
  cases h : e n n <;> simp [h] at this

end CRMLemma1Counter

open CRMLemma1Counter in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] {𝒳 𝒴 : Type}
    [AddCommGroup 𝒳] [Module ℝ 𝒳] [TopologicalSpace 𝒳]
    [IsTopologicalAddGroup 𝒳] [ContinuousSMul ℝ 𝒳] [LocallyConvexSpace ℝ 𝒳]
    [AddCommGroup 𝒴] [Module ℝ 𝒴] [TopologicalSpace 𝒴]
    [IsTopologicalAddGroup 𝒴] [ContinuousSMul ℝ 𝒴] [LocallyConvexSpace ℝ 𝒴]
    [TopologicalSpace.SeparableSpace 𝒳]
    (S : PairedSpaces Ω 𝒳 𝒴) (hC : CondC S) (hC' : CondC' S)
    (ρ : 𝒳 → 𝒳) (hρ : IsCondRiskMapping S ρ) (hph : PosHomogeneous ρ) (hlsc : IsLsc S ρ),
    ∃ κ : ℕ → Ω → 𝒴, (∀ i, IsSelection S ρ (κ i)) ∧
      ∀ X ω, IsLUB (Set.range fun i => pair (S.toMeasure (κ i ω)) (S.toFun X)) (ρω S ρ ω X)) := by
  intro h
  obtain ⟨κ, -, hlub⟩ := h S hCond hCond' ρ0 hRisk hPH hLsc
  let ω0 := up (fun _ => false)
  let C : Set Ωb := ⋃ i, ((κ i ω0).down.support : Set Ωb)
  have hCc : C.Countable := Set.countable_iUnion fun i => Finset.countable_toSet _
  obtain ⟨t0, ht0⟩ := exists_not_mem C hCc
  let X0 : XX := ULift.up ⟨Cᶜ.indicator 1, ⟨1, fun s => by
    by_cases hs : s ∈ C <;> simp [hs]⟩⟩
  have h1 := hlub X0 ω0
  rw [ρω_eq] at h1
  have hsup : supX X0 = 1 := by
    apply le_antisymm
    · refine ciSup_le fun s => ?_
      show Cᶜ.indicator 1 s ≤ 1
      by_cases hs : s ∈ C <;> simp [hs]
    · refine le_ciSup_of_le (bddX X0) t0 ?_
      show 1 ≤ Cᶜ.indicator 1 t0
      simp [ht0]
  have hzero : ∀ i, pair (S.toMeasure (κ i ω0)) (S.toFun X0) = 0 := by
    intro i
    change pair (toMY (κ i ω0)) (toFunX X0) = 0
    rw [pair_toMY, B2_apply]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hsC : s ∈ C := Set.mem_iUnion.mpr ⟨i, hs⟩
    show (κ i ω0).down s * Cᶜ.indicator 1 s = 0
    simp [hsC]
  have hub : (0 : ℝ) ∈ upperBounds
      (Set.range fun i => pair (S.toMeasure (κ i ω0)) (S.toFun X0)) := by
    rintro _ ⟨i, rfl⟩; exact (hzero i).le
  have := h1.2 hub
  rw [hsup] at this
  exact absurd this (by norm_num)
