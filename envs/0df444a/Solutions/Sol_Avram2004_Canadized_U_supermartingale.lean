-- Prove2me | solution 1 for Avram2004.Canadized.U_supermartingale
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T09:39:03.310065+00:00
-- url     : https://prove2.me/submissions/eb78b23f-773a-461a-abda-22b152643de9

import Mathlib
import Definitions.Def_Avram2004_Shared_IsSNLevy
import Definitions.Def_Avram2004_Shared_Standing
import Definitions.Def_Avram2004_Shared_scaleFun
import Definitions.Def_Avram2004_Shared_tiltedScale
import Definitions.Def_Avram2004_Shared_reflected
import Definitions.Def_Avram2004_Shared_esscher
import Definitions.Def_Avram2004_Canadized_canadizedProblem

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Avram2004.Markov92562e40

/-- Chain rule for independence: if `A ⫫ G` and `B ⫫ H` with `A, G ≤ H`, then `A ⊔ B ⫫ G`. -/
lemma indep_sup_chain {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {mA mB G H : MeasurableSpace Ω} (hAm : mA ≤ m) (hBm : mB ≤ m) (hGm : G ≤ m)
    (hA : Indep mA G μ) (hB : Indep mB H μ) (hAH : mA ≤ H) (hGH : G ≤ H) :
    Indep (mA ⊔ mB) G μ := by
  let p : Set (Set Ω) := {s | ∃ a b, MeasurableSet[mA] a ∧ MeasurableSet[mB] b ∧ s = a ∩ b}
  have hp : IsPiSystem p := by
    rintro _ ⟨a1, b1, ha1, hb1, rfl⟩ _ ⟨a2, b2, ha2, hb2, rfl⟩ _
    exact ⟨a1 ∩ a2, b1 ∩ b2, ha1.inter ha2, hb1.inter hb2, by ext; simp only [Set.mem_inter_iff]; tauto⟩
  have hgen : mA ⊔ mB = MeasurableSpace.generateFrom p := by
    apply le_antisymm
    · refine sup_le (fun a ha => MeasurableSpace.measurableSet_generateFrom
        ⟨a, Set.univ, ha, MeasurableSet.univ, by simp⟩) (fun b hb =>
        MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, b, MeasurableSet.univ, hb, by simp⟩)
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨a, b, ha, hb, rfl⟩
      exact MeasurableSet.inter ((le_sup_left : mA ≤ mA ⊔ mB) a ha)
        ((le_sup_right : mB ≤ mA ⊔ mB) b hb)
  have hAi := (Indep_iff _ _ _).1 hA
  have hBi := (Indep_iff _ _ _).1 hB
  refine IndepSets.indep (sup_le hAm hBm) hGm hp (@MeasurableSpace.isPiSystem_measurableSet Ω G)
    hgen (@MeasurableSpace.generateFrom_measurableSet Ω G).symm ?_
  rw [IndepSets_iff]
  rintro _ g ⟨a, b, ha, hb, rfl⟩ hg
  have hag : MeasurableSet[H] (a ∩ g) := (hAH a ha).inter (hGH g hg)
  have h1 := hBi b (a ∩ g) hb hag
  have h2 := hAi a g ha hg
  have h3 := hBi b a hb (hAH a ha)
  calc μ (a ∩ b ∩ g) = μ (b ∩ (a ∩ g)) := by
        congr 1; ext; simp only [Set.mem_inter_iff]; tauto
    _ = μ b * (μ a * μ g) := by rw [h1, h2]
    _ = μ (a ∩ b) * μ g := by
        rw [show a ∩ b = b ∩ a from Set.inter_comm a b, h3]; ring

/-- The σ-algebra of the increments `X (s+u) - X s`, `u ∈ F`. -/
def incAlg {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (F : Finset ℝ≥0) : MeasurableSpace Ω :=
  ⨆ u ∈ F, MeasurableSpace.comap (fun ω => X (s + u) ω - X s ω) (inferInstance : MeasurableSpace ℝ)

lemma incAlg_mono {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : Monotone (incAlg X s) := by
  intro F G hFG
  exact biSup_mono (fun u hu => hFG hu)

lemma incAlg_le {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (X : ℝ≥0 → Ω → ℝ)
    (hX : Adapted 𝓕 X) (s b : ℝ≥0) (F : Finset ℝ≥0) (hF : ∀ u ∈ F, u ≤ b) :
    incAlg X s F ≤ 𝓕 (s + b) := by
  refine iSup₂_le fun u hu => ?_
  have hmeas : Measurable[𝓕 (s + b)] (fun ω => X (s + u) ω - X s ω) := by
    have h1 : Measurable[𝓕 (s + b)] (X (s + u)) :=
      (hX (s + u)).mono (𝓕.mono (add_le_add le_rfl (hF u hu))) le_rfl
    have h2 : Measurable[𝓕 (s + b)] (X s) :=
      (hX s).mono (𝓕.mono (le_add_of_nonneg_right (zero_le (a := b)))) le_rfl
    exact h1.sub h2
  exact hmeas.comap_le

lemma incAlg_le_ambient {Ω : Type*} {m : MeasurableSpace Ω} (X : ℝ≥0 → Ω → ℝ)
    (hXm : ∀ t, Measurable (X t)) (s : ℝ≥0) (F : Finset ℝ≥0) : incAlg X s F ≤ m := by
  refine iSup₂_le fun u _ => ?_
  exact ((hXm (s + u)).sub (hXm s)).comap_le

/-- Markov property at a deterministic time, finite-dimensional form: the increments
`X (s+u) - X s`, `u ∈ F`, are jointly independent of `𝓕 s`. -/
lemma indep_incAlg_past {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (s : ℝ≥0) (F : Finset ℝ≥0) : Indep (incAlg X s F) (𝓕 s) P := by
  have hXm := hX.isSNLevy.measurable
  induction F using Finset.induction_on_max with
  | empty =>
    have : incAlg X s ∅ = ⊥ := by simp [incAlg]
    rw [this]; exact indep_bot_left _
  | insert a F hlt ih =>
    rcases F.eq_empty_or_nonempty with hF | hF
    · subst hF
      have : incAlg X s (insert a ∅) = MeasurableSpace.comap (fun ω => X (s + a) ω - X s ω)
          (inferInstance : MeasurableSpace ℝ) := by simp [incAlg]
      rw [this]; exact hX.indep_past s a
    · set b := F.max' hF with hbdef
      have hbF : b ∈ F := F.max'_mem hF
      have hba : b ≤ a := (hlt b hbF).le
      have hFb : ∀ u ∈ F, u ≤ b := fun u hu => F.le_max' u hu
      -- the new increment of the step `b → a`
      let D : Ω → ℝ := fun ω => X ((s + b) + (a - b)) ω - X (s + b) ω
      have hD := hX.indep_past (s + b) (a - b)
      have hsab : s + b + (a - b) = s + a := by
        rw [add_assoc, add_tsub_cancel_of_le hba]
      have hchain : Indep (incAlg X s F ⊔ MeasurableSpace.comap D (inferInstance : MeasurableSpace ℝ))
          (𝓕 s) P :=
        indep_sup_chain (incAlg_le_ambient X hXm s F)
          (((hXm _).sub (hXm _)).comap_le) (𝓕.le s) ih hD
          (incAlg_le 𝓕 X hX.adapted s b F hFb)
          (𝓕.mono (le_add_of_nonneg_right (zero_le (a := b))))
      refine indep_of_indep_of_le_left hchain ?_
      -- `incAlg (insert a F) ≤ incAlg F ⊔ σ(D)`
      refine iSup₂_le fun u hu => ?_
      rcases Finset.mem_insert.1 hu with rfl | hu
      · -- `X(s+u) - X s = D + (X(s+b) - X s)`
        have hbm : Measurable[incAlg X s F ⊔ MeasurableSpace.comap D (inferInstance : MeasurableSpace ℝ)]
            (fun ω => X (s + b) ω - X s ω) := by
          have : Measurable[incAlg X s F] (fun ω => X (s + b) ω - X s ω) := by
            rw [measurable_iff_comap_le]
            exact le_iSup₂ (f := fun u (_ : u ∈ F) => MeasurableSpace.comap
              (fun ω => X (s + u) ω - X s ω) (inferInstance : MeasurableSpace ℝ)) b hbF
          exact this.mono le_sup_left le_rfl
        have hDm : Measurable[incAlg X s F ⊔ MeasurableSpace.comap D (inferInstance : MeasurableSpace ℝ)]
            D := (comap_measurable D).mono le_sup_right le_rfl
        have heq : (fun ω => X (s + u) ω - X s ω) = fun ω => D ω + (X (s + b) ω - X s ω) := by
          funext ω; simp only [D, hsab]; ring
        rw [← measurable_iff_comap_le, heq]
        exact hDm.add hbm
      · exact le_sup_of_le_left (le_iSup₂ (f := fun u (_ : u ∈ F) => MeasurableSpace.comap
          (fun ω => X (s + u) ω - X s ω) (inferInstance : MeasurableSpace ℝ)) u hu)

/-- Markov property at a deterministic time: the whole post-`s` increment process is
independent of `𝓕 s`. -/
theorem indep_postIncrements_past {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (s : ℝ≥0) :
    Indep (⨆ u, MeasurableSpace.comap (fun ω => X (s + u) ω - X s ω)
      (inferInstance : MeasurableSpace ℝ)) (𝓕 s) P := by
  have h : (⨆ u, MeasurableSpace.comap (fun ω => X (s + u) ω - X s ω)
      (inferInstance : MeasurableSpace ℝ)) = ⨆ F : Finset ℝ≥0, incAlg X s F := by
    rw [iSup_eq_iSup_finset]; rfl
  rw [h]
  exact indep_iSup_of_directed_le (fun F => indep_incAlg_past 𝓕 P X hX s F)
    (fun F => incAlg_le_ambient X hX.isSNLevy.measurable s F) (𝓕.le s)
    (incAlg_mono X s).directed_le

/-! ## Law half of the simple Markov property -/

/-- Consecutive increments along `s + t` have the joint law of consecutive increments along `t`. -/
lemma identDistrib_incVec {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevy P X) (s : ℝ≥0) (n : ℕ) (t : Fin (n + 1) → ℝ≥0)
    (ht : Monotone t) :
    IdentDistrib (fun ω (i : Fin n) => X (s + t i.succ) ω - X (s + t i.castSucc) ω)
      (fun ω (i : Fin n) => X (t i.succ) ω - X (t i.castSucc) ω) P P := by
  have hst : Monotone (fun i => s + t i) := fun i j hij => add_le_add le_rfl (ht hij)
  refine IdentDistrib.pi (X := fun (i : Fin n) ω => X (s + t i.succ) ω - X (s + t i.castSucc) ω)
    (Y := fun (i : Fin n) ω => X (t i.succ) ω - X (t i.castSucc) ω) (fun i => ?_)
    (hX.indep_increments n (fun i => s + t i) hst) (hX.indep_increments n t ht)
  have hle : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have h1 := hX.stationary_increments (s + t i.castSucc) (t i.succ - t i.castSucc)
  have h2 := hX.stationary_increments (t i.castSucc) (t i.succ - t i.castSucc)
  rw [add_assoc, add_tsub_cancel_of_le hle] at h1
  rw [add_tsub_cancel_of_le hle] at h2
  exact h1.trans h2.symm

/-- Telescoping over `Fin`: values relative to time `t 0` are partial sums of the increments. -/
lemma telescope_fin (n : ℕ) (f : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    f i - f 0 = ∑ k ∈ Finset.range i.val,
      (if h : k < n then f (Fin.succ ⟨k, h⟩) - f (Fin.castSucc ⟨k, h⟩) else 0) := by
  let g : ℕ → ℝ := fun k => if h : k < n + 1 then f ⟨k, h⟩ else 0
  have hsum : ∑ k ∈ Finset.range i.val,
      (if h : k < n then f (Fin.succ ⟨k, h⟩) - f (Fin.castSucc ⟨k, h⟩) else 0)
      = ∑ k ∈ Finset.range i.val, (g (k + 1) - g k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < n := by
      have := Finset.mem_range.1 hk; have := i.isLt; omega
    simp only [g, dif_pos hk', dif_pos (show k + 1 < n + 1 by omega),
      dif_pos (show k < n + 1 by omega)]
    try rfl
  rw [hsum, Finset.sum_range_sub]
  simp only [g, dif_pos i.isLt, dif_pos (show 0 < n + 1 by omega)]
  try rfl

/-- The partial-sum map is measurable. -/
lemma measurable_partialSum (n : ℕ) :
    Measurable (fun (v : Fin n → ℝ) (i : Fin (n + 1)) =>
      ∑ k ∈ Finset.range i.val, (if h : k < n then v ⟨k, h⟩ else 0)) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Finset.measurable_sum _ fun k _ => ?_
  by_cases h : k < n
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

/-- Finite-dimensional law of the post-`s` process relative to time `t 0`. -/
lemma identDistrib_fdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevy P X) (s : ℝ≥0) (n : ℕ) (t : Fin (n + 1) → ℝ≥0)
    (ht : Monotone t) :
    IdentDistrib (fun ω (i : Fin (n + 1)) => X (s + t i) ω - X (s + t 0) ω)
      (fun ω (i : Fin (n + 1)) => X (t i) ω - X (t 0) ω) P P := by
  have h := (identDistrib_incVec P X hX s n t ht).comp (measurable_partialSum n)
  have e1 : (fun ω (i : Fin (n + 1)) => X (s + t i) ω - X (s + t 0) ω) =
      (fun (v : Fin n → ℝ) (i : Fin (n + 1)) =>
        ∑ k ∈ Finset.range i.val, (if h : k < n then v ⟨k, h⟩ else 0)) ∘
      (fun ω (i : Fin n) => X (s + t i.succ) ω - X (s + t i.castSucc) ω) := by
    funext ω i
    simp only [Function.comp]
    rw [telescope_fin n (fun j => X (s + t j) ω) i]
  have e2 : (fun ω (i : Fin (n + 1)) => X (t i) ω - X (t 0) ω) =
      (fun (v : Fin n → ℝ) (i : Fin (n + 1)) =>
        ∑ k ∈ Finset.range i.val, (if h : k < n then v ⟨k, h⟩ else 0)) ∘
      (fun ω (i : Fin n) => X (t i.succ) ω - X (t i.castSucc) ω) := by
    funext ω i
    simp only [Function.comp]
    rw [telescope_fin n (fun j => X (t j) ω) i]
  rw [e1, e2]; exact h

/-- Simple Markov property, law half: the post-`s` increment process has the law of `X`. -/
theorem identDistrib_postIncrements {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevy P X) (s : ℝ≥0) :
    IdentDistrib (fun ω (u : ℝ≥0) => X (s + u) ω - X s ω) (fun ω (u : ℝ≥0) => X u ω) P P := by
  have hXm := hX.measurable
  refine (identDistrib_iff_forall_finset_identDistrib
    (X := fun u ω => X (s + u) ω - X s ω) (Y := X)
    (measurable_pi_lambda _ fun u => (hXm _).sub (hXm _)).aemeasurable
    (measurable_pi_lambda _ fun u => hXm u).aemeasurable).2 fun I => ?_
  set k := I.card
  let e := I.orderIsoOfFin (rfl : I.card = k)
  let t : Fin (k + 1) → ℝ≥0 := Fin.cons 0 (fun j => ((e j : I) : ℝ≥0))
  have ht : Monotone t := by
    intro i j hij
    induction i using Fin.cases with
    | zero => simp only [t, Fin.cons_zero]; exact zero_le (a := t j)
    | succ i' =>
      induction j using Fin.cases with
      | zero => exact absurd hij (not_le.2 (Fin.succ_pos i'))
      | succ j' =>
        simp only [t, Fin.cons_succ]
        exact Subtype.coe_le_coe.2 (e.monotone (Fin.succ_le_succ_iff.1 hij))
  have h := (identDistrib_fdd P X hX s k t ht).comp
    (u := fun (w : Fin (k + 1) → ℝ) (u : I) => w (e.symm u).succ)
    (measurable_pi_lambda _ fun u => measurable_pi_apply _)
  have ht0 : t 0 = 0 := rfl
  have hte : ∀ u : I, t (e.symm u).succ = (u : ℝ≥0) := by
    intro u; simp only [t, Fin.cons_succ, OrderIso.apply_symm_apply]
  convert h using 1
  · funext ω u; simp only [Function.comp, Finset.restrict, hte, ht0, add_zero]
  · funext ω u; simp only [Function.comp, Finset.restrict, hte, ht0, hX.start_zero, sub_zero]

/-! ## Strong Markov property for countably-valued stopping times -/

/-- The path of increments after a deterministic time `d`. -/
def postPath {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (d : ℝ≥0) (ω : Ω) : ℝ≥0 → ℝ :=
  fun u => X (d + u) ω - X d ω

lemma measurable_postPath {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℝ)
    (hXm : ∀ t, Measurable (X t)) (d : ℝ≥0) : Measurable (postPath X d) :=
  measurable_pi_lambda _ fun u => (hXm _).sub (hXm _)

lemma measurable_postPath_post {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (d : ℝ≥0) :
    Measurable[⨆ u, MeasurableSpace.comap (fun ω => X (d + u) ω - X d ω)
      (inferInstance : MeasurableSpace ℝ)] (postPath X d) := by
  letI : MeasurableSpace Ω := ⨆ u, MeasurableSpace.comap (fun ω => X (d + u) ω - X d ω)
    (inferInstance : MeasurableSpace ℝ)
  refine measurable_pi_lambda _ fun u => ?_
  rw [measurable_iff_comap_le]
  exact le_iSup (fun u => MeasurableSpace.comap (fun ω => X (d + u) ω - X d ω)
    (inferInstance : MeasurableSpace ℝ)) u

/-- `{τ = d}` cut down to an `𝓕_τ` event is `𝓕 d`-measurable when `τ` has countably many values. -/
lemma measurableSet_inter_eq {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (τ : Ω → ℝ≥0) (hτc : (Set.range τ).Countable) (A : Set Ω)
    (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t})) (d : ℝ≥0) :
    MeasurableSet[𝓕 d] (A ∩ {ω | τ ω = d}) := by
  have heq : A ∩ {ω | τ ω = d} = (A ∩ {ω | τ ω ≤ d}) \
      ⋃ d' ∈ {d' ∈ Set.range τ | d' < d}, (A ∩ {ω | τ ω ≤ d'}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_iUnion, exists_prop,
      Set.mem_range, not_exists, not_and]
    constructor
    · rintro ⟨hA, rfl⟩
      refine ⟨⟨hA, le_rfl⟩, fun x hx _ hle => absurd hle (not_le.2 hx.2)⟩
    · rintro ⟨⟨hA, hle⟩, hno⟩
      refine ⟨hA, le_antisymm hle (not_lt.1 fun hlt => hno (τ ω) ⟨⟨ω, rfl⟩, hlt⟩ hA le_rfl)⟩
  rw [heq]
  refine (hA d).diff (MeasurableSet.biUnion (hτc.mono fun x hx => hx.1) fun d' hd' => ?_)
  exact 𝓕.mono hd'.2.le _ (hA d')

/-- Strong Markov property at a countably-valued stopping time: for every `𝓕_τ` event `A` and
every measurable set `B` of paths, `P(A ∩ {post-τ path ∈ B}) = P(A) P(X ∈ B)`. -/
theorem strongMarkov_countable {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (τ : Ω → ℝ≥0) (hτc : (Set.range τ).Countable) (A : Set Ω)
    (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t})) (B : Set (ℝ≥0 → ℝ)) (hB : MeasurableSet B) :
    P (A ∩ {ω | (fun u => X (τ ω + u) ω - X (τ ω) ω) ∈ B}) =
      P A * P {ω | (fun u => X u ω) ∈ B} := by
  have hXm := hX.isSNLevy.measurable
  have hAd := measurableSet_inter_eq 𝓕 τ hτc A hA
  have hAm : ∀ d, MeasurableSet (A ∩ {ω | τ ω = d}) := fun d => 𝓕.le d _ (hAd d)
  -- the law of every post-`d` path is the law of `X`
  have hlaw : ∀ d, P (postPath X d ⁻¹' B) = P {ω | (fun u => X u ω) ∈ B} := by
    intro d
    exact (identDistrib_postIncrements P X hX.isSNLevy d).measure_mem_eq hB
  -- independence of the post-`d` path from `𝓕 d`
  have hind : ∀ d, P (A ∩ {ω | τ ω = d} ∩ postPath X d ⁻¹' B) =
      P (A ∩ {ω | τ ω = d}) * P (postPath X d ⁻¹' B) := by
    intro d
    have h := (Indep_iff _ _ _).1 (indep_postIncrements_past 𝓕 P X hX d)
      (postPath X d ⁻¹' B) (A ∩ {ω | τ ω = d}) (measurable_postPath_post X d hB) (hAd d)
    rw [Set.inter_comm, h, mul_comm]
  have hsplit : ∀ C : Set Ω, (∀ d, MeasurableSet (C ∩ {ω | τ ω = d})) →
      P C = ∑' d : Set.range τ, P (C ∩ {ω | τ ω = d}) := by
    intro C hC
    have hU : C = ⋃ d ∈ Set.range τ, C ∩ {ω | τ ω = d} := by
      ext ω; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_range,
        exists_prop]
      exact ⟨fun h => ⟨τ ω, ⟨ω, rfl⟩, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
    conv_lhs => rw [hU]
    refine measure_biUnion hτc ?_ fun d _ => hC d
    intro d₁ _ d₂ _ hne
    refine Set.disjoint_left.2 fun ω h1 h2 => hne ?_
    exact h1.2.symm.trans h2.2
  have hC : ∀ d, MeasurableSet ((A ∩ {ω | (fun u => X (τ ω + u) ω - X (τ ω) ω) ∈ B}) ∩
      {ω | τ ω = d}) := by
    intro d
    have : (A ∩ {ω | (fun u => X (τ ω + u) ω - X (τ ω) ω) ∈ B}) ∩ {ω | τ ω = d} =
        A ∩ {ω | τ ω = d} ∩ postPath X d ⁻¹' B := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, postPath]
      constructor
      · rintro ⟨⟨hA, hB⟩, rfl⟩; exact ⟨⟨hA, rfl⟩, hB⟩
      · rintro ⟨⟨hA, rfl⟩, hB⟩; exact ⟨⟨hA, hB⟩, rfl⟩
    rw [this]; exact (hAm d).inter (measurable_postPath X hXm d hB)
  rw [hsplit _ hC, hsplit A hAm, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun ⟨d, _⟩ => ?_
  have : (A ∩ {ω | (fun u => X (τ ω + u) ω - X (τ ω) ω) ∈ B}) ∩ {ω | τ ω = d} =
      A ∩ {ω | τ ω = d} ∩ postPath X d ⁻¹' B := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, postPath]
    constructor
    · rintro ⟨⟨hA, hB⟩, rfl⟩; exact ⟨⟨hA, rfl⟩, hB⟩
    · rintro ⟨⟨hA, rfl⟩, hB⟩; exact ⟨⟨hA, hB⟩, rfl⟩
  simp only
  rw [this, hind d, hlaw d]

/-! ## Dyadic approximation of a stopping time from above -/

/-- `dyad n τ = ⌈2^n τ⌉ / 2^n`, the dyadic approximation of `τ` from above. -/
noncomputable def dyad {Ω : Type*} (n : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (⌈τ ω * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n

lemma le_dyad {Ω : Type*} (n : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) : τ ω ≤ dyad n τ ω := by
  unfold dyad; rw [le_div_iff₀ (by positivity)]; exact Nat.le_ceil _

lemma dyad_le {Ω : Type*} (n : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) : dyad n τ ω ≤ τ ω + (1 / 2) ^ n := by
  unfold dyad
  rw [div_le_iff₀ (by positivity), add_mul, div_pow, one_pow, one_div,
    inv_mul_cancel₀ (by positivity)]
  exact (Nat.ceil_lt_add_one (zero_le (a := τ ω * 2 ^ n))).le

lemma dyad_range_countable {Ω : Type*} (n : ℕ) (τ : Ω → ℝ≥0) : (Set.range (dyad n τ)).Countable := by
  refine (Set.countable_range (fun k : ℕ => (k : ℝ≥0) / 2 ^ n)).mono ?_
  rintro _ ⟨ω, rfl⟩; exact ⟨_, rfl⟩

lemma floor_dyad_le (n : ℕ) (t : ℝ≥0) : (⌊t * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n ≤ t := by
  rw [div_le_iff₀ (by positivity)]; exact Nat.floor_le (zero_le (a := t * 2 ^ n))

lemma dyad_le_iff {Ω : Type*} (n : ℕ) (τ : Ω → ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    dyad n τ ω ≤ t ↔ τ ω ≤ (⌊t * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n := by
  unfold dyad
  rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  constructor
  · intro h
    have : ⌈τ ω * 2 ^ n⌉₊ ≤ ⌊t * 2 ^ n⌋₊ := Nat.le_floor h
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  · intro h
    have : ⌈τ ω * 2 ^ n⌉₊ ≤ ⌊t * 2 ^ n⌋₊ := Nat.ceil_le.2 h
    exact (by exact_mod_cast this : (⌈τ ω * 2 ^ n⌉₊ : ℝ≥0) ≤ ⌊t * 2 ^ n⌋₊).trans
      (Nat.floor_le (zero_le (a := t * 2 ^ n)))

lemma dyad_event {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0)
    (A : Set Ω) (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t})) (n : ℕ) :
    ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | dyad n τ ω ≤ t}) := by
  intro t
  have : A ∩ {ω | dyad n τ ω ≤ t} = A ∩ {ω | τ ω ≤ (⌊t * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, dyad_le_iff]
  rw [this]; exact 𝓕.mono (floor_dyad_le n t) _ (hA _)

lemma tendsto_dyad {Ω : Type*} (τ : Ω → ℝ≥0) (ω : Ω) :
    Filter.Tendsto (fun n => dyad n τ ω) Filter.atTop (nhdsWithin (τ ω) (Set.Ici (τ ω))) := by
  have hp : Filter.Tendsto (fun n : ℕ => ((1 / 2 : ℝ≥0)) ^ n) Filter.atTop (nhds 0) := by
    rw [← NNReal.tendsto_coe]; push_cast
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hu : Filter.Tendsto (fun n : ℕ => τ ω + (1 / 2 : ℝ≥0) ^ n) Filter.atTop (nhds (τ ω)) := by
    simpa using (tendsto_const_nhds (x := τ ω)).add hp
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => le_dyad n τ ω⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (le_dyad · τ ω)
    (dyad_le · τ ω)

/-- Right-continuity carries the post-`dyad` path to the post-`τ` path pointwise. -/
lemma tendsto_post_dyad {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (τ : Ω → ℝ≥0) (ω : Ω) (u : ℝ≥0) :
    Filter.Tendsto (fun n => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω) Filter.atTop
      (nhds (X (τ ω + u) ω - X (τ ω) ω)) := by
  have hc : ∀ r, Filter.Tendsto (fun n => X (dyad n τ ω + r) ω) Filter.atTop
      (nhds (X (τ ω + r) ω)) := by
    intro r
    have h1 : Filter.Tendsto (fun n => dyad n τ ω + r) Filter.atTop
        (nhdsWithin (τ ω + r) (Set.Ici (τ ω + r))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n =>
        add_le_add (le_dyad n τ ω) le_rfl⟩
      exact (tendsto_nhdsWithin_iff.1 (tendsto_dyad τ ω)).1.add tendsto_const_nhds
    exact (hX.right_continuous ω (τ ω + r)).tendsto.comp h1
  have h0 := hc 0
  simp only [add_zero] at h0
  exact (hc u).sub h0

lemma measurable_post_dyad {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℝ)
    (hXm : ∀ t, Measurable (X t)) (τ : Ω → ℝ≥0) (hτ : Measurable τ) (n : ℕ) (u : ℝ≥0) :
    Measurable (fun ω => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω) := by
  have hk : Measurable (fun ω => ⌈τ ω * 2 ^ n⌉₊) :=
    Nat.measurable_ceil.comp (hτ.mul_const _)
  have hF : Measurable (fun p : ℕ × Ω =>
      X ((p.1 : ℝ≥0) / 2 ^ n + u) p.2 - X ((p.1 : ℝ≥0) / 2 ^ n) p.2) :=
    measurable_from_prod_countable_right fun j => by
      dsimp only
      exact Measurable.sub (hXm _) (hXm _)
  have heq : (fun ω => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω) =
      (fun p : ℕ × Ω => X ((p.1 : ℝ≥0) / 2 ^ n + u) p.2 - X ((p.1 : ℝ≥0) / 2 ^ n) p.2) ∘
        (fun ω => (⌈τ ω * 2 ^ n⌉₊, ω)) := by
    funext ω; simp only [Function.comp, dyad]
  rw [heq]
  exact hF.comp (hk.prodMk measurable_id)

/-- Measure form of the countable strong Markov property. -/
lemma map_restrict_countable {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (τ : Ω → ℝ≥0) (hτc : (Set.range τ).Countable) (A : Set Ω)
    (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t}))
    (hZ : Measurable (fun ω (u : ℝ≥0) => X (τ ω + u) ω - X (τ ω) ω)) :
    (P.restrict A).map (fun ω (u : ℝ≥0) => X (τ ω + u) ω - X (τ ω) ω) =
      P A • P.map (fun ω (u : ℝ≥0) => X u ω) := by
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hX.isSNLevy.measurable u
  ext B hB
  rw [Measure.map_apply hZ hB, Measure.smul_apply, Measure.map_apply hXp hB, smul_eq_mul,
    Measure.restrict_apply' ?_]
  · rw [Set.inter_comm]; exact strongMarkov_countable 𝓕 P X hX τ hτc A hA B hB
  · have hAd := measurableSet_inter_eq 𝓕 τ hτc A hA
    have hU : A = ⋃ d ∈ Set.range τ, A ∩ {ω | τ ω = d} := by
      ext ω; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_range,
        exists_prop]
      exact ⟨fun h => ⟨τ ω, ⟨ω, rfl⟩, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
    rw [hU]; exact MeasurableSet.biUnion hτc fun d _ => 𝓕.le d _ (hAd d)

/-! ## Strong Markov property at a general stopping time -/

lemma measurable_post {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (τ : Ω → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω (u : ℝ≥0) => X (τ ω + u) ω - X (τ ω) ω) := by
  refine measurable_pi_lambda _ fun u => ?_
  exact measurable_of_tendsto_metrizable
    (fun n => measurable_post_dyad X hX.measurable τ hτ n u)
    (tendsto_pi_nhds.2 fun ω => tendsto_post_dyad hX τ ω u)

/-- Finite-dimensional strong Markov identity at a general stopping time. -/
lemma map_restrict_fdd {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (A : Set Ω)
    (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t})) (I : Finset ℝ≥0) :
    (P.restrict A).map (fun ω => I.restrict (fun u => X (τ ω + u) ω - X (τ ω) ω)) =
      (P A).toNNReal • P.map (fun ω => I.restrict (fun u => X u ω)) := by
  have hXL := hX.isSNLevy
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) := measurable_pi_lambda _ fun u => hXL.measurable u
  have hcoe : ((P A).toNNReal : ℝ≥0∞) = P A := ENNReal.coe_toNNReal (measure_ne_top P A)
  have hsm : ∀ μ : Measure (I → ℝ), (P A).toNNReal • μ = P A • μ := fun μ => by
    ext s hs
    rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, hcoe, smul_eq_mul]
  -- the identity for every dyadic approximation
  have hn : ∀ n : ℕ, (P.restrict A).map
      (fun ω => I.restrict (fun u => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω)) =
      (P A).toNNReal • P.map (fun ω => I.restrict (fun u => X u ω)) := by
    intro n
    have hZ : Measurable (fun ω (u : ℝ≥0) => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω) :=
      measurable_pi_lambda _ fun u => measurable_post_dyad X hXL.measurable τ hτ n u
    have h := map_restrict_countable 𝓕 P X hX (dyad n τ) (dyad_range_countable n τ) A
      (dyad_event 𝓕 τ A hA n) hZ
    have h2 := congrArg (Measure.map I.restrict) h
    rw [Measure.map_map (Finset.measurable_restrict _) hZ, Measure.map_smul,
      Measure.map_map (Finset.measurable_restrict _) hXp] at h2
    rw [hsm]
    exact h2
  have hZ : Measurable (fun ω (u : ℝ≥0) => X (τ ω + u) ω - X (τ ω) ω) := measurable_post hXL τ hτ
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  -- both sides equal the limit of the dyadic integrals
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ x, f x ∂((P.restrict A).map
      (fun ω => I.restrict (fun u => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω))))
      Filter.atTop (nhds (∫ x, f x ∂((P.restrict A).map
        (fun ω => I.restrict (fun u => X (τ ω + u) ω - X (τ ω) ω))))) := by
    have hmeas : ∀ n : ℕ, Measurable
        (fun ω => I.restrict (fun u => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω)) := fun n =>
      (Finset.measurable_restrict _).comp
        (measurable_pi_lambda _ fun u => measurable_post_dyad X hXL.measurable τ hτ n u)
    have hm1 : ∀ n : ℕ, ∫ x, f x ∂((P.restrict A).map
        (fun ω => I.restrict (fun u => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω))) =
        ∫ ω, f (I.restrict (fun u => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω)) ∂(P.restrict A) :=
      fun n => integral_map (hmeas n).aemeasurable f.continuous.aestronglyMeasurable
    simp_rw [hm1]
    have hZI : Measurable (fun ω => I.restrict (fun u => X (τ ω + u) ω - X (τ ω) ω)) :=
      (Finset.measurable_restrict _).comp hZ
    rw [integral_map hZI.aemeasurable f.continuous.aestronglyMeasurable]
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) (fun n => ?_)
      (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact (f.continuous.measurable.comp (hmeas n)).aestronglyMeasurable
    · refine (f.continuous.tendsto _).comp ?_
      exact tendsto_pi_nhds.2 fun u => tendsto_post_dyad hXL τ ω u
  have hconst : ∀ n : ℕ, ∫ x, f x ∂((P.restrict A).map
      (fun ω => I.restrict (fun u => X (dyad n τ ω + u) ω - X (dyad n τ ω) ω))) =
      ∫ x, f x ∂((P A).toNNReal • P.map (fun ω => I.restrict (fun u => X u ω))) :=
    fun n => by rw [hn n]
  simp_rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- STRONG MARKOV PROPERTY (G0.1) of a spectrally negative Lévy process at a finite stopping time
`τ`: for every `𝓕_τ` event `A`, the law of the post-`τ` increment path restricted to `A` is
`P(A)` times the law of `X`.  In particular the post-`τ` path is independent of `𝓕_τ` and is
again distributed as `X`. -/
theorem strongMarkov {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (A : Set Ω)
    (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t})) :
    (P.restrict A).map (fun ω (u : ℝ≥0) => X (τ ω + u) ω - X (τ ω) ω) =
      (P A).toNNReal • P.map (fun ω (u : ℝ≥0) => X u ω) := by
  have hXL := hX.isSNLevy
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) := measurable_pi_lambda _ fun u => hXL.measurable u
  have hZ : Measurable (fun ω (u : ℝ≥0) => X (τ ω + u) ω - X (τ ω) ω) := measurable_post hXL τ hτ
  have h1 : IsProjectiveLimit ((P.restrict A).map (fun ω (u : ℝ≥0) => X (τ ω + u) ω - X (τ ω) ω))
      (fun I => ((P A).toNNReal • P.map (fun ω (u : ℝ≥0) => X u ω)).map I.restrict) := by
    intro I
    show _ = Measure.map I.restrict ((P A).toNNReal • Measure.map (fun ω (u : ℝ≥0) => X u ω) P)
    rw [Measure.map_map (Finset.measurable_restrict _) hZ, Measure.map_smul,
      Measure.map_map (Finset.measurable_restrict _) hXp]
    exact map_restrict_fdd 𝓕 P X hX τ hτ A hA I
  exact h1.unique (fun I => rfl)

/-- Set form of the strong Markov property. -/
theorem strongMarkov_set {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (A : Set Ω) (hAm : MeasurableSet A)
    (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t})) (B : Set (ℝ≥0 → ℝ)) (hB : MeasurableSet B) :
    P (A ∩ {ω | (fun u => X (τ ω + u) ω - X (τ ω) ω) ∈ B}) =
      P A * P {ω | (fun u => X u ω) ∈ B} := by
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hX.isSNLevy.measurable u
  have hZ := measurable_post hX.isSNLevy τ hτ
  have h := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ B) (strongMarkov 𝓕 P X hX τ hτ A hA)
  rw [Measure.map_apply hZ hB, Measure.restrict_apply (hZ hB), Measure.smul_apply,
    Measure.map_apply hXp hB, ENNReal.smul_def, ENNReal.coe_toNNReal (measure_ne_top P A),
    smul_eq_mul] at h
  rw [Set.inter_comm]; exact h

end Avram2004.Markov92562e40


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Avram2004.Markov92562e40

/-- Upward creeping, pathwise: a right-continuous path started at `0` with left limits and no
positive jumps hits every level `a ≥ 0` it exceeds exactly at its first passage time. -/
theorem creep_path (f : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hll : ∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l))
    (hnj : ∀ t : ℝ≥0, 0 < t → f t ≤ Function.leftLim f t) (h0 : f 0 = 0)
    {a : ℝ} (ha : 0 ≤ a) (hne : ∃ t, a < f t) :
    f (sInf {t | a < f t}) = a := by
  set S := {t | a < f t} with hS
  have hbdd : BddBelow S := OrderBot.bddBelow S
  have hSne : S.Nonempty := hne
  set τ := sInf S with hτ
  have hbefore : ∀ t, t < τ → f t ≤ a := by
    intro t ht
    by_contra h
    exact (not_le.mpr ht) (csInf_le hbdd (not_le.mp h))
  have hge : a ≤ f τ := by
    by_contra h
    push_neg at h
    have hev : ∀ᶠ t in 𝓝[≥] τ, f t < a := (hrc τ).eventually (gt_mem_nhds h)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have hut : u ≤ τ := by
      apply le_csInf hSne
      intro x hx
      by_contra hxu
      push_neg at hxu
      have hx1 : τ ≤ x := csInf_le hbdd hx
      have hfx : f x < a := hsub ⟨hx1, hxu⟩
      exact absurd hx (not_lt.mpr hfx.le)
    exact absurd (show τ < u from hu) (not_lt.mpr hut)
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ τ) with h | h
  · rw [← h, h0] at hge ⊢
    linarith
  · obtain ⟨l, hl⟩ := hll τ h
    haveI : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, h⟩
    have hlim : Function.leftLim f τ = l := leftLim_eq_of_tendsto hl
    have hla : l ≤ a := le_of_tendsto hl (eventually_nhdsWithin_of_forall fun t ht => hbefore t ht)
    have := hnj τ h
    linarith

/-- First passage strictly above `a`, truncated at `T`. -/
noncomputable def hitT {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  sInf ({t | a < X t ω} ∪ Set.Ici T)

lemma hitT_le {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) (ω : Ω) : hitT X a T ω ≤ T :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_union_right _ (Set.mem_Ici.mpr le_rfl))

lemma hitT_lt_iff {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) (ω : Ω) (s : ℝ≥0) :
    hitT X a T ω < s ↔ T < s ∨ ∃ t, t < s ∧ a < X t ω := by
  unfold hitT
  rw [csInf_lt_iff (OrderBot.bddBelow _) ⟨T, Set.mem_union_right _ (Set.mem_Ici.mpr le_rfl)⟩]
  constructor
  · rintro ⟨t, ht | ht, hts⟩
    · exact Or.inr ⟨t, hts, ht⟩
    · exact Or.inl (lt_of_le_of_lt ht hts)
  · rintro (h | ⟨t, hts, ht⟩)
    · exact ⟨T, Set.mem_union_right _ (Set.mem_Ici.mpr le_rfl), h⟩
    · exact ⟨t, Or.inl ht, hts⟩

lemma exists_rat_hit (f : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t) {a : ℝ}
    {s : ℝ≥0} (h : ∃ t, t < s ∧ a < f t) :
    ∃ q : ℚ, Real.toNNReal q < s ∧ a < f (Real.toNNReal q) := by
  obtain ⟨t, hts, ht⟩ := h
  have hev : ∀ᶠ r in 𝓝[≥] t, a < f r := (hrc t).eventually (lt_mem_nhds ht)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
  have hlt : (t : ℝ) < ((min u s : ℝ≥0) : ℝ) := by exact_mod_cast lt_min hu hts
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have hq0 : (0 : ℝ) ≤ q := le_trans t.2 hq1.le
  have hqe : ((Real.toNNReal q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
  have h1 : t ≤ Real.toNNReal q := by rw [← NNReal.coe_le_coe, hqe]; exact hq1.le
  have h2 : Real.toNNReal q < min u s := by rw [← NNReal.coe_lt_coe, hqe]; exact hq2
  exact ⟨q, lt_of_lt_of_le h2 (min_le_right _ _), hsub ⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩⟩

lemma measurableSet_hitT_lt {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevyWrt 𝓕 P X) (a : ℝ) (T s : ℝ≥0) :
    MeasurableSet[𝓕 s] {ω | hitT X a T ω < s} := by
  have heq : {ω | hitT X a T ω < s} = {ω | T < s} ∪
      ⋃ q : ℚ, {ω | Real.toNNReal q < s ∧ a < X (Real.toNNReal q) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, hitT_lt_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (exists_rat_hit _ (hX.isSNLevy.right_continuous ω) h)
    · rintro (h | ⟨q, hq, hq'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨_, hq, hq'⟩
  rw [heq]
  refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun q => ?_)
  · by_cases h : T < s
    · simp [h]
    · simp [h]
  · by_cases h : Real.toNNReal q < s
    · have hm : MeasurableSet[𝓕 (Real.toNNReal q)] (X (Real.toNNReal q) ⁻¹' Set.Ioi a) :=
        (hX.adapted (Real.toNNReal q)) measurableSet_Ioi
      convert 𝓕.mono h.le _ hm using 1
      ext ω
      simp [h]
    · simp [h]

lemma measurableSet_hitT_le {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevyWrt 𝓕 P X) (a : ℝ) (T t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | hitT X a T ω ≤ t} := by
  have := hX.right_continuous_filtration
  have hst : IsStoppingTime 𝓕 (fun ω => ((hitT X a T ω : ℝ≥0) : WithTop ℝ≥0)) := by
    apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    intro i
    show MeasurableSet[𝓕 i] {ω | ((hitT X a T ω : ℝ≥0) : WithTop ℝ≥0) < (i : WithTop ℝ≥0)}
    simp only [WithTop.coe_lt_coe]
    exact measurableSet_hitT_lt 𝓕 hX a T i
  have h := hst t
  simp only [WithTop.coe_le_coe] at h
  exact h

lemma measurable_hitT {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevyWrt 𝓕 P X) (a : ℝ) (T : ℝ≥0) :
    Measurable (hitT X a T) :=
  measurable_of_Iic fun t => 𝓕.le t _ (measurableSet_hitT_le 𝓕 hX a T t)

lemma hitT_eq {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) (ω : Ω)
    (h : ∃ t, t < T ∧ a < X t ω) : hitT X a T ω = sInf {t | a < X t ω} := by
  obtain ⟨t0, ht0T, ht0⟩ := h
  have hSne : ({t | a < X t ω} : Set ℝ≥0).Nonempty := ⟨t0, ht0⟩
  apply le_antisymm
  · exact le_csInf hSne fun x hx => csInf_le (OrderBot.bddBelow _) (Set.mem_union_left _ hx)
  · apply le_csInf ⟨T, Set.mem_union_right _ (Set.mem_Ici.mpr le_rfl)⟩
    rintro x (hx | hx)
    · exact csInf_le (OrderBot.bddBelow _) hx
    · exact le_trans (csInf_le (OrderBot.bddBelow _) ht0) (le_trans ht0T.le hx)

/-- Upward creeping at the truncated first passage time. -/
theorem creep_hitT {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) {a : ℝ} (ha : 0 ≤ a) (T : ℝ≥0) (ω : Ω)
    (h : ∃ t, t < T ∧ a < X t ω) : X (hitT X a T ω) ω = a := by
  rw [hitT_eq X a T ω h]
  obtain ⟨t0, -, ht0⟩ := h
  exact creep_path (fun r => X r ω) (hX.right_continuous ω) (hX.left_limits ω)
    (hX.no_positive_jumps ω) (hX.start_zero ω) ha ⟨t0, ht0⟩

/-- Before the truncated first passage, the path stays at or below `a`. -/
lemma le_of_lt_hitT {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) (ω : Ω) (t : ℝ≥0)
    (ht : t < hitT X a T ω) : X t ω ≤ a := by
  by_contra h
  exact (not_le.mpr ht) (csInf_le (OrderBot.bddBelow _) (Set.mem_union_left _ (not_le.mp h)))

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

/-- "The path exceeds `c` at some time", through rational times (a measurable set of paths). -/
def exceedSet (c : ℝ) : Set (ℝ≥0 → ℝ) := ⋃ q : ℚ, {f | c < f (Real.toNNReal q)}

lemma measurableSet_exceedSet (c : ℝ) : MeasurableSet (exceedSet c) :=
  MeasurableSet.iUnion fun q => measurableSet_lt measurable_const (measurable_pi_apply _)

lemma mem_exceedSet_iff (f : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t) (c : ℝ) :
    f ∈ exceedSet c ↔ ∃ t, c < f t := by
  simp only [exceedSet, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨_, hq⟩
  · rintro ⟨t, ht⟩
    obtain ⟨q, -, hq⟩ := exists_rat_hit f hrc (s := t + 1) ⟨t, lt_add_one t, ht⟩
    exact ⟨q, hq⟩

lemma post_rc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (d : ℝ≥0) (ω : Ω) :
    ∀ u, ContinuousWithinAt (fun u => X (d + u) ω - X d ω) (Set.Ici u) u := by
  intro u
  have h1 : ContinuousWithinAt (fun r => X r ω) (Set.Ici (d + u)) (d + u) :=
    hX.right_continuous ω (d + u)
  have h2 : ContinuousWithinAt (fun v : ℝ≥0 => d + v) (Set.Ici u) u :=
    (continuous_const.add continuous_id).continuousWithinAt
  have h3 := h1.comp h2 (fun x hx => (add_le_add le_rfl hx : d + u ≤ d + x))
  exact h3.sub continuousWithinAt_const

lemma mem_A_iff {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) (ω : Ω) :
    hitT X a T ω < T ↔ ∃ t, t < T ∧ a < X t ω := by
  rw [hitT_lt_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (lt_irrefl _)
    · exact h
  · exact Or.inr

/-- G0.2: tails of the all-time supremum are multiplicative,
`P(sup X > a + b) = P(sup X > a) P(sup X > b)` for `a, b ≥ 0` (strong Markov at the first
passage above `a` + upward creeping). -/
theorem sup_mult {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    P {ω | ∃ t, a + b < X t ω} = P {ω | ∃ t, a < X t ω} * P {ω | ∃ t, b < X t ω} := by
  have hXL := hX.isSNLevy
  have hE : ∀ c, {ω | ∃ t, c < X t ω} = {ω | (fun u => X u ω) ∈ exceedSet c} := by
    intro c
    ext ω
    exact (mem_exceedSet_iff _ (hXL.right_continuous ω) c).symm
  set A : ℕ → Set Ω := fun n => {ω | hitT X a (n : ℝ≥0) ω < (n : ℝ≥0)} with hAdef
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    𝓕.le _ _ (measurableSet_hitT_lt 𝓕 hX a (n : ℝ≥0) (n : ℝ≥0))
  have hAst : ∀ n (t : ℝ≥0), MeasurableSet[𝓕 t] (A n ∩ {ω | hitT X a (n : ℝ≥0) ω ≤ t}) := by
    intro n t
    by_cases ht : (n : ℝ≥0) ≤ t
    · exact (𝓕.mono ht _ (measurableSet_hitT_lt 𝓕 hX a (n : ℝ≥0) (n : ℝ≥0))).inter
        (measurableSet_hitT_le 𝓕 hX a _ t)
    · push_neg at ht
      have heq : A n ∩ {ω | hitT X a (n : ℝ≥0) ω ≤ t} = {ω | hitT X a (n : ℝ≥0) ω ≤ t} := by
        ext ω
        exact ⟨fun h => h.2, fun h => ⟨lt_of_le_of_lt h ht, h⟩⟩
      rw [heq]
      exact measurableSet_hitT_le 𝓕 hX a _ t
  have hkey : ∀ n, A n ∩ {ω | ∃ t, a + b < X t ω} =
      A n ∩ {ω | (fun u => X (hitT X a (n : ℝ≥0) ω + u) ω - X (hitT X a (n : ℝ≥0) ω) ω) ∈
        exceedSet b} := by
    intro n
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hA, t, ht⟩
      refine ⟨hA, ?_⟩
      have hcr := creep_hitT hXL ha (n : ℝ≥0) ω ((mem_A_iff X a _ ω).mp hA)
      rw [mem_exceedSet_iff _ (post_rc hXL _ ω)]
      have hτt : hitT X a (n : ℝ≥0) ω ≤ t := by
        by_contra h
        have := le_of_lt_hitT X a (n : ℝ≥0) ω t (not_le.mp h)
        linarith
      refine ⟨t - hitT X a (n : ℝ≥0) ω, ?_⟩
      rw [add_tsub_cancel_of_le hτt, hcr]
      linarith
    · rintro ⟨hA, hpost⟩
      refine ⟨hA, ?_⟩
      have hcr := creep_hitT hXL ha (n : ℝ≥0) ω ((mem_A_iff X a _ ω).mp hA)
      rw [mem_exceedSet_iff _ (post_rc hXL _ ω)] at hpost
      obtain ⟨u, hu⟩ := hpost
      rw [hcr] at hu
      exact ⟨_, by linarith⟩
  have hSM : ∀ n, P (A n ∩ {ω | ∃ t, a + b < X t ω}) = P (A n) * P {ω | ∃ t, b < X t ω} := by
    intro n
    rw [hkey n, hE b]
    exact strongMarkov_set 𝓕 P X hX _ (measurable_hitT 𝓕 hX a _) (A n) (hAm n) (hAst n)
      (exceedSet b) (measurableSet_exceedSet b)
  have hAmono : Monotone A := by
    intro i j hij ω hω
    simp only [hAdef, Set.mem_setOf_eq, mem_A_iff] at hω ⊢
    obtain ⟨t, ht, ht'⟩ := hω
    exact ⟨t, lt_of_lt_of_le ht (by exact_mod_cast hij), ht'⟩
  have hAU : ⋃ n, A n = {ω | ∃ t, a < X t ω} := by
    ext ω
    simp only [hAdef, Set.mem_iUnion, Set.mem_setOf_eq, mem_A_iff]
    constructor
    · rintro ⟨n, t, -, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      obtain ⟨n, hn⟩ := exists_nat_gt t
      exact ⟨n, t, hn, ht⟩
  have hsub : {ω | ∃ t, a + b < X t ω} ⊆ {ω | ∃ t, a < X t ω} := by
    rintro ω ⟨t, ht⟩
    exact ⟨t, by linarith⟩
  have hlim1 : Filter.Tendsto (fun n => P (A n ∩ {ω | ∃ t, a + b < X t ω})) Filter.atTop
      (𝓝 (P {ω | ∃ t, a + b < X t ω})) := by
    have hmono : Monotone fun n => A n ∩ {ω | ∃ t, a + b < X t ω} :=
      fun i j hij => Set.inter_subset_inter_left _ (hAmono hij)
    have h := tendsto_measure_iUnion_atTop (μ := P) hmono
    rwa [← Set.iUnion_inter, hAU, Set.inter_eq_right.mpr hsub] at h
  have hlim2 : Filter.Tendsto (fun n => P (A n) * P {ω | ∃ t, b < X t ω}) Filter.atTop
      (𝓝 (P {ω | ∃ t, a < X t ω} * P {ω | ∃ t, b < X t ω})) := by
    have h := tendsto_measure_iUnion_atTop (μ := P) hAmono
    rw [hAU] at h
    exact ENNReal.Tendsto.mul_const h (Or.inr (measure_ne_top _ _))
  simp_rw [hSM] at hlim1
  exact tendsto_nhds_unique hlim1 hlim2

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

/-- The σ-algebra of Borel sets `s` with `A ∩ τ⁻¹ s` an `𝓕_τ`-event. -/
def tauSigma {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t})) : MeasurableSpace ℝ≥0 :=
  { MeasurableSet' := fun s => ∀ t, MeasurableSet[𝓕 t] ((A ∩ τ ⁻¹' s) ∩ {ω | τ ω ≤ t})
    measurableSet_empty := fun t => by simp
    measurableSet_compl := fun s hs t => by
      have : (A ∩ τ ⁻¹' sᶜ) ∩ {ω | τ ω ≤ t} =
          (A ∩ {ω | τ ω ≤ t}) \ ((A ∩ τ ⁻¹' s) ∩ {ω | τ ω ≤ t}) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_diff,
          Set.mem_setOf_eq]
        tauto
      rw [this]
      exact (hA t).diff (hs t)
    measurableSet_iUnion := fun f hf t => by
      have : (A ∩ τ ⁻¹' ⋃ i, f i) ∩ {ω | τ ω ≤ t} = ⋃ i, (A ∩ τ ⁻¹' f i) ∩ {ω | τ ω ≤ t} := by
        ext ω
        simp only [Set.preimage_iUnion, Set.mem_inter_iff, Set.mem_iUnion]
        tauto
      rw [this]
      exact MeasurableSet.iUnion fun i => hf i t }

/-- `τ⁻¹ s ∩ A` is an `𝓕_τ`-event for every Borel `s` when `A` is one. -/
lemma stopped_preimage {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (τ : Ω → ℝ≥0) (A : Set Ω) (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t}))
    (s : Set ℝ≥0) (hs : MeasurableSet s) :
    ∀ t, MeasurableSet[𝓕 t] ((A ∩ τ ⁻¹' s) ∩ {ω | τ ω ≤ t}) := by
  have hle : NNReal.measurableSpace ≤ tauSigma 𝓕 τ A hA := by
    rw [@BorelSpace.measurable_eq ℝ≥0 _ NNReal.measurableSpace _, borel_eq_generateFrom_Iic]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨r, rfl⟩ t
    have : (A ∩ τ ⁻¹' Set.Iic r) ∩ {ω | τ ω ≤ t} = A ∩ {ω | τ ω ≤ min r t} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq, le_min_iff]
      tauto
    rw [this]
    exact 𝓕.mono (min_le_right r t) _ (hA (min r t))
  exact hle s hs

/-- Strong Markov, joint form: on an `𝓕_τ`-event `A`, the pair (τ, post-τ increment path) has the
product law `(law of τ on A) ⊗ (law of X)`. -/
theorem strongMarkov_joint {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (A : Set Ω) (hAm : MeasurableSet A)
    (hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | τ ω ≤ t})) :
    (P.restrict A).map (fun ω => (τ ω, fun u => X (τ ω + u) ω - X (τ ω) ω)) =
      ((P.restrict A).map τ).prod (P.map (fun ω (u : ℝ≥0) => X u ω)) := by
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hX.isSNLevy.measurable u
  have hZ := measurable_post hX.isSNLevy τ hτ
  symm
  apply Measure.prod_eq
  intro s B hs hB
  rw [Measure.map_apply (hτ.prodMk hZ) (hs.prod hB), Measure.map_apply hτ hs,
    Measure.map_apply hXp hB, Measure.restrict_apply ((hτ.prodMk hZ) (hs.prod hB)),
    Measure.restrict_apply (hτ hs)]
  have h := strongMarkov_set 𝓕 P X hX τ hτ (A ∩ τ ⁻¹' s) (hAm.inter (hτ hs))
    (stopped_preimage 𝓕 τ A hA s hs) B hB
  rw [Set.inter_comm (τ ⁻¹' s) A]
  refine Eq.trans ?_ h
  congr 1
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]
  tauto

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

/-- First passage strictly above `c` (equal to `0` when the level is never exceeded). -/
noncomputable def pass {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (c : ℝ) (ω : Ω) : ℝ≥0 :=
  sInf {t | c < X t ω}

/-- First passage above `c` read off rational times: a measurable function on path space. -/
noncomputable def passQ (c : ℝ) (f : ℝ≥0 → ℝ) : ℝ≥0 :=
  sInf {r | ∃ q : ℚ, Real.toNNReal q = r ∧ c < f r}

lemma passQ_lt_iff (c : ℝ) (f : ℝ≥0 → ℝ) (s : ℝ≥0) (hf : f ∈ exceedSet c) :
    passQ c f < s ↔ ∃ q : ℚ, Real.toNNReal q < s ∧ c < f (Real.toNNReal q) := by
  have hne : ({r | ∃ q : ℚ, Real.toNNReal q = r ∧ c < f r} : Set ℝ≥0).Nonempty := by
    simp only [exceedSet, Set.mem_iUnion, Set.mem_setOf_eq] at hf
    obtain ⟨q, hq⟩ := hf
    exact ⟨_, q, rfl, hq⟩
  unfold passQ
  rw [csInf_lt_iff (OrderBot.bddBelow _) hne]
  constructor
  · rintro ⟨r, ⟨q, rfl, hq⟩, hr⟩
    exact ⟨q, hr, hq⟩
  · rintro ⟨q, hqs, hq⟩
    exact ⟨_, ⟨q, rfl, hq⟩, hqs⟩

lemma passQ_of_not (c : ℝ) (f : ℝ≥0 → ℝ) (hf : f ∉ exceedSet c) : passQ c f = 0 := by
  have : ({r | ∃ q : ℚ, Real.toNNReal q = r ∧ c < f r} : Set ℝ≥0) = ∅ := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨q, rfl, hq⟩
    exact hf (Set.mem_iUnion.mpr ⟨q, hq⟩)
  unfold passQ
  rw [this, NNReal.sInf_empty]

lemma measurable_passQ (c : ℝ) : Measurable (passQ c) := by
  refine measurable_of_Iio fun s => ?_
  have heq : passQ c ⁻¹' Set.Iio s = ((exceedSet c)ᶜ ∩ {_f | (0 : ℝ≥0) < s}) ∪
      ⋃ q : ℚ, {f | Real.toNNReal q < s ∧ c < f (Real.toNNReal q)} := by
    ext f
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    by_cases hf : f ∈ exceedSet c
    · rw [passQ_lt_iff c f s hf]
      simp [hf]
    · rw [passQ_of_not c f hf]
      constructor
      · intro h
        exact Or.inl ⟨hf, h⟩
      · rintro (⟨-, h⟩ | ⟨q, -, hq⟩)
        · exact h
        · exact absurd (Set.mem_iUnion.mpr ⟨q, hq⟩) hf
  rw [heq]
  refine ((measurableSet_exceedSet c).compl.inter ?_).union (MeasurableSet.iUnion fun q => ?_)
  · by_cases h : (0 : ℝ≥0) < s <;> simp [h]
  · by_cases h : Real.toNNReal q < s
    · have hm : MeasurableSet {f : ℝ≥0 → ℝ | c < f (Real.toNNReal q)} :=
        measurableSet_lt measurable_const (measurable_pi_apply _)
      convert hm using 1
      ext f
      simp [h]
    · simp [h]

lemma passQ_eq (f : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t) (c : ℝ)
    (hne : ∃ t, c < f t) : passQ c f = sInf {t | c < f t} := by
  have hf : f ∈ exceedSet c := (mem_exceedSet_iff f hrc c).mpr hne
  apply le_antisymm
  · apply le_csInf hne
    intro t ht
    by_contra h
    push_neg at h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_hit f hrc (s := passQ c f) ⟨t, h, ht⟩
    exact absurd ((passQ_lt_iff c f _ hf).mpr ⟨q, hq1, hq2⟩) (lt_irrefl _)
  · by_contra h
    push_neg at h
    obtain ⟨q, hq1, hq2⟩ := (passQ_lt_iff c f _ hf).mp h
    exact absurd (csInf_le (OrderBot.bddBelow {t | c < f t})
      (show Real.toNNReal q ∈ {t | c < f t} from hq2)) (not_le.mpr hq1)

lemma pass_eq_passQ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (c : ℝ) (ω : Ω) : pass X c ω = passQ c (fun u => X u ω) := by
  by_cases h : ∃ t, c < X t ω
  · exact (passQ_eq _ (hX.right_continuous ω) c h).symm
  · have h1 : ({t | c < X t ω} : Set ℝ≥0) = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun ht => h ⟨t, ht⟩
    unfold pass
    rw [h1, NNReal.sInf_empty, passQ_of_not]
    rwa [mem_exceedSet_iff _ (hX.right_continuous ω)]

lemma measurable_pass {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (c : ℝ) : Measurable (pass X c) := by
  have : pass X c = fun ω => passQ c (fun u => X u ω) := funext (pass_eq_passQ hX c)
  rw [this]
  exact (measurable_passQ c).comp (measurable_pi_lambda _ fun u => hX.measurable u)

/-- Pathwise additivity of first passage times (upward creeping at `pass a`). -/
lemma pass_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ω : Ω)
    (h : ∃ t, a + b < X t ω) :
    pass X (a + b) ω =
      pass X a ω + passQ b (fun u => X (pass X a ω + u) ω - X (pass X a ω) ω) := by
  have hA : ∃ t, a < X t ω := by
    obtain ⟨t, ht⟩ := h
    exact ⟨t, by linarith⟩
  set d := pass X a ω with hd
  have hcr : X d ω = a := creep_path (fun r => X r ω) (hX.right_continuous ω)
    (hX.left_limits ω) (hX.no_positive_jumps ω) (hX.start_zero ω) ha hA
  have hbefore : ∀ t, t < d → X t ω ≤ a := fun t ht => by
    by_contra h'
    exact (not_le.mpr ht) (csInf_le (OrderBot.bddBelow _) (not_le.mp h'))
  have hU : ∃ u, b < X (d + u) ω - X d ω := by
    obtain ⟨t, ht⟩ := h
    have hdt : d ≤ t := by
      by_contra h'
      have := hbefore t (not_le.mp h')
      linarith
    exact ⟨t - d, by rw [add_tsub_cancel_of_le hdt, hcr]; linarith⟩
  rw [passQ_eq _ (post_rc hX d ω) b hU]
  have himg : {t | a + b < X t ω} = (fun u => d + u) '' {u | b < X (d + u) ω - X d ω} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro ht
      have hdt : d ≤ t := by
        by_contra h'
        have := hbefore t (not_le.mp h')
        linarith
      exact ⟨t - d, by rw [add_tsub_cancel_of_le hdt, hcr]; linarith, add_tsub_cancel_of_le hdt⟩
    · rintro ⟨u, hu, rfl⟩
      rw [hcr] at hu
      linarith
  show sInf {t | a + b < X t ω} = _
  rw [himg]
  exact (Monotone.map_csInf_of_continuousAt (f := fun u : ℝ≥0 => d + u)
    (continuous_const.add continuous_id).continuousAt (fun x y hxy => add_le_add le_rfl hxy)
    hU (OrderBot.bddBelow _)).symm

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

/-- `e^{-q τ_c}` as an extended nonnegative real. -/
noncomputable def expPass {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (q c : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(q * (pass X c ω : ℝ))))

/-- `1{path exceeds b} e^{-q τ_b(path)}` on path space. -/
noncomputable def gQ (q b : ℝ) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  (exceedSet b).indicator (fun f => ENNReal.ofReal (Real.exp (-(q * (passQ b f : ℝ))))) f

lemma measurable_kq (q : ℝ) : Measurable (fun s : ℝ≥0 => ENNReal.ofReal (Real.exp (-(q * (s : ℝ))))) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.mul measurable_coe_nnreal_real).neg))

lemma measurable_gQ (q b : ℝ) : Measurable (gQ q b) :=
  ((measurable_kq q).comp (measurable_passQ b)).indicator (measurableSet_exceedSet b)

lemma measurable_expPass {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (q c : ℝ) : Measurable (expPass X q c) :=
  (measurable_kq q).comp (measurable_pass hX c)

lemma post_exceed_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ω : Ω)
    (hA : ∃ t, a < X t ω) :
    (∃ t, a + b < X t ω) ↔ ∃ u, b < X (pass X a ω + u) ω - X (pass X a ω) ω := by
  set d := pass X a ω with hd
  have hcr : X d ω = a := creep_path (fun r => X r ω) (hX.right_continuous ω)
    (hX.left_limits ω) (hX.no_positive_jumps ω) (hX.start_zero ω) ha hA
  have hbefore : ∀ t, t < d → X t ω ≤ a := fun t ht => by
    by_contra h'
    exact (not_le.mpr ht) (csInf_le (OrderBot.bddBelow _) (not_le.mp h'))
  constructor
  · rintro ⟨t, ht⟩
    have hdt : d ≤ t := by
      by_contra h'
      have := hbefore t (not_le.mp h')
      linarith
    exact ⟨t - d, by rw [add_tsub_cancel_of_le hdt, hcr]; linarith⟩
  · rintro ⟨u, hu⟩
    rw [hcr] at hu
    exact ⟨_, by linarith⟩

lemma key_point {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℝ) (T : ℝ≥0) (ω : Ω)
    (hT : hitT X a T ω < T) :
    {ω | ∃ t, a + b < X t ω}.indicator (expPass X q (a + b)) ω =
      ENNReal.ofReal (Real.exp (-(q * (hitT X a T ω : ℝ)))) *
        gQ q b (fun u => X (hitT X a T ω + u) ω - X (hitT X a T ω) ω) := by
  have hex := (mem_A_iff X a T ω).mp hT
  have hpa : hitT X a T ω = pass X a ω := hitT_eq X a T ω hex
  have hA : ∃ t, a < X t ω := by
    obtain ⟨t, -, ht⟩ := hex
    exact ⟨t, ht⟩
  rw [hpa]
  have hiff := post_exceed_iff hX ha hb ω hA
  by_cases h : ∃ t, a + b < X t ω
  · have h' : (fun u => X (pass X a ω + u) ω - X (pass X a ω) ω) ∈ exceedSet b :=
      (mem_exceedSet_iff _ (post_rc hX _ ω) b).mpr (hiff.mp h)
    rw [Set.indicator_of_mem (show ω ∈ {ω | ∃ t, a + b < X t ω} from h), gQ,
      Set.indicator_of_mem h', expPass, pass_add hX ha hb ω h, NNReal.coe_add, mul_add, neg_add,
      Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  · have h' : (fun u => X (pass X a ω + u) ω - X (pass X a ω) ω) ∉ exceedSet b := fun h' =>
      h (hiff.mpr ((mem_exceedSet_iff _ (post_rc hX _ ω) b).mp h'))
    rw [Set.indicator_of_notMem (show ω ∉ {ω | ∃ t, a + b < X t ω} from h), gQ,
      Set.indicator_of_notMem h', mul_zero]

/-- G0.3a: the Laplace transform of first passage is multiplicative in the level,
`E[e^{-q τ_{a+b}}; τ_{a+b} < ∞] = E[e^{-q τ_a}; τ_a < ∞] E[e^{-q τ_b}; τ_b < ∞]`. -/
theorem laplace_mult {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω in {ω | ∃ t, a + b < X t ω}, expPass X q (a + b) ω ∂P =
      (∫⁻ ω in {ω | ∃ t, a < X t ω}, expPass X q a ω ∂P) *
        ∫⁻ ω in {ω | ∃ t, b < X t ω}, expPass X q b ω ∂P := by
  have hXL := hX.isSNLevy
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hXL.measurable u
  have hE : ∀ c, {ω | ∃ t, c < X t ω} = {ω | (fun u => X u ω) ∈ exceedSet c} := by
    intro c
    ext ω
    exact (mem_exceedSet_iff _ (hXL.right_continuous ω) c).symm
  have hEm : ∀ c, MeasurableSet {ω | ∃ t, c < X t ω} := fun c => by
    rw [hE c]
    exact hXp (measurableSet_exceedSet c)
  set A : ℕ → Set Ω := fun n => {ω | hitT X a (n : ℝ≥0) ω < (n : ℝ≥0)} with hAdef
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    𝓕.le _ _ (measurableSet_hitT_lt 𝓕 hX a (n : ℝ≥0) (n : ℝ≥0))
  have hAst : ∀ n (t : ℝ≥0), MeasurableSet[𝓕 t] (A n ∩ {ω | hitT X a (n : ℝ≥0) ω ≤ t}) := by
    intro n t
    by_cases ht : (n : ℝ≥0) ≤ t
    · exact (𝓕.mono ht _ (measurableSet_hitT_lt 𝓕 hX a (n : ℝ≥0) (n : ℝ≥0))).inter
        (measurableSet_hitT_le 𝓕 hX a _ t)
    · push_neg at ht
      have heq : A n ∩ {ω | hitT X a (n : ℝ≥0) ω ≤ t} = {ω | hitT X a (n : ℝ≥0) ω ≤ t} := by
        ext ω
        exact ⟨fun h => h.2, fun h => ⟨lt_of_le_of_lt h ht, h⟩⟩
      rw [heq]
      exact measurableSet_hitT_le 𝓕 hX a _ t
  have hgX : ∫⁻ ω, gQ q b (fun u => X u ω) ∂P = ∫⁻ ω in {ω | ∃ t, b < X t ω}, expPass X q b ω ∂P := by
    rw [← lintegral_indicator (hEm b)]
    congr 1
    funext ω
    by_cases h : ∃ t, b < X t ω
    · have h' : (fun u => X u ω) ∈ exceedSet b :=
        (mem_exceedSet_iff _ (hXL.right_continuous ω) b).mpr h
      rw [gQ, Set.indicator_of_mem h', Set.indicator_of_mem (show ω ∈ {ω | ∃ t, b < X t ω} from h),
        expPass, pass_eq_passQ hXL]
    · have h' : (fun u => X u ω) ∉ exceedSet b := fun h' =>
        h ((mem_exceedSet_iff _ (hXL.right_continuous ω) b).mp h')
      rw [gQ, Set.indicator_of_notMem h',
        Set.indicator_of_notMem (show ω ∉ {ω | ∃ t, b < X t ω} from h)]
  have hstep : ∀ n, ∫⁻ ω in A n ∩ {ω | ∃ t, a + b < X t ω}, expPass X q (a + b) ω ∂P =
      (∫⁻ ω in A n, expPass X q a ω ∂P) * ∫⁻ ω in {ω | ∃ t, b < X t ω}, expPass X q b ω ∂P := by
    intro n
    have hτ := measurable_hitT 𝓕 hX a (n : ℝ≥0)
    have hZ := measurable_post hXL _ hτ
    have hF : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
        ENNReal.ofReal (Real.exp (-(q * (z.1 : ℝ)))) * gQ q b z.2) :=
      ((measurable_kq q).comp measurable_fst).mul ((measurable_gQ q b).comp measurable_snd)
    calc ∫⁻ ω in A n ∩ {ω | ∃ t, a + b < X t ω}, expPass X q (a + b) ω ∂P
        = ∫⁻ ω in A n, {ω | ∃ t, a + b < X t ω}.indicator (expPass X q (a + b)) ω ∂P := by
          rw [Set.inter_comm, ← Measure.restrict_restrict (hEm _), lintegral_indicator (hEm _)]
      _ = ∫⁻ ω in A n, ENNReal.ofReal (Real.exp (-(q * (hitT X a (n : ℝ≥0) ω : ℝ)))) *
            gQ q b (fun u => X (hitT X a (n : ℝ≥0) ω + u) ω - X (hitT X a (n : ℝ≥0) ω) ω) ∂P :=
          setLIntegral_congr_fun (hAm n) (fun ω hω => key_point hXL ha hb q _ ω hω)
      _ = ∫⁻ z, ENNReal.ofReal (Real.exp (-(q * (z.1 : ℝ)))) * gQ q b z.2
            ∂((P.restrict (A n)).map (fun ω => (hitT X a (n : ℝ≥0) ω,
              fun u => X (hitT X a (n : ℝ≥0) ω + u) ω - X (hitT X a (n : ℝ≥0) ω) ω))) := by
          rw [lintegral_map hF (hτ.prodMk hZ)]
      _ = ∫⁻ z, ENNReal.ofReal (Real.exp (-(q * (z.1 : ℝ)))) * gQ q b z.2
            ∂(((P.restrict (A n)).map (hitT X a (n : ℝ≥0))).prod
              (P.map (fun ω (u : ℝ≥0) => X u ω))) := by
          rw [strongMarkov_joint 𝓕 P X hX _ hτ (A n) (hAm n) (hAst n)]
      _ = (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * (s : ℝ)))) ∂((P.restrict (A n)).map
              (hitT X a (n : ℝ≥0)))) * ∫⁻ f, gQ q b f ∂(P.map (fun ω (u : ℝ≥0) => X u ω)) :=
          lintegral_prod_mul (measurable_kq q).aemeasurable (measurable_gQ q b).aemeasurable
      _ = (∫⁻ ω in A n, ENNReal.ofReal (Real.exp (-(q * (hitT X a (n : ℝ≥0) ω : ℝ)))) ∂P) *
            ∫⁻ ω, gQ q b (fun u => X u ω) ∂P := by
          rw [lintegral_map (measurable_kq q) hτ, lintegral_map (measurable_gQ q b) hXp]
      _ = (∫⁻ ω in A n, expPass X q a ω ∂P) *
            ∫⁻ ω in {ω | ∃ t, b < X t ω}, expPass X q b ω ∂P := by
          rw [hgX]
          congr 1
          refine setLIntegral_congr_fun (hAm n) (fun ω hω => ?_)
          rw [expPass, hitT_eq X a _ ω ((mem_A_iff X a _ ω).mp hω)]
          rfl
  have hAmono : Monotone A := by
    intro i j hij ω hω
    simp only [hAdef, Set.mem_setOf_eq, mem_A_iff] at hω ⊢
    obtain ⟨t, ht, ht'⟩ := hω
    exact ⟨t, lt_of_lt_of_le ht (by exact_mod_cast hij), ht'⟩
  have hAU : ⋃ n, A n = {ω | ∃ t, a < X t ω} := by
    ext ω
    simp only [hAdef, Set.mem_iUnion, Set.mem_setOf_eq, mem_A_iff]
    constructor
    · rintro ⟨n, t, -, ht⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      obtain ⟨n, hn⟩ := exists_nat_gt t
      exact ⟨n, t, hn, ht⟩
  have hsub : {ω | ∃ t, a + b < X t ω} ⊆ {ω | ∃ t, a < X t ω} := by
    rintro ω ⟨t, ht⟩
    exact ⟨t, by linarith⟩
  have hfin : ∫⁻ ω in {ω | ∃ t, b < X t ω}, expPass X q b ω ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (measure_ne_top P {ω | ∃ t, b < X t ω}) ?_
    calc ∫⁻ ω in {ω | ∃ t, b < X t ω}, expPass X q b ω ∂P
        ≤ ∫⁻ ω in {ω | ∃ t, b < X t ω}, 1 ∂P := by
          refine lintegral_mono fun ω => ?_
          exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr
            (neg_nonpos.mpr (mul_nonneg hq (NNReal.coe_nonneg _))))
      _ = P {ω | ∃ t, b < X t ω} := by rw [setLIntegral_const, one_mul]
  have hlim1 : Filter.Tendsto
      (fun n => ∫⁻ ω in A n ∩ {ω | ∃ t, a + b < X t ω}, expPass X q (a + b) ω ∂P) Filter.atTop
      (𝓝 (∫⁻ ω in {ω | ∃ t, a + b < X t ω}, expPass X q (a + b) ω ∂P)) := by
    have hmono : Monotone fun n => A n ∩ {ω | ∃ t, a + b < X t ω} :=
      fun i j hij => Set.inter_subset_inter_left _ (hAmono hij)
    have h := tendsto_measure_iUnion_atTop (μ := P.withDensity (expPass X q (a + b))) hmono
    rw [← Set.iUnion_inter, hAU, Set.inter_eq_right.mpr hsub, withDensity_apply _ (hEm _)] at h
    exact h.congr fun n => withDensity_apply _ ((hAm n).inter (hEm _))
  have hlim2 : Filter.Tendsto (fun n => (∫⁻ ω in A n, expPass X q a ω ∂P) *
      ∫⁻ ω in {ω | ∃ t, b < X t ω}, expPass X q b ω ∂P) Filter.atTop
      (𝓝 ((∫⁻ ω in {ω | ∃ t, a < X t ω}, expPass X q a ω ∂P) *
        ∫⁻ ω in {ω | ∃ t, b < X t ω}, expPass X q b ω ∂P)) := by
    have h := tendsto_measure_iUnion_atTop (μ := P.withDensity (expPass X q a)) hAmono
    rw [hAU, withDensity_apply _ (hEm _)] at h
    exact ENNReal.Tendsto.mul_const (h.congr fun n => withDensity_apply _ (hAm n)) (Or.inr hfin)
  simp_rw [hstep] at hlim1
  exact tendsto_nhds_unique hlim1 hlim2

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40


/-- Cauchy's multiplicative equation on `[0, ∞)` for a positive function bounded by `1`. -/
lemma cauchy_real (g : ℝ → ℝ) (hmul : ∀ a b, 0 ≤ a → 0 ≤ b → g (a + b) = g a * g b)
    (hle : ∀ a, 0 ≤ a → g a ≤ 1) (hpos : ∀ a, 0 ≤ a → 0 < g a) :
    ∀ a, 0 ≤ a → g a = g 1 ^ a := by
  have h0 : g 0 = 1 := by
    have h := hmul 0 0 le_rfl le_rfl
    rw [add_zero] at h
    exact mul_left_cancel₀ (hpos 0 le_rfl).ne' (h.symm.trans (mul_one _).symm)
  have hanti : ∀ a b, 0 ≤ a → a ≤ b → g b ≤ g a := by
    intro a b ha hab
    have h := hmul a (b - a) ha (by linarith)
    rw [show a + (b - a) = b by ring] at h
    rw [h]
    exact mul_le_of_le_one_right (hpos a ha).le (hle _ (by linarith))
  have hpow : ∀ a, 0 ≤ a → ∀ n : ℕ, g (n * a) = g a ^ n := by
    intro a ha n
    induction n with
    | zero => simp [h0]
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hmul _ _ (by positivity) ha, ih, pow_succ]
  have hx : 0 < g 1 := hpos 1 zero_le_one
  have hrat : ∀ m n : ℕ, 0 < n → g (m / n) = g 1 ^ ((m : ℝ) / n) := by
    intro m n hn
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have h1 : g (m / n) ^ n = g 1 ^ m := by
      rw [← hpow _ (by positivity) n, mul_div_cancel₀ _ hnR.ne']
      have h := hpow 1 zero_le_one m
      rwa [mul_one] at h
    have hgpos := hpos (m / n) (by positivity)
    calc g (m / n) = (g (m / n) ^ n) ^ ((n : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast hgpos.le hn.ne').symm
      _ = (g 1 ^ m) ^ ((n : ℝ)⁻¹) := by rw [h1]
      _ = g 1 ^ ((m : ℝ) / n) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, div_eq_mul_inv]
  have hcont : Continuous (fun p : ℝ => g 1 ^ p) := Real.continuous_const_rpow hx.ne'
  have hgrid : ∀ u v : ℝ, 0 ≤ u → u < v →
      ∃ m n : ℕ, 0 < n ∧ u < (m : ℝ) / n ∧ (m : ℝ) / n < v := by
    intro u v hu huv
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr huv)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : 1 < (v - u) * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ hn1] at hn
      linarith
    have hfl := Nat.lt_floor_add_one (u * ((n : ℝ) + 1))
    have hfl2 := Nat.floor_le (by positivity : 0 ≤ u * ((n : ℝ) + 1))
    refine ⟨⌊u * ((n : ℝ) + 1)⌋₊ + 1, n + 1, n.succ_pos, ?_, ?_⟩
    · rw [lt_div_iff₀ (by exact_mod_cast n.succ_pos)]
      push_cast
      linarith
    · rw [div_lt_iff₀ (by exact_mod_cast n.succ_pos)]
      push_cast
      nlinarith
  intro a ha
  rcases ha.eq_or_lt with rfl | ha'
  · rw [h0, Real.rpow_zero]
  apply le_antisymm
  · by_contra hcon
    push Not at hcon
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.continuousAt_iff.mp hcont.continuousAt (g a - g 1 ^ a) (by linarith)
    obtain ⟨m, n, hn, h1, h2⟩ :=
      hgrid (max 0 (a - δ)) a (le_max_left _ _) (max_lt ha' (by linarith))
    have hp0 : 0 ≤ (m : ℝ) / n := by positivity
    have hd : dist ((m : ℝ) / n) a < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right 0 (a - δ)]
    have hb := hball hd
    rw [Real.dist_eq, abs_lt] at hb
    have hge := hanti _ _ hp0 h2.le
    rw [hrat m n hn] at hge
    linarith [hb.2]
  · by_contra hcon
    push Not at hcon
    obtain ⟨δ, hδ, hball⟩ :=
      Metric.continuousAt_iff.mp hcont.continuousAt (g 1 ^ a - g a) (by linarith)
    obtain ⟨m, n, hn, h1, h2⟩ := hgrid a (a + δ) ha (by linarith)
    have hd : dist ((m : ℝ) / n) a < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hb := hball hd
    rw [Real.dist_eq, abs_lt] at hb
    have hle' := hanti a _ ha h1.le
    rw [hrat m n hn] at hle'
    linarith [hb.1]

/-- Cauchy's multiplicative equation in `ℝ≥0∞` for a function bounded by `1`:
`f a = f 1 ^ a` for every `a > 0` (the degenerate case `f 1 = 0` included). -/
lemma cauchy_ennreal (f : ℝ → ℝ≥0∞) (hmul : ∀ a b, 0 ≤ a → 0 ≤ b → f (a + b) = f a * f b)
    (hle : ∀ a, 0 ≤ a → f a ≤ 1) : ∀ a, 0 < a → f a = f 1 ^ a := by
  have hanti : ∀ a b, 0 ≤ a → a ≤ b → f b ≤ f a := by
    intro a b ha hab
    have h := hmul a (b - a) ha (by linarith)
    rw [show a + (b - a) = b by ring] at h
    rw [h]
    calc f a * f (b - a) ≤ f a * 1 := by gcongr; exact hle _ (by linarith)
      _ = f a := mul_one _
  have hpow : ∀ a, 0 ≤ a → ∀ n : ℕ, f (((n + 1 : ℕ) : ℝ) * a) = f a ^ (n + 1) := by
    intro a ha n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [show (((k + 1 + 1 : ℕ) : ℝ)) * a = ((k + 1 : ℕ) : ℝ) * a + a by push_cast; ring,
        hmul _ _ (by positivity) ha, ih]
      ring
  have hfin : ∀ a, 0 ≤ a → f a ≠ ⊤ := fun a ha =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hle a ha)
  by_cases h1 : f 1 = 0
  · intro a ha
    rw [h1, ENNReal.zero_rpow_of_pos ha]
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ha
    have hz : f (1 / ((n : ℝ) + 1)) = 0 := by
      have h := hpow (1 / ((n : ℝ) + 1)) (by positivity) n
      rw [show (((n + 1 : ℕ) : ℝ)) * (1 / ((n : ℝ) + 1)) = 1 by push_cast; field_simp, h1] at h
      exact (pow_eq_zero_iff n.succ_ne_zero).mp h.symm
    exact le_antisymm (hz ▸ hanti _ _ (by positivity) hn.le) (by simp)
  · have hpos : ∀ a, 0 ≤ a → 0 < f a := by
      intro a ha
      obtain ⟨n, hn⟩ := exists_nat_ge a
      have h := hpow (a / ((n : ℝ) + 1)) (by positivity) n
      rw [show (((n + 1 : ℕ) : ℝ)) * (a / ((n : ℝ) + 1)) = a by push_cast; field_simp] at h
      rw [h]
      have hle1 : a / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      exact pos_iff_ne_zero.mpr (pow_ne_zero _
        (lt_of_lt_of_le (pos_iff_ne_zero.mpr h1) (hanti _ _ (by positivity) hle1)).ne')
    have hg : ∀ a, 0 ≤ a → (f a).toReal = (f 1).toReal ^ a :=
      cauchy_real (fun a => (f a).toReal)
        (fun a b ha hb => by rw [hmul a b ha hb, ENNReal.toReal_mul])
        (fun a ha => ENNReal.toReal_le_of_le_ofReal zero_le_one
          (by rw [ENNReal.ofReal_one]; exact hle a ha))
        (fun a ha => ENNReal.toReal_pos (hpos a ha).ne' (hfin a ha))
    intro a ha
    calc f a = ENNReal.ofReal (f a).toReal := (ENNReal.ofReal_toReal (hfin a ha.le)).symm
      _ = ENNReal.ofReal ((f 1).toReal ^ a) := by rw [hg a ha.le]
      _ = ENNReal.ofReal (f 1).toReal ^ a :=
          (ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ha.le).symm
      _ = f 1 ^ a := by rw [ENNReal.ofReal_toReal (hfin 1 zero_le_one)]


lemma setLIntegral_expPass_le_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) {q : ℝ} (hq : 0 ≤ q) (c : ℝ) (S : Set Ω) :
    ∫⁻ ω in S, expPass X q c ω ∂P ≤ 1 := by
  calc ∫⁻ ω in S, expPass X q c ω ∂P ≤ ∫⁻ _ in S, 1 ∂P := by
        refine lintegral_mono fun ω => ?_
        refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr ?_)
        have := mul_nonneg hq (NNReal.coe_nonneg (pass X c ω))
        linarith
    _ = P S := by rw [lintegral_one, Measure.restrict_apply_univ]
    _ ≤ 1 := prob_le_one

/-- G0.3b: `E[e^{-q τ_a}; τ_a < ∞] = (E[e^{-q τ_1}; τ_1 < ∞]) ^ a` for every level `a > 0`. -/
theorem laplace_rpow {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 ≤ q) {a : ℝ} (ha : 0 < a) :
    ∫⁻ ω in {ω | ∃ t, a < X t ω}, expPass X q a ω ∂P =
      (∫⁻ ω in {ω | ∃ t, 1 < X t ω}, expPass X q 1 ω ∂P) ^ a :=
  cauchy_ennreal (fun c => ∫⁻ ω in {ω | ∃ t, c < X t ω}, expPass X q c ω ∂P)
    (fun _ _ ha hb => laplace_mult 𝓕 P X hX ha hb hq)
    (fun c _ => setLIntegral_expPass_le_one P X hq c _) a ha

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- W1: a process with right-continuous paths and measurable sections is jointly measurable. -/
theorem measurable_joint_of_rc {Ω β : Type*} [MeasurableSpace Ω] [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (Y : ℝ≥0 → Ω → β) (hm : ∀ t, Measurable (Y t))
    (hrc : ∀ ω t, ContinuousWithinAt (fun r => Y r ω) (Set.Ici t) t) :
    Measurable (fun p : ℝ≥0 × Ω => Y p.1 p.2) := by
  have happ : ∀ n : ℕ, Measurable (fun p : ℝ≥0 × Ω => Y (dyad n Prod.fst p) p.2) := by
    intro n
    have hk : Measurable (fun p : ℝ≥0 × Ω => ⌈p.1 * 2 ^ n⌉₊) :=
      Nat.measurable_ceil.comp (measurable_fst.mul_const _)
    have hF : Measurable (fun z : ℕ × Ω => Y ((z.1 : ℝ≥0) / 2 ^ n) z.2) :=
      measurable_from_prod_countable_right fun j => by dsimp only; exact hm _
    exact hF.comp (hk.prodMk measurable_snd)
  refine measurable_of_tendsto_metrizable happ (tendsto_pi_nhds.2 fun p => ?_)
  exact (hrc p.2 p.1).tendsto.comp (tendsto_dyad Prod.fst p)

/-- `e^{-θ (f u - f s)}`. -/
noncomputable def rterm (θ : ℝ) (s u : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(θ * (f u - f s))))

/-- `e^{-θ R_s(f)}` with `R_s(f) = sup_{u ≤ s} f u - f s` (the reflected path). -/
noncomputable def rexpP (θ : ℝ) (s : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ u : Set.Iic s, rterm θ s u f

/-- The same functional read off rational times (measurable on path space). -/
noncomputable def rexpQ (θ : ℝ) (s : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  min 1 (⨅ r : {r : ℚ // Real.toNNReal r ≤ s}, rterm θ s (Real.toNNReal r) f)

lemma rterm_self (θ : ℝ) (s : ℝ≥0) (f : ℝ≥0 → ℝ) : rterm θ s s f = 1 := by
  simp [rterm]

lemma measurable_rterm (θ : ℝ) (s u : ℝ≥0) : Measurable (rterm θ s u) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.mul ((measurable_pi_apply u).sub (measurable_pi_apply s))).neg))

lemma measurable_rexpQ (θ : ℝ) (s : ℝ≥0) : Measurable (rexpQ θ s) :=
  measurable_const.min (Measurable.iInf fun _ => measurable_rterm θ s _)

lemma rexpP_le_one (θ : ℝ) (s : ℝ≥0) (f : ℝ≥0 → ℝ) : rexpP θ s f ≤ 1 :=
  (iInf_le _ ⟨s, Set.mem_Iic.mpr le_rfl⟩).trans (rterm_self θ s f).le

lemma rexpP_eq_rexpQ (θ : ℝ) (s : ℝ≥0) (f : ℝ≥0 → ℝ)
    (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t) : rexpP θ s f = rexpQ θ s f := by
  apply le_antisymm
  · exact le_min (rexpP_le_one θ s f) (le_iInf fun r => iInf_le (fun u : Set.Iic s => rterm θ s u f) ⟨Real.toNNReal r, r.2⟩)
  · refine le_iInf fun u => ?_
    rcases (Set.mem_Iic.mp u.2).eq_or_lt with h | h
    · rw [h, rterm_self]; exact min_le_left _ _
    · by_contra hcon
      push Not at hcon
      have hfin : rexpQ θ s f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
      have hlt : Real.exp (-(θ * (f u - f s))) < (rexpQ θ s f).toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos _).le hfin).mp hcon
      have hrc' : ∀ t, ContinuousWithinAt (fun v => -Real.exp (-(θ * (f v - f s))))
          (Set.Ici t) t := fun t =>
        (((continuousWithinAt_const.mul ((hrc t).sub continuousWithinAt_const)).neg).rexp).neg
      obtain ⟨r, hrs, hr⟩ := exists_rat_hit _ hrc' (a := -(rexpQ θ s f).toReal)
        ⟨u, h, by linarith⟩
      have h1 : rexpQ θ s f ≤ rterm θ s (Real.toNNReal r) f :=
        (min_le_right _ _).trans (iInf_le (fun r : {r : ℚ // Real.toNNReal r ≤ s} =>
          rterm θ s (Real.toNNReal r) f) ⟨r, hrs.le⟩)
      have h2 : rterm θ s (Real.toNNReal r) f < rexpQ θ s f := by
        unfold rterm
        rw [ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos _).le hfin]
        linarith
      exact absurd h1 (not_le.mpr h2)

/-- `e^{-θ R_v}` is right-continuous in `v` along a right-continuous path. -/
theorem rexpP_rc (θ : ℝ) (f : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (v : ℝ≥0) : ContinuousWithinAt (fun w => rexpP θ w f) (Set.Ici v) v := by
  set g : ℝ≥0 → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-(θ * f u))) with hg
  set A : ℝ≥0 → ℝ≥0∞ := fun w => ENNReal.ofReal (Real.exp (θ * f w)) with hA
  set B : ℝ≥0 → ℝ≥0∞ := fun w => ⨅ u : Set.Iic w, g u with hB
  have hsplit : ∀ w, rexpP θ w f = A w * B w := by
    intro w
    rw [hB, ENNReal.mul_iInf_of_ne (by simp [hA, Real.exp_pos]) ENNReal.ofReal_ne_top]
    refine iInf_congr fun u => ?_
    simp only [rterm, hA, hg]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hAc : ContinuousWithinAt A (Set.Ici v) v :=
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_const.mul (hrc v)).rexp)
  have hgc : ContinuousWithinAt g (Set.Ici v) v :=
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      ((continuousWithinAt_const.mul (hrc v)).neg.rexp)
  have hBle : ∀ w, v ≤ w → B w ≤ B v := fun w hw =>
    le_iInf fun u => iInf_le (fun u : Set.Iic w => g u) ⟨u, le_trans (Set.mem_Iic.mp u.2) hw⟩
  have hBv : B v ≤ g v := iInf_le (fun u : Set.Iic v => g u) ⟨v, Set.mem_Iic.mpr le_rfl⟩
  have hBc : ContinuousWithinAt B (Set.Ici v) v := by
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨b', hb1, hb2⟩ := exists_between hb
      have hev : ∀ᶠ u in 𝓝[≥] v, b' < g u :=
        hgc.eventually (lt_mem_nhds (lt_of_lt_of_le hb2 hBv))
      obtain ⟨w, hw, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
      have hmem : Set.Ico v w ∈ 𝓝[≥] v := Ico_mem_nhdsGE hw
      filter_upwards [hmem] with w' hw'
      refine lt_of_lt_of_le hb1 (le_iInf fun u => ?_)
      by_cases huv : (u : ℝ≥0) ≤ v
      · exact le_trans hb2.le (iInf_le (fun u : Set.Iic v => g u) ⟨u, huv⟩)
      · exact (hsub ⟨(not_le.mp huv).le, lt_of_le_of_lt (Set.mem_Iic.mp u.2) hw'.2⟩).le
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact lt_of_le_of_lt (hBle w hw) hb
  have hB1 : B v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBv
  have h := ENNReal.Tendsto.mul hAc (Or.inr hB1) hBc (Or.inr ENNReal.ofReal_ne_top)
  simp only [ContinuousWithinAt]
  simp_rw [hsplit]
  exact h

/-- The jointly measurable version `limsup_n rexpQ θ (dyad n τ z) (π z)`. -/
noncomputable def rexpJ (θ : ℝ) {α : Type*} (τ : α → ℝ≥0) (π : α → ℝ≥0 → ℝ) (z : α) : ℝ≥0∞ :=
  limsup (fun n => rexpQ θ (dyad n τ z) (π z)) atTop

lemma measurable_rexpJ (θ : ℝ) {α : Type*} [MeasurableSpace α] {τ : α → ℝ≥0}
    {π : α → ℝ≥0 → ℝ} (hτ : Measurable τ) (hπ : Measurable π) : Measurable (rexpJ θ τ π) := by
  show Measurable (fun z => limsup (fun n => rexpQ θ (dyad n τ z) (π z)) atTop)
  refine Measurable.limsup (f := fun n z => rexpQ θ (dyad n τ z) (π z)) fun n => ?_
  have hk : Measurable (fun z => ⌈τ z * 2 ^ n⌉₊) := Nat.measurable_ceil.comp (hτ.mul_const _)
  have hF : Measurable (fun p : ℕ × (ℝ≥0 → ℝ) => rexpQ θ ((p.1 : ℝ≥0) / 2 ^ n) p.2) :=
    measurable_from_prod_countable_right fun j => by dsimp only; exact measurable_rexpQ θ _
  have heq : (fun z => rexpQ θ (dyad n τ z) (π z)) =
      (fun p : ℕ × (ℝ≥0 → ℝ) => rexpQ θ ((p.1 : ℝ≥0) / 2 ^ n) p.2) ∘
        (fun z => (⌈τ z * 2 ^ n⌉₊, π z)) := by
    funext z; simp only [Function.comp, dyad]
  rw [heq]
  exact hF.comp (hk.prodMk hπ)

lemma rexpJ_eq (θ : ℝ) {α : Type*} (τ : α → ℝ≥0) (π : α → ℝ≥0 → ℝ) (z : α)
    (hrc : ∀ t, ContinuousWithinAt (π z) (Set.Ici t) t) :
    rexpJ θ τ π z = rexpP θ (τ z) (π z) := by
  have h : Tendsto (fun n => rexpQ θ (dyad n τ z) (π z)) atTop (𝓝 (rexpP θ (τ z) (π z))) := by
    have h1 := (rexpP_rc θ (π z) hrc (τ z)).tendsto.comp (tendsto_dyad τ z)
    refine h1.congr fun n => ?_
    exact rexpP_eq_rexpQ θ _ (π z) hrc
  exact h.limsup_eq

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

/-- Path identity: if `f ≤ f τ` before `τ ≤ t`, the reflected functional at `t` is that of the
post-`τ` path at `t - τ`. -/
lemma rexp_split {f : ℝ≥0 → ℝ} {τ t : ℝ≥0} {θ : ℝ} (hθ : 0 ≤ θ) (hτt : τ ≤ t)
    (hbefore : ∀ u, u < τ → f u ≤ f τ) :
    rexpP θ t f = rexpP θ (t - τ) (fun v => f (τ + v) - f τ) := by
  have hterm : ∀ v, rterm θ (t - τ) v (fun v => f (τ + v) - f τ) = rterm θ t (τ + v) f := by
    intro v
    simp only [rterm]
    rw [add_tsub_cancel_of_le hτt]
    congr 3
    ring
  apply le_antisymm
  · refine le_iInf fun v => ?_
    rw [hterm]
    have hv : τ + (v : ℝ≥0) ≤ t := by
      have h1 := add_le_add (le_refl τ) (Set.mem_Iic.mp v.2)
      rwa [add_tsub_cancel_of_le hτt] at h1
    exact iInf_le (fun u : Set.Iic t => rterm θ t u f) ⟨τ + v, hv⟩
  · refine le_iInf fun u => ?_
    by_cases hu : τ ≤ (u : ℝ≥0)
    · have hv : (u : ℝ≥0) - τ ≤ t - τ := tsub_le_tsub_right (Set.mem_Iic.mp u.2) τ
      calc rexpP θ (t - τ) (fun v => f (τ + v) - f τ)
          ≤ rterm θ (t - τ) ((u : ℝ≥0) - τ) (fun v => f (τ + v) - f τ) :=
            iInf_le (fun v : Set.Iic (t - τ) => rterm θ (t - τ) v _) ⟨_, hv⟩
        _ = rterm θ t u f := by rw [hterm, add_tsub_cancel_of_le hu]
    · push Not at hu
      calc rexpP θ (t - τ) (fun v => f (τ + v) - f τ)
          ≤ rterm θ (t - τ) 0 (fun v => f (τ + v) - f τ) :=
            iInf_le (fun v : Set.Iic (t - τ) => rterm θ (t - τ) v _) ⟨0, by simp⟩
        _ = rterm θ t τ f := by rw [hterm, add_zero]
        _ ≤ rterm θ t u f := by
          unfold rterm
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have h1 := mul_le_mul_of_nonneg_left (hbefore u hu) hθ
          linarith

/-- W3 (Wiener-Hopf splitting at a fixed time): on `{τ_x < t}` the reflected functional
`e^{-θ R_t}` factorises through the strong Markov property at the first passage `τ_x`. -/
theorem wh_split {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {x θ : ℝ} (hx : 0 ≤ x) (hθ : 0 ≤ θ) {t T : ℝ≥0} (htT : t ≤ T) :
    ∫⁻ ω in {ω | hitT X x T ω < t}, rexpP θ t (fun u => X u ω) ∂P =
      ∫⁻ ω in {ω | hitT X x T ω < t},
        (∫⁻ ω', rexpP θ (t - hitT X x T ω) (fun u => X u ω') ∂P) ∂P := by
  have hXL := hX.isSNLevy
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hXL.measurable u
  have hτ : Measurable (hitT X x T) := measurable_hitT 𝓕 hX x T
  have hZ := measurable_post hXL _ hτ
  have hAm : MeasurableSet {ω | hitT X x T ω < t} :=
    𝓕.le _ _ (measurableSet_hitT_lt 𝓕 hX x T t)
  have hAst : ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
      ({ω | hitT X x T ω < t} ∩ {ω | hitT X x T ω ≤ s}) := by
    intro s
    by_cases hs : t ≤ s
    · exact (𝓕.mono hs _ (measurableSet_hitT_lt 𝓕 hX x T t)).inter
        (measurableSet_hitT_le 𝓕 hX x T s)
    · push Not at hs
      have heq : {ω | hitT X x T ω < t} ∩ {ω | hitT X x T ω ≤ s} = {ω | hitT X x T ω ≤ s} := by
        ext ω
        exact ⟨fun h => h.2, fun h => ⟨lt_of_le_of_lt h hs, h⟩⟩
      rw [heq]
      exact measurableSet_hitT_le 𝓕 hX x T s
  have hGm : Measurable (rexpJ θ (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => t - z.1) Prod.snd) :=
    measurable_rexpJ θ (measurable_const.sub measurable_fst) measurable_snd
  have hpath : ∀ ω ∈ {ω | hitT X x T ω < t}, rexpP θ t (fun u => X u ω) =
      rexpJ θ (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => t - z.1) Prod.snd
        (hitT X x T ω, fun u => X (hitT X x T ω + u) ω - X (hitT X x T ω) ω) := by
    intro ω hω
    have hω' : hitT X x T ω < t := hω
    have hex : ∃ u, u < T ∧ x < X u ω := by
      rcases (hitT_lt_iff X x T ω t).mp hω' with h | ⟨u, hu, hxu⟩
      · exact absurd htT (not_le.mpr h)
      · exact ⟨u, lt_of_lt_of_le hu htT, hxu⟩
    have hcr := creep_hitT hXL hx T ω hex
    rw [rexpJ_eq θ _ _ _ (post_rc hXL _ ω)]
    refine rexp_split hθ hω'.le fun u hu => ?_
    rw [hcr]
    exact le_of_lt_hitT X x T ω u hu
  calc ∫⁻ ω in {ω | hitT X x T ω < t}, rexpP θ t (fun u => X u ω) ∂P
      = ∫⁻ ω in {ω | hitT X x T ω < t}, rexpJ θ (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => t - z.1) Prod.snd
          (hitT X x T ω, fun u => X (hitT X x T ω + u) ω - X (hitT X x T ω) ω) ∂P :=
        setLIntegral_congr_fun hAm hpath
    _ = ∫⁻ z, rexpJ θ (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => t - z.1) Prod.snd z
          ∂((P.restrict {ω | hitT X x T ω < t}).map
            (fun ω => (hitT X x T ω, fun u => X (hitT X x T ω + u) ω - X (hitT X x T ω) ω))) := by
        rw [lintegral_map hGm (hτ.prodMk hZ)]
    _ = ∫⁻ z, rexpJ θ (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => t - z.1) Prod.snd z
          ∂(((P.restrict {ω | hitT X x T ω < t}).map (hitT X x T)).prod
            (P.map (fun ω (u : ℝ≥0) => X u ω))) := by
        rw [strongMarkov_joint 𝓕 P X hX _ hτ _ hAm hAst]
    _ = ∫⁻ s, ∫⁻ f, rexpJ θ (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => t - z.1) Prod.snd (s, f)
          ∂(P.map (fun ω (u : ℝ≥0) => X u ω))
          ∂((P.restrict {ω | hitT X x T ω < t}).map (hitT X x T)) :=
        lintegral_prod _ hGm.aemeasurable
    _ = ∫⁻ ω in {ω | hitT X x T ω < t}, ∫⁻ f, rexpJ θ (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => t - z.1)
          Prod.snd (hitT X x T ω, f) ∂(P.map (fun ω (u : ℝ≥0) => X u ω)) ∂P :=
        lintegral_map hGm.lintegral_prod_right' hτ
    _ = ∫⁻ ω in {ω | hitT X x T ω < t},
          (∫⁻ ω', rexpP θ (t - hitT X x T ω) (fun u => X u ω') ∂P) ∂P := by
        refine lintegral_congr fun ω => ?_
        have hmf : Measurable (fun f : ℝ≥0 → ℝ => rexpJ θ (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => t - z.1)
            Prod.snd (hitT X x T ω, f)) := hGm.comp measurable_prodMk_left
        rw [lintegral_map hmf hXp]
        exact lintegral_congr fun ω' => rexpJ_eq θ _ _ _ (hXL.right_continuous ω')

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- `s ↦ E[e^{-θ R_s}]` is measurable. -/
lemma measurable_rexpMean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) (θ : ℝ) :
    Measurable (fun s : ℝ≥0 => ∫⁻ ω, rexpP θ s (fun u => X u ω) ∂P) := by
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hX.measurable u
  have hG : Measurable (rexpJ θ (fun z : ℝ≥0 × Ω => z.1) (fun z => fun u => X u z.2)) :=
    measurable_rexpJ θ measurable_fst (hXp.comp measurable_snd)
  have h := hG.lintegral_prod_right' (ν := P)
  have heq : (fun s : ℝ≥0 => ∫⁻ ω, rexpP θ s (fun u => X u ω) ∂P) =
      fun s => ∫⁻ ω, rexpJ θ (fun z : ℝ≥0 × Ω => z.1) (fun z => fun u => X u z.2) (s, ω) ∂P :=
    funext fun s => lintegral_congr fun ω =>
      (rexpJ_eq θ (fun z : ℝ≥0 × Ω => z.1) (fun z => fun u => X u z.2) (s, ω)
        (hX.right_continuous ω)).symm
  rw [heq]
  exact h

lemma measurable_expWeight (q : ℝ) : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)

/-- Shift of the time variable: `∫_{t>p} e^{-qt} F(t-p) dt = e^{-qp} ∫_{s>0} e^{-qs} F(s) ds`. -/
lemma shift_lintegral (F : ℝ≥0 → ℝ≥0∞) (hF : Measurable F) (q : ℝ) (p : ℝ≥0) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) *
        (if p < Real.toNNReal t then F (Real.toNNReal t - p) else 0) =
      ENNReal.ofReal (Real.exp (-(q * p))) *
        ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) * F (Real.toNNReal s) := by
  set g : ℝ → ℝ≥0∞ := (Set.Ioi (p : ℝ)).indicator
    (fun t => ENNReal.ofReal (Real.exp (-(q * t))) * F (Real.toNNReal t - p)) with hg
  have h1 : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) *
        (if p < Real.toNNReal t then F (Real.toNNReal t - p) else 0) = ∫⁻ t, g t := by
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun t => ?_
    simp only [hg, Set.indicator, Set.mem_Ioi]
    by_cases ht : (p : ℝ) < t
    · have ht0 : (0 : ℝ) < t := lt_of_le_of_lt p.2 ht
      have hpt : p < Real.toNNReal t := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht0.le]; exact ht
      simp [ht, ht0, hpt]
    · have hpt : ¬ p < Real.toNNReal t := by
        intro h
        apply ht
        rcases le_or_gt t 0 with h0 | h0
        · rw [Real.toNNReal_of_nonpos h0] at h
          exact absurd h (by simp)
        · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ h0.le] at h
          exact h
      simp [ht, hpt]
  have h2 : ∫⁻ t, g t = ∫⁻ s, g (s + p) := (lintegral_add_right_eq_self g (p : ℝ)).symm
  have h3 : ∀ s, g (s + p) = ENNReal.ofReal (Real.exp (-(q * p))) *
      (Set.Ioi (0 : ℝ)).indicator
        (fun s => ENNReal.ofReal (Real.exp (-(q * s))) * F (Real.toNNReal s)) s := by
    intro s
    simp only [hg, Set.indicator, Set.mem_Ioi]
    by_cases hs : (0 : ℝ) < s
    · have hsp : (p : ℝ) < s + p := by linarith
      have hsub : Real.toNNReal (s + p) - p = Real.toNNReal s := by
        rw [show s + (p : ℝ) = ((Real.toNNReal s + p : ℝ≥0) : ℝ) by
          push_cast [Real.coe_toNNReal _ hs.le]; ring, Real.toNNReal_coe, add_tsub_cancel_right]
      rw [if_pos hsp, if_pos hs, hsub, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      congr 3
      ring
    · have hsp : ¬ (p : ℝ) < s + p := by linarith
      rw [if_neg hsp, if_neg hs, mul_zero]
  rw [h1, h2]
  simp_rw [h3]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Ioi]

/-- W4 (resolvent form of the splitting): `∫ e^{-qt} E[1{τ_x<t} e^{-θR_t}] dt = L_q(x) ∫ e^{-qs} E[e^{-θR_s}] ds`. -/
theorem wh_resolvent {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {x θ : ℝ} (hx : 0 ≤ x) (hθ : 0 ≤ θ) (q : ℝ) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) *
        ∫⁻ ω in {ω | ∃ u, u < Real.toNNReal t ∧ x < X u ω},
          rexpP θ (Real.toNNReal t) (fun u => X u ω) ∂P =
      (∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P) *
        ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) *
          ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P := by
  have hXL := hX.isSNLevy
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hXL.measurable u
  set F : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ ω, rexpP θ s (fun u => X u ω) ∂P with hFdef
  have hF : Measurable F := measurable_rexpMean hXL θ
  have hpm : Measurable (pass X x) := measurable_pass hXL x
  have hEm : MeasurableSet {ω | ∃ u, x < X u ω} := by
    have : {ω | ∃ u, x < X u ω} = {ω | (fun u => X u ω) ∈ exceedSet x} := by
      ext ω
      exact (mem_exceedSet_iff _ (hXL.right_continuous ω) x).symm
    rw [this]
    exact hXp (measurableSet_exceedSet x)
  set k : ℝ → Ω → ℝ≥0∞ := fun t ω =>
    if pass X x ω < Real.toNNReal t then F (Real.toNNReal t - pass X x ω) else 0 with hk
  have hkm : Measurable (Function.uncurry fun t ω => ENNReal.ofReal (Real.exp (-(q * t))) * k t ω) := by
    refine ((measurable_expWeight q).comp measurable_fst).mul ?_
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt (hpm.comp measurable_snd) (measurable_real_toNNReal.comp measurable_fst)
    · exact hF.comp ((measurable_real_toNNReal.comp measurable_fst).sub (hpm.comp measurable_snd))
  have hstep : ∀ t : ℝ, ∫⁻ ω in {ω | ∃ u, u < Real.toNNReal t ∧ x < X u ω},
      rexpP θ (Real.toNNReal t) (fun u => X u ω) ∂P = ∫⁻ ω in {ω | ∃ u, x < X u ω}, k t ω ∂P := by
    intro t
    set t' := Real.toNNReal t
    have hA : {ω | ∃ u, u < t' ∧ x < X u ω} = {ω | hitT X x t' ω < t'} := by
      ext ω
      simp only [Set.mem_setOf_eq, hitT_lt_iff, lt_irrefl, false_or]
    have hAm : MeasurableSet {ω | hitT X x t' ω < t'} :=
      𝓕.le _ _ (measurableSet_hitT_lt 𝓕 hX x t' t')
    rw [hA, wh_split 𝓕 P X hX hx hθ le_rfl, ← lintegral_indicator hAm, ← lintegral_indicator hEm]
    refine lintegral_congr fun ω => ?_
    by_cases hω : hitT X x t' ω < t'
    · have hex : ∃ u, u < t' ∧ x < X u ω := (hitT_lt_iff X x t' ω t').mp hω |>.resolve_left (lt_irrefl _)
      have heq := hitT_eq X x t' ω hex
      obtain ⟨u, hu, hxu⟩ := hex
      have hpass : pass X x ω < t' :=
        lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) hxu) hu
      rw [Set.indicator_of_mem (show ω ∈ {ω | hitT X x t' ω < t'} from hω),
        Set.indicator_of_mem (show ω ∈ {ω | ∃ u, x < X u ω} from ⟨u, hxu⟩)]
      have hp : hitT X x t' ω = pass X x ω := heq
      show F (t' - hitT X x t' ω) = if pass X x ω < t' then F (t' - pass X x ω) else 0
      rw [hp, if_pos (hp ▸ hω)]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | hitT X x t' ω < t'} from hω)]
      by_cases hE : ω ∈ {ω | ∃ u, x < X u ω}
      · rw [Set.indicator_of_mem hE]
        simp only [hk]
        rw [if_neg]
        intro hlt
        apply hω
        obtain ⟨u, hu, hxu⟩ := (csInf_lt_iff (OrderBot.bddBelow _) hE).mp hlt
        exact (hitT_lt_iff X x t' ω t').mpr (Or.inr ⟨u, hxu, hu⟩)
      · rw [Set.indicator_of_notMem hE]
  calc ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) *
        ∫⁻ ω in {ω | ∃ u, u < Real.toNNReal t ∧ x < X u ω},
          rexpP θ (Real.toNNReal t) (fun u => X u ω) ∂P
      = ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ ω in {ω | ∃ u, x < X u ω},
          ENNReal.ofReal (Real.exp (-(q * t))) * k t ω ∂P := by
        refine lintegral_congr fun t => ?_
        rw [hstep t, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ ω in {ω | ∃ u, x < X u ω}, (∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) * k t ω) ∂P :=
        lintegral_lintegral_swap hkm.aemeasurable
    _ = ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω *
          (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) * F (Real.toNNReal s)) ∂P := by
        refine lintegral_congr fun ω => ?_
        exact shift_lintegral F hF q (pass X x ω)
    _ = _ := lintegral_mul_const _ (measurable_expPass hXL q x)

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- W5a: a cadlag path is bounded above on every `[0, t]`. -/
theorem bddAbove_of_cadlag (f : ℝ≥0 → ℝ) (hrc : ∀ s, ContinuousWithinAt f (Set.Ici s) s)
    (hll : ∀ s : ℝ≥0, 0 < s → ∃ l : ℝ, Tendsto f (𝓝[<] s) (𝓝 l)) (t : ℝ≥0) :
    BddAbove (f '' Set.Iic t) := by
  have hloc : ∀ s : ℝ≥0, ∃ C : ℝ, {u | f u < C} ∈ 𝓝 s := by
    intro s
    by_cases hpos' : 0 < s
    swap
    · have h0 : s = 0 := le_antisymm (not_lt.mp hpos') (by simp)
      refine ⟨f s + 1, ?_⟩
      have hR : ∀ᶠ u in 𝓝[≥] s, f u < f s + 1 := (hrc s).eventually (gt_mem_nhds (by linarith))
      have hL : ∀ᶠ u in 𝓝[<] s, f u < f s + 1 := by
        have hE : Set.Iio s = ∅ := by
          rw [h0]; ext u; simp
        rw [hE, nhdsWithin_empty]
        exact Filter.eventually_bot
      rw [← nhdsLT_sup_nhdsGE s]
      exact Filter.mem_sup.mpr ⟨hL, hR⟩
    · obtain ⟨l, hl⟩ := hll s hpos'
      refine ⟨max (f s) l + 1, ?_⟩
      have hR : ∀ᶠ u in 𝓝[≥] s, f u < max (f s) l + 1 :=
        (hrc s).eventually (gt_mem_nhds (by have := le_max_left (f s) l; linarith))
      have hL : ∀ᶠ u in 𝓝[<] s, f u < max (f s) l + 1 :=
        hl.eventually (gt_mem_nhds (by have := le_max_right (f s) l; linarith))
      rw [← nhdsLT_sup_nhdsGE s]
      exact Filter.mem_sup.mpr ⟨hL, hR⟩
  choose C hC using hloc
  have hK : IsCompact (Set.Iic t) := by
    rw [show Set.Iic t = Set.Icc 0 t by ext; simp]
    exact isCompact_Icc
  obtain ⟨T, -, hcov⟩ := hK.elim_nhds_subcover (fun s => {u | f u < C s})
    (fun s _ => hC s)
  refine ⟨∑ s ∈ T, |C s|, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨s, hs, hus⟩ := Set.mem_iUnion₂.mp (hcov hu)
  have h1 : f u < C s := hus
  have h2 : C s ≤ ∑ s ∈ T, |C s| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (C i)) hs)
  linarith

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- No positive jumps: a level `x ≥ 0` exceeded by time `t` is exceeded strictly before `t`. -/
lemma exceed_before (f : ℝ≥0 → ℝ) (h0 : f 0 = 0)
    (hll : ∀ s : ℝ≥0, 0 < s → ∃ l : ℝ, Tendsto f (𝓝[<] s) (𝓝 l))
    (hnj : ∀ s : ℝ≥0, 0 < s → f s ≤ Function.leftLim f s) {x : ℝ} (hx : 0 ≤ x) (t : ℝ≥0) :
    (∃ u, u < t ∧ x < f u) ↔ (∃ u, u ≤ t ∧ x < f u) := by
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu.le, h⟩
  · rintro ⟨u, hu, h⟩
    rcases hu.lt_or_eq with hlt | heq
    · exact ⟨u, hlt, h⟩
    · subst heq
      have hpos : 0 < u := pos_iff_ne_zero.mpr (by rintro rfl; rw [h0] at h; linarith)
      obtain ⟨l, hl⟩ := hll u hpos
      haveI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
      have hL : Function.leftLim f u = l := leftLim_eq_of_tendsto hl
      have hxl : x < l := lt_of_lt_of_le h (hL ▸ hnj u hpos)
      have hev : ∀ᶠ v in 𝓝[<] u, x < f v := hl.eventually (lt_mem_nhds hxl)
      obtain ⟨v, hv1, hv2⟩ := (hev.and eventually_mem_nhdsWithin).exists
      exact ⟨v, hv2, hv1⟩

/-- `e^{-θ R_t} = e^{-θ (S_t - f t)}` with `S_t` the running supremum. -/
lemma rexpP_eq_sup {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ≥0) (f : ℝ≥0 → ℝ)
    (hb : BddAbove (f '' Set.Iic t)) :
    rexpP θ t f = ENNReal.ofReal (Real.exp (-(θ * (sSup (f '' Set.Iic t) - f t)))) := by
  set g : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-(θ * (y - f t)))) with hgdef
  have hg : Antitone g := by
    intro a b hab
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have := mul_le_mul_of_nonneg_left (show a - f t ≤ b - f t by linarith) hθ
    linarith
  have hgc : Continuous g :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_id.sub continuous_const)).neg))
  have hne : (f '' Set.Iic t).Nonempty := ⟨f t, t, Set.mem_Iic.mpr le_rfl, rfl⟩
  show (⨅ u : Set.Iic t, rterm θ t u f) = g (sSup (f '' Set.Iic t))
  rw [Antitone.map_csSup_of_continuousAt hgc.continuousAt hg hne hb, Set.image_image, sInf_image']
  rfl

/-- Layer cake for the exponential: `1 + ∫_0^S θ e^{θx} dx = e^{θS}`. -/
lemma layer_cake_exp {θ : ℝ} (hθ : 0 ≤ θ) {S : ℝ} (hS : 0 ≤ S) :
    1 + ∫⁻ x in Set.Ioi (0 : ℝ),
        (Set.Iio S).indicator (fun x => ENNReal.ofReal (θ * Real.exp (θ * x))) x =
      ENNReal.ofReal (Real.exp (θ * S)) := by
  rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    show Set.Iio S ∩ Set.Ioi 0 = Set.Ioo 0 S by ext; simp [and_comm],
    Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hd : ∀ x ∈ Set.uIcc 0 S, HasDerivAt (fun x => Real.exp (θ * x)) (θ * Real.exp (θ * x)) x := by
    intro x _
    have := ((hasDerivAt_id' x).const_mul θ).exp
    convert this using 1
    ring
  have hcont : Continuous (fun x => θ * Real.exp (θ * x)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hii : IntervalIntegrable (fun x => θ * Real.exp (θ * x)) MeasureTheory.volume 0 S :=
    hcont.intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hii
  rw [intervalIntegral.integral_of_le hS] at hftc
  have hint : IntegrableOn (fun x => θ * Real.exp (θ * x)) (Set.Ioc 0 S) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hS).mp hii
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => mul_nonneg hθ (Real.exp_pos _).le), hftc]
  simp only [mul_zero, Real.exp_zero]
  have h1 : 1 ≤ Real.exp (θ * S) := Real.one_le_exp (mul_nonneg hθ hS)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
  congr 1
  ring

/-- W5b pathwise: `e^{θ f_t} = e^{-θR_t} + ∫_0^∞ θ e^{θx} 1{∃u<t, x<f u} e^{-θR_t} dx`. -/
lemma path_identity (f : ℝ≥0 → ℝ) (h0 : f 0 = 0) (hrc : ∀ s, ContinuousWithinAt f (Set.Ici s) s)
    (hll : ∀ s : ℝ≥0, 0 < s → ∃ l : ℝ, Tendsto f (𝓝[<] s) (𝓝 l))
    (hnj : ∀ s : ℝ≥0, 0 < s → f s ≤ Function.leftLim f s) {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp (θ * f t)) = rexpP θ t f +
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (θ * x)) *
        ({x : ℝ | ∃ u, u < t ∧ x < f u}.indicator (fun _ => rexpP θ t f) x) := by
  have hb := bddAbove_of_cadlag f hrc hll t
  set S := sSup (f '' Set.Iic t) with hSdef
  have hne : (f '' Set.Iic t).Nonempty := ⟨f t, t, Set.mem_Iic.mpr le_rfl, rfl⟩
  have hS0 : 0 ≤ S := le_csSup hb ⟨0, Set.mem_Iic.mpr (by simp), h0⟩
  have hR : rexpP θ t f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (rexpP_le_one θ t f)
  calc ENNReal.ofReal (Real.exp (θ * f t))
      = rexpP θ t f * ENNReal.ofReal (Real.exp (θ * S)) := by
        rw [rexpP_eq_sup hθ t f hb, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring
    _ = rexpP θ t f * (1 + ∫⁻ x in Set.Ioi (0 : ℝ),
          (Set.Iio S).indicator (fun x => ENNReal.ofReal (θ * Real.exp (θ * x))) x) := by
        rw [layer_cake_exp hθ hS0]
    _ = rexpP θ t f + ∫⁻ x in Set.Ioi (0 : ℝ), rexpP θ t f *
          (Set.Iio S).indicator (fun x => ENNReal.ofReal (θ * Real.exp (θ * x))) x := by
        rw [mul_add, mul_one, lintegral_const_mul' _ _ hR]
    _ = _ := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        have hx0 : 0 ≤ x := le_of_lt hx
        have hiff : (∃ u, u < t ∧ x < f u) ↔ x < S := by
          rw [exceed_before f h0 hll hnj hx0 t, hSdef, lt_csSup_iff hb hne]
          constructor
          · rintro ⟨u, hu, h⟩
            exact ⟨f u, ⟨u, Set.mem_Iic.mpr hu, rfl⟩, h⟩
          · rintro ⟨_, ⟨u, hu, rfl⟩, h⟩
            exact ⟨u, Set.mem_Iic.mp hu, h⟩
        by_cases hxS : x < S
        · rw [Set.indicator_of_mem (show x ∈ Set.Iio S from hxS),
            Set.indicator_of_mem (show x ∈ {x : ℝ | ∃ u, u < t ∧ x < f u} from hiff.mpr hxS)]
          ring
        · rw [Set.indicator_of_notMem (show x ∉ Set.Iio S from hxS),
            Set.indicator_of_notMem (show x ∉ {x : ℝ | ∃ u, u < t ∧ x < f u} from
              fun h => hxS (hiff.mp h))]
          simp

/-- W5 (Wiener-Hopf identity in resolvent form, `ℝ≥0∞`-valued):
`∫ e^{-qt} E e^{θX_t} dt = ρ_q(θ) (1 + ∫_0^∞ θ e^{θx} L_q(x) dx)` with
`ρ_q(θ) = ∫ e^{-qs} E e^{-θR_s} ds` and `L_q(x) = E[e^{-q τ_x}; τ_x < ∞]`. -/
theorem wh_identity {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {θ : ℝ} (hθ : 0 ≤ θ) {q : ℝ} (hq : 0 < q) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (Real.toNNReal t) ω)) ∂P =
      (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) *
          ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P) *
        (1 + ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (θ * x)) *
          ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P) := by
  have hXL := hX.isSNLevy
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hXL.measurable u
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t))) with hw
  set c : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (θ * Real.exp (θ * x)) with hc
  set R : ℝ → Ω → ℝ≥0∞ := fun t ω => rexpP θ (Real.toNNReal t) (fun u => X u ω) with hRdef
  have hcm : Measurable c :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  set Z : Set ((ℝ × ℝ) × Ω) := {z | ∃ u, u < Real.toNNReal z.1.1 ∧ z.1.2 < X u z.2} with hZ
  have hZm : MeasurableSet Z := by
    have : Z = ⋃ r : ℚ, {z : (ℝ × ℝ) × Ω |
        Real.toNNReal r < Real.toNNReal z.1.1 ∧ z.1.2 < X (Real.toNNReal r) z.2} := by
      ext z
      simp only [hZ, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        exact exists_rat_hit (fun u => X u z.2) (hXL.right_continuous z.2) h
      · rintro ⟨r, h1, h2⟩
        exact ⟨_, h1, h2⟩
    rw [this]
    refine MeasurableSet.iUnion fun r => ?_
    exact (measurableSet_lt measurable_const
      (measurable_real_toNNReal.comp (measurable_fst.comp measurable_fst))).inter
      (measurableSet_lt (measurable_snd.comp measurable_fst) ((hXL.measurable _).comp measurable_snd))
  have hRj : Measurable (fun z : (ℝ × ℝ) × Ω => R z.1.1 z.2) := by
    have h := measurable_rexpJ θ (τ := fun z : (ℝ × ℝ) × Ω => Real.toNNReal z.1.1)
      (π := fun z => fun u => X u z.2)
      (measurable_real_toNNReal.comp (measurable_fst.comp measurable_fst)) (hXp.comp measurable_snd)
    have heq : (fun z : (ℝ × ℝ) × Ω => R z.1.1 z.2) =
        rexpJ θ (fun z : (ℝ × ℝ) × Ω => Real.toNNReal z.1.1) (fun z => fun u => X u z.2) :=
      funext fun z => (rexpJ_eq θ (fun z : (ℝ × ℝ) × Ω => Real.toNNReal z.1.1)
        (fun z => fun u => X u z.2) z (hXL.right_continuous z.2)).symm
    rw [heq]
    exact h
  have hRt : ∀ t, Measurable (R t) := fun t =>
    hRj.comp (show Measurable fun ω : Ω => (((t, (0 : ℝ)) : ℝ × ℝ), ω) from
      measurable_const.prodMk measurable_id)
  set K : (ℝ × ℝ) × Ω → ℝ≥0∞ := Z.indicator (fun z => R z.1.1 z.2) with hK
  have hKm : Measurable K := hRj.indicator hZm
  have hKx : ∀ t x ω, K ((t, x), ω) =
      ({x' : ℝ | ∃ u, u < Real.toNNReal t ∧ x' < X u ω}).indicator (fun _ => R t ω) x :=
    fun t x ω => rfl
  have hKA : ∀ t x, ∫⁻ ω, K ((t, x), ω) ∂P =
      ∫⁻ ω in {ω | ∃ u, u < Real.toNNReal t ∧ x < X u ω}, R t ω ∂P := by
    intro t x
    have hm : MeasurableSet {ω | ∃ u, u < Real.toNNReal t ∧ x < X u ω} :=
      (show Measurable fun ω : Ω => (((t, x) : ℝ × ℝ), ω) from
        measurable_const.prodMk measurable_id) hZm
    rw [← lintegral_indicator hm]
    rfl
  have hstep : ∀ t : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (Real.toNNReal t) ω)) ∂P =
      ∫⁻ ω, R t ω ∂P + ∫⁻ x in Set.Ioi (0 : ℝ), c x * ∫⁻ ω, K ((t, x), ω) ∂P := by
    intro t
    have hpw : ∀ ω, ENNReal.ofReal (Real.exp (θ * X (Real.toNNReal t) ω)) =
        R t ω + ∫⁻ x in Set.Ioi (0 : ℝ), c x * K ((t, x), ω) := by
      intro ω
      simp_rw [hKx]
      exact path_identity (fun u => X u ω) (hXL.start_zero ω) (hXL.right_continuous ω)
        (hXL.left_limits ω) (hXL.no_positive_jumps ω) hθ (Real.toNNReal t)
    rw [lintegral_congr hpw, lintegral_add_left (hRt t)]
    congr 1
    have hmeas : Measurable (Function.uncurry fun (ω : Ω) (x : ℝ) => c x * K ((t, x), ω)) :=
      (hcm.comp measurable_snd).mul (hKm.comp
        ((measurable_const.prodMk measurable_snd).prodMk measurable_fst))
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    refine lintegral_congr fun x => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hG : Measurable fun z : ℝ × ℝ => ∫⁻ ω, K (z, ω) ∂P := hKm.lintegral_prod_right'
  have hρm : Measurable fun t : ℝ => w t * ∫⁻ ω, R t ω ∂P :=
    (measurable_expWeight q).mul ((measurable_rexpMean hXL θ).comp measurable_real_toNNReal)
  have hjoint : Measurable (Function.uncurry fun (t x : ℝ) => w t * (c x * ∫⁻ ω, K ((t, x), ω) ∂P)) :=
    ((measurable_expWeight q).comp measurable_fst).mul ((hcm.comp measurable_snd).mul hG)
  set ρ := ∫⁻ s in Set.Ioi (0 : ℝ), w s * ∫⁻ ω, R s ω ∂P with hρdef
  have hρ : ρ ≠ ⊤ := by
    have hle : ρ ≤ ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-q * s)) := by
      refine lintegral_mono fun s => ?_
      have h1 : ∫⁻ ω, R s ω ∂P ≤ 1 := by
        calc ∫⁻ ω, R s ω ∂P ≤ ∫⁻ _, 1 ∂P := lintegral_mono fun ω => rexpP_le_one _ _ _
          _ = 1 := by simp
      calc w s * ∫⁻ ω, R s ω ∂P ≤ w s * 1 := by gcongr
        _ = ENNReal.ofReal (Real.exp (-q * s)) := by rw [mul_one, hw, neg_mul]
    exact ne_top_of_le_ne_top (exp_neg_integrableOn_Ioi 0 hq).lintegral_lt_top.ne hle
  calc ∫⁻ t in Set.Ioi (0 : ℝ), w t * ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (Real.toNNReal t) ω)) ∂P
      = ∫⁻ t in Set.Ioi (0 : ℝ), (w t * ∫⁻ ω, R t ω ∂P +
          ∫⁻ x in Set.Ioi (0 : ℝ), w t * (c x * ∫⁻ ω, K ((t, x), ω) ∂P)) := by
        refine lintegral_congr fun t => ?_
        rw [hstep t, mul_add, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ρ + ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in Set.Ioi (0 : ℝ),
          w t * (c x * ∫⁻ ω, K ((t, x), ω) ∂P) := lintegral_add_left hρm _
    _ = ρ + ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ t in Set.Ioi (0 : ℝ),
          w t * (c x * ∫⁻ ω, K ((t, x), ω) ∂P) := by
        rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ = ρ + ∫⁻ x in Set.Ioi (0 : ℝ), c x *
          ((∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P) * ρ) := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        simp_rw [mul_left_comm (w _) (c x)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        simp_rw [hKA]
        exact wh_resolvent 𝓕 P X hX (le_of_lt hx) hθ q
    _ = ρ * (1 + ∫⁻ x in Set.Ioi (0 : ℝ), c x *
          ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P) := by
        rw [mul_add, mul_one, ← lintegral_const_mul' _ _ hρ]
        congr 1
        refine lintegral_congr fun x => ?_
        ring

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- W6a: `t ↦ E e^{θ X_t}` (in `ℝ≥0∞`) is multiplicative. -/
theorem mgf_mult {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (θ : ℝ) (s t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (s + t) ω)) ∂P =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X t ω)) ∂P := by
  have hXL := hX.isSNLevy
  set φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (θ * y)) with hφ
  have hφm : Measurable φ :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  set Δ : Ω → ℝ := fun ω => X (s + t) ω - X s ω with hΔ
  have hΔm : Measurable Δ := (hXL.measurable _).sub (hXL.measurable _)
  have h1 : ∀ ω, ENNReal.ofReal (Real.exp (θ * X (s + t) ω)) = φ (X s ω) * φ (Δ ω) := by
    intro ω
    simp only [hφ, hΔ]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [lintegral_congr h1]
  have hind : Indep (𝓕 s) (MeasurableSpace.comap Δ inferInstance) P := (hX.indep_past s t).symm
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (f := fun ω => φ (X s ω)) (g := fun ω => φ (Δ ω)) (𝓕.le s)
      (measurable_iff_comap_le.1 hΔm) hind (hφm.comp (hX.adapted s))
      (hφm.comp (comap_measurable Δ))]
  refine congrArg₂ (· * ·) rfl ?_
  exact ((hXL.stationary_increments s t).comp hφm).lintegral_eq

/-- The set `{(ω, x) | ∃ u < t, x < X_u(ω)}` is measurable. -/
lemma measurableSet_exceedBefore {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) (t : ℝ≥0) :
    MeasurableSet {p : Ω × ℝ | ∃ u, u < t ∧ p.2 < X u p.1} := by
  have : {p : Ω × ℝ | ∃ u, u < t ∧ p.2 < X u p.1} =
      ⋃ r : ℚ, {p : Ω × ℝ | Real.toNNReal r < t ∧ p.2 < X (Real.toNNReal r) p.1} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact exists_rat_hit (fun u => X u p.1) (hX.right_continuous p.1) h
    · rintro ⟨r, h1, h2⟩
      exact ⟨_, h1, h2⟩
  rw [this]
  refine MeasurableSet.iUnion fun r => ?_
  by_cases hr : Real.toNNReal r < t
  · simp only [hr, true_and]
    exact measurableSet_lt measurable_snd ((hX.measurable _).comp measurable_fst)
  · simp only [hr, false_and, Set.setOf_false]
    exact MeasurableSet.empty

lemma measurableSet_exceeds {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) (x : ℝ) :
    MeasurableSet {ω | ∃ u, x < X u ω} := by
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hX.measurable u
  have : {ω | ∃ u, x < X u ω} = {ω | (fun u => X u ω) ∈ exceedSet x} := by
    ext ω
    exact (mem_exceedSet_iff _ (hX.right_continuous ω) x).symm
  rw [this]
  exact hXp (measurableSet_exceedSet x)

/-- `P(∃u<t, x<X_u) ≤ e^{qt} E[e^{-qτ_x}; τ_x<∞]`. -/
lemma prob_exceed_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {q : ℝ} (hq : 0 ≤ q) (t : ℝ≥0) (x : ℝ) :
    P {ω | ∃ u, u < t ∧ x < X u ω} ≤ ENNReal.ofReal (Real.exp (q * t)) *
      ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P := by
  have hA : MeasurableSet {ω | ∃ u, u < t ∧ x < X u ω} :=
    measurable_prodMk_right (measurableSet_exceedBefore hX t)
  have hE := measurableSet_exceeds hX x
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator_one hA,
    ← lintegral_indicator hE]
  refine lintegral_mono fun ω => ?_
  by_cases h : ∃ u, u < t ∧ x < X u ω
  · obtain ⟨u, hu, hxu⟩ := h
    have hpass : pass X x ω < t := lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) hxu) hu
    rw [Set.indicator_of_mem (show ω ∈ {ω | ∃ u, u < t ∧ x < X u ω} from ⟨u, hu, hxu⟩),
      Set.indicator_of_mem (show ω ∈ {ω | ∃ u, x < X u ω} from ⟨u, hxu⟩)]
    simp only [Pi.one_apply]
    unfold expPass
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
    have : ((pass X x ω : ℝ≥0) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hpass.le
    nlinarith
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | ∃ u, u < t ∧ x < X u ω} from h)]
    simp

/-- W6b: `E e^{θX_t} ≤ 1 + e^{qt} ∫_0^∞ θ e^{θx} L_q(x) dx`. -/
theorem mgf_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {θ : ℝ} (hθ : 0 ≤ θ) {q : ℝ} (hq : 0 ≤ q)
    (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X t ω)) ∂P ≤ 1 + ENNReal.ofReal (Real.exp (q * t)) *
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (θ * x)) *
        ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P := by
  set c : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (θ * Real.exp (θ * x)) with hc
  have hcm : Measurable c :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  have hZ := measurableSet_exceedBefore hX t
  set Z := {p : Ω × ℝ | ∃ u, u < t ∧ p.2 < X u p.1} with hZdef
  have hpw : ∀ ω, ENNReal.ofReal (Real.exp (θ * X t ω)) ≤
      1 + ∫⁻ x in Set.Ioi (0 : ℝ), c x * Z.indicator 1 (ω, x) := by
    intro ω
    rw [path_identity (fun u => X u ω) (hX.start_zero ω) (hX.right_continuous ω)
      (hX.left_limits ω) (hX.no_positive_jumps ω) hθ t]
    refine add_le_add (rexpP_le_one θ t _) (lintegral_mono fun x => ?_)
    gcongr
    by_cases h : ∃ u, u < t ∧ x < X u ω
    · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | ∃ u, u < t ∧ x < X u ω} from h),
        Set.indicator_of_mem (show (ω, x) ∈ Z from h)]
      exact rexpP_le_one θ t _
    · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | ∃ u, u < t ∧ x < X u ω} from h)]
      simp
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X t ω)) ∂P
      ≤ ∫⁻ ω, (1 + ∫⁻ x in Set.Ioi (0 : ℝ), c x * Z.indicator 1 (ω, x)) ∂P := lintegral_mono hpw
    _ = 1 + ∫⁻ x in Set.Ioi (0 : ℝ), c x * P {ω | ∃ u, u < t ∧ x < X u ω} := by
        rw [lintegral_add_left measurable_const, lintegral_one, measure_univ]
        congr 1
        have hm : Measurable (Function.uncurry fun (ω : Ω) (x : ℝ) => c x * Z.indicator 1 (ω, x)) :=
          (hcm.comp measurable_snd).mul (measurable_one.indicator hZ)
        rw [lintegral_lintegral_swap hm.aemeasurable]
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        have hs : MeasurableSet {ω | ∃ u, u < t ∧ x < X u ω} := measurable_prodMk_right hZ
        rw [← lintegral_indicator_one hs]
        rfl
    _ ≤ 1 + ∫⁻ x in Set.Ioi (0 : ℝ), c x * (ENNReal.ofReal (Real.exp (q * t)) *
          ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P) := by
        gcongr with x
        exact prob_exceed_le P hX hq t x
    _ = _ := by
        congr 1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        ring

/-- The first passage above `c > 0` is strictly positive on `{τ_c < ∞}`. -/
lemma pass_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) {c : ℝ} (hc : 0 < c) (ω : Ω) (hω : ∃ u, c < X u ω) :
    0 < pass X c ω := by
  have hev : ∀ᶠ r in 𝓝[≥] (0 : ℝ≥0), X r ω < c :=
    (hX.right_continuous ω 0).eventually (gt_mem_nhds (by show X 0 ω < c; rw [hX.start_zero ω]; exact hc))
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
  refine lt_of_lt_of_le hδ (le_csInf hω fun u hu => ?_)
  by_contra hlt
  push Not at hlt
  have := hsub ⟨by simp, hlt⟩
  exact absurd (show c < X u ω from hu) (not_lt.mpr (show X u ω < c from this).le)

/-- W6c: `L_q(1) → 0` as `q → ∞`. -/
theorem laplace_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) :
    Tendsto (fun q : ℝ => ∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P) atTop (𝓝 0) := by
  have hE := measurableSet_exceeds hX 1
  have h := tendsto_lintegral_filter_of_dominated_convergence' (μ := P.restrict {ω | ∃ u, 1 < X u ω})
    (l := atTop) (F := fun q => expPass X q 1) (f := fun _ => 0) (fun _ => 1)
    (Eventually.of_forall fun q => (measurable_expPass hX q 1).aemeasurable)
    ((eventually_ge_atTop 0).mono fun q hq => Eventually.of_forall fun ω => by
      refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr ?_)
      have := mul_nonneg hq (NNReal.coe_nonneg (pass X 1 ω))
      linarith)
    (by simp)
    ((ae_restrict_iff' hE).mpr (Eventually.of_forall fun ω hω => by
      have hp : (0 : ℝ) < (pass X 1 ω : ℝ) := by exact_mod_cast pass_pos hX one_pos ω hω
      have h1 : Tendsto (fun q : ℝ => -(q * (pass X 1 ω : ℝ))) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hp)
      have h2 := ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp h1)
      rw [ENNReal.ofReal_zero] at h2
      exact h2))
  simpa using h

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- W6d1: an exponential-in-time bound `E e^{θ X_t} ≤ 1 + e^{qt} M` with `M < ∞`. -/
theorem exists_mgf_bound {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ q : ℝ, 0 ≤ q ∧ ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ t : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X t ω)) ∂P ≤ 1 + ENNReal.ofReal (Real.exp (q * t)) * M := by
  have hXL := hX.isSNLevy
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-(θ + 1))) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  obtain ⟨q, hqL, hq⟩ := (((laplace_tendsto_zero P hXL).eventually (gt_mem_nhds hpos)).and
    (eventually_ge_atTop 0)).exists
  have hqL' : ∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P ≤
      ENNReal.ofReal (Real.exp (-(θ + 1))) := le_of_lt hqL
  refine ⟨q, hq, ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (θ * x)) *
      ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P, ?_, fun t => mgf_bound P hXL hθ hq t⟩
  have hle : ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (θ * x)) *
      ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P ≤
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (-1 * x)) := by
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    rw [laplace_rpow 𝓕 P X hX hq hx]
    calc ENNReal.ofReal (θ * Real.exp (θ * x)) *
          (∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P) ^ x
        ≤ ENNReal.ofReal (θ * Real.exp (θ * x)) * ENNReal.ofReal (Real.exp (-(θ + 1))) ^ x := by
          gcongr
      _ = ENNReal.ofReal (θ * Real.exp (-1 * x)) := by
          rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
            ← ENNReal.ofReal_mul (mul_nonneg hθ (Real.exp_pos _).le)]
          congr 1
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  exact ne_top_of_le_ne_top ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul θ).lintegral_lt_top.ne hle

/-- W6d2: `E e^{θ X_t} < ∞` for `θ ≥ 0`. -/
theorem mgf_finite {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X t ω)) ∂P ≠ ⊤ := by
  obtain ⟨q, -, M, hM, hb⟩ := exists_mgf_bound 𝓕 P X hX hθ
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM⟩) (hb t)

/-- W6d3: `E e^{θ X_t} = e^{t ψ(θ)}` for `θ ≥ 0`, with `ψ = Shared.psi` (the cgf of `X_1`). -/
theorem mgf_exp {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X t ω)) ∂P =
      ENNReal.ofReal (Real.exp (t * Shared.psi P X θ)) := by
  have hXL := hX.isSNLevy
  set G : ℝ≥0 → ℝ≥0∞ := fun s => ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P with hG
  have hGfin : ∀ s, G s ≠ ⊤ := fun s => mgf_finite 𝓕 P X hX hθ s
  have hGpos : ∀ s, 0 < G s := by
    intro s
    have hm : Measurable fun ω => ENNReal.ofReal (Real.exp (θ * X s ω)) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul (hXL.measurable s)))
    show 0 < ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X s ω)) ∂P
    rw [lintegral_pos_iff_support hm]
    have : Function.support (fun ω => ENNReal.ofReal (Real.exp (θ * X s ω))) = Set.univ :=
      Set.eq_univ_of_forall fun ω => by simp [Function.mem_support, Real.exp_pos]
    rw [this, measure_univ]
    exact one_pos
  obtain ⟨q, hq, M, hM, hb⟩ := exists_mgf_bound 𝓕 P X hX hθ
  set h : ℝ → ℝ := fun a => (G (Real.toNNReal a)).toReal * Real.exp (-(q * a)) with hh
  have hpos : ∀ a, 0 ≤ a → 0 < h a := fun a _ =>
    mul_pos (ENNReal.toReal_pos (hGpos _).ne' (hGfin _)) (Real.exp_pos _)
  have hmul : ∀ a b, 0 ≤ a → 0 ≤ b → h (a + b) = h a * h b := by
    intro a b ha hb'
    simp only [hh]
    rw [Real.toNNReal_add ha hb']
    have := mgf_mult 𝓕 P X hX θ (Real.toNNReal a) (Real.toNNReal b)
    simp only [hG]
    rw [this, ENNReal.toReal_mul]
    rw [show -(q * (a + b)) = -(q * a) + -(q * b) by ring, Real.exp_add]
    ring
  have hbd : ∀ a, 0 ≤ a → h a ≤ 1 + M.toReal := by
    intro a ha
    have h1 : (G (Real.toNNReal a)).toReal ≤ 1 + Real.exp (q * a) * M.toReal := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM⟩) (hb (Real.toNNReal a))
      rw [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.coe_toNNReal _ ha,
        ENNReal.toReal_one] at this
      exact this
    have h2 : Real.exp (-(q * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h3 : Real.exp (q * a) * Real.exp (-(q * a)) = 1 := by rw [← Real.exp_add]; simp
    have hM0 : 0 ≤ M.toReal := ENNReal.toReal_nonneg
    calc h a = (G (Real.toNNReal a)).toReal * Real.exp (-(q * a)) := rfl
      _ ≤ (1 + Real.exp (q * a) * M.toReal) * Real.exp (-(q * a)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-(q * a)) + M.toReal * (Real.exp (q * a) * Real.exp (-(q * a))) := by ring
      _ ≤ 1 + M.toReal := by rw [h3, mul_one]; linarith
  have hpow : ∀ a, 0 ≤ a → ∀ n : ℕ, h (n * a) = h a ^ n := by
    intro a ha n
    induction n with
    | zero =>
      have h0 : h 0 = 1 := by
        have := hmul 0 0 le_rfl le_rfl
        rw [add_zero] at this
        have hp := hpos 0 le_rfl
        have : h 0 * (h 0 - 1) = 0 := by linarith [this]
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · linarith
      simp [h0]
    | succ n ih =>
      rw [show ((n + 1 : ℕ) : ℝ) * a = n * a + a by push_cast; ring,
        hmul _ _ (mul_nonneg (Nat.cast_nonneg n) ha) ha, ih, pow_succ]
  have hle : ∀ a, 0 ≤ a → h a ≤ 1 := by
    intro a ha
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 + M.toReal) hlt
    have := hbd (n * a) (mul_nonneg (Nat.cast_nonneg n) ha)
    rw [hpow a ha n] at this
    linarith
  have hc := cauchy_real h hmul hle hpos
  -- identify `G 1` with the real mgf
  have hmgf : (G 1).toReal = mgf (X 1) P θ := by
    show _ = ∫ ω, Real.exp (θ * X 1 ω) ∂P
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => Real.exp (θ * X 1 ω))
      (Eventually.of_forall fun ω => (Real.exp_pos _).le)
      (Real.measurable_exp.comp (measurable_const.mul (hXL.measurable 1))).aestronglyMeasurable]
  have hmgfpos : 0 < mgf (X 1) P θ := hmgf ▸ ENNReal.toReal_pos (hGpos 1).ne' (hGfin 1)
  have ht := hc t t.2
  have h1 : h 1 = (G 1).toReal * Real.exp (-q) := by
    simp only [hh, Real.toNNReal_one, mul_one]
  show G t = _
  rw [← ENNReal.ofReal_toReal (hGfin t)]
  congr 1
  have hGt : (G t).toReal = h t * Real.exp (q * t) := by
    simp only [hh, Real.toNNReal_coe]
    rw [mul_assoc, ← Real.exp_add]
    simp
  rw [hGt, ht, h1, Real.mul_rpow (ENNReal.toReal_nonneg) (Real.exp_pos _).le, ← Real.exp_mul,
    hmgf, Real.rpow_def_of_pos hmgfpos, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold Shared.psi cgf
  ring

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- `∫_0^∞ e^{ax} dx = (-a)⁻¹` for `a < 0` (as `ℝ≥0∞`). -/
lemma lintegral_exp_Ioi {a : ℝ} (ha : a < 0) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (a * x)) = ENNReal.ofReal (-a)⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi ha 0)
    (Eventually.of_forall fun x => (Real.exp_pos _).le), integral_exp_mul_Ioi ha 0]
  congr 1
  rw [mul_zero, Real.exp_zero]
  have : a ≠ 0 := ha.ne
  field_simp

/-- `∫_0^∞ c e^{ax} dx = ∞` for `a ≥ 0`, `c > 0`. -/
lemma lintegral_exp_Ioi_top {a : ℝ} (ha : 0 ≤ a) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (a * x)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  calc (⊤ : ℝ≥0∞) = ∫⁻ _ in Set.Ioi (0 : ℝ), ENNReal.ofReal c := by
        rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top (by simpa using hc)]
    _ ≤ _ := by
        refine setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal ?_
        have : 1 ≤ Real.exp (a * x) := Real.one_le_exp (mul_nonneg ha (le_of_lt hx))
        nlinarith

/-- W6e1: the time integral of `e^{-qt} e^{tψ}`, finite case. -/
lemma time_integral_lt {q ψ : ℝ} (h : ψ < q) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) *
      ENNReal.ofReal (Real.exp (t * ψ)) = ENNReal.ofReal (q - ψ)⁻¹ := by
  have : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-(q * t))) * ENNReal.ofReal (Real.exp (t * ψ)) =
      ENNReal.ofReal (Real.exp ((ψ - q) * t)) := by
    intro t
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  simp_rw [this]
  rw [lintegral_exp_Ioi (by linarith)]
  congr 2
  ring

/-- W6e1': the time integral of `e^{-qt} e^{tψ}`, infinite case. -/
lemma time_integral_top {q ψ : ℝ} (h : q ≤ ψ) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) *
      ENNReal.ofReal (Real.exp (t * ψ)) = ⊤ := by
  have : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-(q * t))) * ENNReal.ofReal (Real.exp (t * ψ)) =
      ENNReal.ofReal (1 * Real.exp ((ψ - q) * t)) := by
    intro t
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, one_mul]
    congr 2
    ring
  simp_rw [this]
  exact lintegral_exp_Ioi_top (by linarith) one_pos

/-- W6e2: `∫_0^∞ θ e^{θx} (e^{-κ})^x dx = θ/(κ-θ)` for `0 ≤ θ < κ`. -/
lemma level_integral_lt {θ κ : ℝ} (hθ : 0 ≤ θ) (h : θ < κ) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (θ * x)) *
      ENNReal.ofReal (Real.exp (-κ)) ^ x = ENNReal.ofReal (θ * (κ - θ)⁻¹) := by
  have : ∀ x : ℝ, ENNReal.ofReal (θ * Real.exp (θ * x)) * ENNReal.ofReal (Real.exp (-κ)) ^ x =
      ENNReal.ofReal θ * ENNReal.ofReal (Real.exp ((θ - κ) * x)) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
      ENNReal.ofReal_mul hθ, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3
    ring
  simp_rw [this]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_exp_Ioi (by linarith),
    ← ENNReal.ofReal_mul hθ]
  congr 2
  ring

/-- W6e2': the level integral is infinite for `0 < θ`, `κ ≤ θ`. -/
lemma level_integral_top {θ κ : ℝ} (hθ : 0 < θ) (h : κ ≤ θ) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (θ * x)) *
      ENNReal.ofReal (Real.exp (-κ)) ^ x = ⊤ := by
  have : ∀ x : ℝ, ENNReal.ofReal (θ * Real.exp (θ * x)) * ENNReal.ofReal (Real.exp (-κ)) ^ x =
      ENNReal.ofReal (θ * Real.exp ((θ - κ) * x)) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
      ← ENNReal.ofReal_mul (mul_nonneg hθ.le (Real.exp_pos _).le), mul_assoc, ← Real.exp_add]
    congr 3
    ring
  simp_rw [this]
  exact lintegral_exp_Ioi_top (by linarith) hθ

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- `ρ_q(θ) = ∫ e^{-qs} E e^{-θR_s} ds < ∞` for `q > 0`. -/
lemma rho_ne_top {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) {q : ℝ} (hq : 0 < q) (θ : ℝ) :
    (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) *
      ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P) ≠ ⊤ := by
  have hle : (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) *
      ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P) ≤
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-q * s)) := by
    refine lintegral_mono fun s => ?_
    have h1 : ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P ≤ 1 :=
      (lintegral_mono fun ω => rexpP_le_one _ _ _).trans (by simp)
    calc ENNReal.ofReal (Real.exp (-(q * s))) * ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P
        ≤ ENNReal.ofReal (Real.exp (-(q * s))) * 1 := by gcongr
      _ = ENNReal.ofReal (Real.exp (-q * s)) := by rw [mul_one, neg_mul]
  exact ne_top_of_le_ne_top (exp_neg_integrableOn_Ioi 0 hq).lintegral_lt_top.ne hle

/-- `ρ_q(θ) > 0`. -/
lemma rho_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {θ : ℝ} (hθ : 0 ≤ θ) (q : ℝ) :
    0 < ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) *
      ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P := by
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hX.measurable u
  have hin : ∀ s : ℝ≥0, 0 < ∫⁻ ω, rexpP θ s (fun u => X u ω) ∂P := by
    intro s
    have hm : Measurable fun ω => rexpP θ s (fun u => X u ω) := by
      have : (fun ω => rexpP θ s (fun u => X u ω)) = fun ω => rexpQ θ s (fun u => X u ω) :=
        funext fun ω => rexpP_eq_rexpQ θ s _ (hX.right_continuous ω)
      rw [this]
      exact (measurable_rexpQ θ s).comp hXp
    rw [lintegral_pos_iff_support hm]
    have : Function.support (fun ω => rexpP θ s (fun u => X u ω)) = Set.univ :=
      Set.eq_univ_of_forall fun ω => by
        rw [Function.mem_support, rexpP_eq_sup hθ s _
          (bddAbove_of_cadlag _ (hX.right_continuous ω) (hX.left_limits ω) s)]
        exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    rw [this, measure_univ]
    exact one_pos
  have hm : Measurable fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s))) *
      ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P :=
    (measurable_expWeight q).mul ((measurable_rexpMean hX θ).comp measurable_real_toNNReal)
  rw [lintegral_pos_iff_support hm]
  have : Function.support (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s))) *
      ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P) = Set.univ :=
    Set.eq_univ_of_forall fun s =>
      (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' (hin _).ne').ne'
  rw [this, Measure.restrict_apply_univ, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- `L_q(1) < 1` for `q > 0`. -/
lemma laplace_lt_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {q : ℝ} (hq : 0 < q) :
    ∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P < 1 := by
  have hEm := measurableSet_exceeds hX 1
  by_cases hE0 : P {ω | ∃ u, 1 < X u ω} = 0
  · rw [Measure.restrict_eq_zero.mpr hE0, lintegral_zero_measure]
    exact zero_lt_one
  · calc ∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P
        < ∫⁻ _ in {ω | ∃ u, 1 < X u ω}, 1 ∂P := by
          refine setLIntegral_strict_mono hEm hE0 measurable_const
            ((setLIntegral_expPass_le_one P X hq.le 1 _).trans_lt ENNReal.one_lt_top).ne
            (Eventually.of_forall fun ω hω => ?_)
          have hp : (0 : ℝ) < (pass X 1 ω : ℝ) := by exact_mod_cast pass_pos hX one_pos ω hω
          refine ENNReal.ofReal_lt_one.mpr (Real.exp_lt_one_iff.mpr ?_)
          nlinarith
      _ = P {ω | ∃ u, 1 < X u ω} := by rw [setLIntegral_const, one_mul]
      _ ≤ 1 := prob_le_one

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- A rational point in `[t, s)` where a right-continuous `f` lands in an open set `U ∋ f t`. -/
lemma exists_rat_window (f : ℝ≥0 → ℝ) {t : ℝ≥0} (hrc : ContinuousWithinAt f (Set.Ici t) t)
    {U : Set ℝ} (hU : IsOpen U) (ht : f t ∈ U) {s : ℝ≥0} (hts : t < s) :
    ∃ q : ℚ, t ≤ Real.toNNReal q ∧ Real.toNNReal q < s ∧ f (Real.toNNReal q) ∈ U := by
  have hev : ∀ᶠ r in 𝓝[≥] t, f r ∈ U := hrc.eventually (hU.mem_nhds ht)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
  have hlt : (t : ℝ) < ((min u s : ℝ≥0) : ℝ) := by exact_mod_cast lt_min hu hts
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have hq0 : (0 : ℝ) ≤ q := le_trans t.2 hq1.le
  have hqe : ((Real.toNNReal q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
  have h1 : t ≤ Real.toNNReal q := by rw [← NNReal.coe_le_coe, hqe]; exact hq1.le
  have h2 : Real.toNNReal q < min u s := by rw [← NNReal.coe_lt_coe, hqe]; exact hq2
  exact ⟨q, h1, lt_of_lt_of_le h2 (min_le_right _ _),
    hsub ⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩⟩

/-- A right-continuous path that is antitone on the rational points is antitone. -/
lemma antitone_of_rat (f : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (H : ∀ e d : ℚ, Real.toNNReal e ≤ Real.toNNReal d →
      f (Real.toNNReal d) ≤ f (Real.toNNReal e)) : Antitone f := by
  intro s t hst
  rcases eq_or_lt_of_le hst with rfl | hlt
  · exact le_rfl
  by_contra hcon
  push Not at hcon
  obtain ⟨d, hd1, -, hd3⟩ := exists_rat_window f (hrc t) (isOpen_Ioi (a := (f s + f t) / 2))
    (show f t ∈ Set.Ioi ((f s + f t) / 2) by rw [Set.mem_Ioi]; linarith) (lt_add_one t)
  obtain ⟨e, -, he2, he3⟩ := exists_rat_window f (hrc s) (isOpen_Iio (a := (f s + f t) / 2))
    (show f s ∈ Set.Iio ((f s + f t) / 2) by rw [Set.mem_Iio]; linarith) (lt_of_lt_of_le hlt hd1)
  have h := H e d he2.le
  rw [Set.mem_Ioi] at hd3
  rw [Set.mem_Iio] at he3
  linarith

/-- `P(∃u, 1 < X_u) > 0`: otherwise `X ≤ 0` a.s. at every time, so `X` is a.s. antitone. -/
theorem exceed_one_pos {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) :
    P {ω | ∃ u, 1 < X u ω} ≠ 0 := by
  have hXL := hX.isSNLevy
  intro h1
  have hp : ∀ n : ℕ, P {ω | ∃ u, ((1 : ℝ) / 2) ^ n < X u ω} = 0 := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      have hm := sup_mult 𝓕 P X hX (a := ((1 : ℝ) / 2) ^ (n + 1)) (b := ((1 : ℝ) / 2) ^ (n + 1))
        (by positivity) (by positivity)
      have he : ((1 : ℝ) / 2) ^ (n + 1) + ((1 : ℝ) / 2) ^ (n + 1) = ((1 : ℝ) / 2) ^ n := by
        rw [pow_succ]; ring
      rw [he, ih] at hm
      exact mul_self_eq_zero.mp hm.symm
  have h0 : P {ω | ∃ u, 0 < X u ω} = 0 := by
    have : {ω | ∃ u, 0 < X u ω} = ⋃ n : ℕ, {ω | ∃ u, ((1 : ℝ) / 2) ^ n < X u ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨u, hu⟩
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hu (by norm_num : (1 : ℝ) / 2 < 1)
        exact ⟨n, u, hn⟩
      · rintro ⟨n, u, hu⟩
        exact ⟨u, lt_trans (by positivity) hu⟩
    rw [this]
    exact measure_iUnion_null hp
  have hle : ∀ t : ℝ≥0, P {ω | 0 < X t ω} = 0 := fun t =>
    measure_mono_null (fun ω (hω : 0 < X t ω) => (⟨t, hω⟩ : ∃ u, 0 < X u ω)) h0
  have hinc : ∀ s t : ℝ≥0, ∀ᵐ ω ∂P, X (s + t) ω ≤ X s ω := by
    intro s t
    have hmeq := (hXL.stationary_increments s t).measure_mem_eq (measurableSet_Ioi (a := (0 : ℝ)))
    rw [ae_iff]
    have hset : {ω | ¬ X (s + t) ω ≤ X s ω} = (fun ω => X (s + t) ω - X s ω) ⁻¹' Set.Ioi 0 := by
      ext ω
      simp [sub_pos]
    rw [hset, hmeq]
    exact hle t
  apply hXL.not_ae_antitone
  have hall : ∀ᵐ ω ∂P, ∀ e d : ℚ, Real.toNNReal e ≤ Real.toNNReal d →
      X (Real.toNNReal d) ω ≤ X (Real.toNNReal e) ω := by
    rw [ae_all_iff]
    intro e
    rw [ae_all_iff]
    intro d
    by_cases hed : Real.toNNReal e ≤ Real.toNNReal d
    · filter_upwards [hinc (Real.toNNReal e) (Real.toNNReal d - Real.toNNReal e)] with ω hω _
      rwa [add_tsub_cancel_of_le hed] at hω
    · exact Eventually.of_forall fun ω h => absurd h hed
  filter_upwards [hall] with ω hω
  exact antitone_of_rat _ (hXL.right_continuous ω) hω

/-- `L_q(1) = E[e^{-qτ_1}; τ_1 < ∞] > 0`. -/
theorem laplace_pos {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (q : ℝ) : 0 < ∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P := by
  have hXL := hX.isSNLevy
  rw [pos_iff_ne_zero]
  intro h0
  rw [lintegral_eq_zero_iff (measurable_expPass hXL q 1)] at h0
  have h2 : ∀ᵐ ω ∂(P.restrict {ω | ∃ u, 1 < X u ω}), False :=
    h0.mono fun ω hω => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hω
  have h3 := ae_iff.mp h2
  simp only [not_false_eq_true, Set.setOf_true, Measure.restrict_apply_univ] at h3
  exact exceed_one_pos 𝓕 P X hX h3

/-- `κ(q) := -log L_q(1)`, so that `L_q(x) = e^{-κ x}`. -/
noncomputable def kap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (q : ℝ) : ℝ :=
  -Real.log (∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P).toReal

lemma laplace_eq_kap {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P = ENNReal.ofReal (Real.exp (-(kap P X q))) := by
  have hpos := laplace_pos 𝓕 P X hX q
  have hle : ∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P ≤ 1 :=
    setLIntegral_expPass_le_one P X hq 1 _
  have hne : ∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hle
  unfold kap
  rw [neg_neg, Real.exp_log (ENNReal.toReal_pos hpos.ne' hne), ENNReal.ofReal_toReal hne]

lemma kap_pos {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) : 0 < kap P X q := by
  have hpos := laplace_pos 𝓕 P X hX q
  have hlt := laplace_lt_one P hX.isSNLevy hq
  have hne : ∫⁻ ω in {ω | ∃ u, 1 < X u ω}, expPass X q 1 ω ∂P ≠ ⊤ :=
    ne_top_of_lt (hlt.trans ENNReal.one_lt_top)
  unfold kap
  rw [neg_pos]
  exact Real.log_neg (ENNReal.toReal_pos hpos.ne' hne)
    (ENNReal.toReal_lt_of_lt_ofReal (by rwa [ENNReal.ofReal_one]))

lemma time_mgf {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {θ : ℝ} (hθ : 0 ≤ θ) (q : ℝ) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (Real.toNNReal t) ω)) ∂P =
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) *
        ENNReal.ofReal (Real.exp (t * Shared.psi P X θ)) := by
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [mgf_exp 𝓕 P X hX hθ, Real.coe_toNNReal _ (le_of_lt ht)]

lemma level_kap {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (θ : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (θ * x)) *
        ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P =
      ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (θ * Real.exp (θ * x)) *
        ENNReal.ofReal (Real.exp (-(kap P X q))) ^ x := by
  refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  rw [laplace_rpow 𝓕 P X hX hq hx, laplace_eq_kap 𝓕 P X hX hq]

/-- Closed Wiener-Hopf identity below `κ`: `(q - ψ θ)⁻¹ = ρ_q(θ) (1 + θ/(κ-θ))` and `ψ θ < q`. -/
theorem wh_closed {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθ : 0 ≤ θ) (hθκ : θ < kap P X q) :
    ENNReal.ofReal (q - Shared.psi P X θ)⁻¹ =
      (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) *
          ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P) *
        (1 + ENNReal.ofReal (θ * (kap P X q - θ)⁻¹)) ∧ Shared.psi P X θ < q := by
  have h := wh_identity 𝓕 P X hX hθ hq
  rw [time_mgf 𝓕 P X hX hθ, level_kap 𝓕 P X hX θ hq.le, level_integral_lt hθ hθκ] at h
  have hψ : Shared.psi P X θ < q := by
    by_contra hc
    push Not at hc
    rw [time_integral_top hc] at h
    exact (ENNReal.mul_ne_top (rho_ne_top P X hq θ)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩)) h.symm
  rw [time_integral_lt hψ] at h
  exact ⟨h, hψ⟩

/-- At or beyond `κ`, `ψ θ ≥ q`. -/
theorem psi_ge_of_kap_le {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {θ : ℝ} (hκθ : kap P X q ≤ θ) : q ≤ Shared.psi P X θ := by
  have hθ : 0 < θ := lt_of_lt_of_le (kap_pos 𝓕 P X hX hq) hκθ
  have h := wh_identity 𝓕 P X hX hθ.le hq
  rw [time_mgf 𝓕 P X hX hθ.le, level_kap 𝓕 P X hX θ hq.le, level_integral_top hθ hκθ,
    add_top, ENNReal.mul_top (rho_pos P hX.isSNLevy hθ.le q).ne'] at h
  by_contra hc
  push Not at hc
  rw [time_integral_lt hc] at h
  exact ENNReal.ofReal_ne_top h

lemma integrable_exp_X1 {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {θ : ℝ} (hθ : 0 ≤ θ) : Integrable (fun ω => Real.exp (θ * X 1 ω)) P := by
  have h := mgf_exp 𝓕 P X hX hθ 1
  have hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X 1 ω)) ∂P ≠ ⊤ := by
    rw [h]; exact ENNReal.ofReal_ne_top
  refine ⟨(Real.measurable_exp.comp (measurable_const.mul
    (hX.isSNLevy.measurable 1))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  exact lt_top_iff_ne_top.2 hfin

lemma Ioi_subset_interior {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) :
    Set.Ioi (0 : ℝ) ⊆ interior (integrableExpSet (X 1) P) :=
  interior_maximal (fun θ hθ => integrable_exp_X1 𝓕 P X hX (le_of_lt hθ)) isOpen_Ioi

lemma psi_analytic {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) :
    AnalyticOnNhd ℝ (Shared.psi P X) (Set.Ioi 0) := by
  have hpsi : Shared.psi P X = cgf (X 1) P := rfl
  rw [hpsi]
  exact fun θ hθ => analyticAt_cgf (Ioi_subset_interior 𝓕 P X hX hθ)

lemma psi_convexOn {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) :
    ConvexOn ℝ (Set.Ioi 0) (Shared.psi P X) := by
  have hA := psi_analytic 𝓕 P X hX
  have hpsi : Shared.psi P X = cgf (X 1) P := rfl
  refine convexOn_of_deriv2_nonneg (convex_Ioi 0) hA.continuousOn ?_ ?_ ?_
  · rw [interior_Ioi]; exact hA.differentiableOn
  · rw [interior_Ioi]; exact hA.deriv.differentiableOn
  · intro x hx
    rw [interior_Ioi] at hx
    rw [← iteratedDeriv_eq_iterate, hpsi,
      iteratedDeriv_two_cgf_eq_integral (Ioi_subset_interior 𝓕 P X hX hx)]
    exact div_nonneg (integral_nonneg fun ω => by positivity) mgf_nonneg

/-- `ψ θ < q ↔ θ < κ(q)` for `θ ≥ 0`. -/
theorem psi_lt_iff {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθ : 0 ≤ θ) : Shared.psi P X θ < q ↔ θ < kap P X q := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact absurd (psi_ge_of_kap_le 𝓕 P X hX hq hc) (not_le.mpr h)
  · intro h
    exact (wh_closed 𝓕 P X hX hq hθ h).2

theorem psi_kap {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) : Shared.psi P X (kap P X q) = q := by
  have hκ := kap_pos 𝓕 P X hX hq
  refine le_antisymm ?_ (psi_ge_of_kap_le 𝓕 P X hX hq le_rfl)
  have hc : ContinuousAt (Shared.psi P X) (kap P X q) := (psi_analytic 𝓕 P X hX _ hκ).continuousAt
  have ht : Tendsto (Shared.psi P X) (𝓝[<] (kap P X q)) (𝓝 (Shared.psi P X (kap P X q))) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ θ in 𝓝[<] (kap P X q), Shared.psi P X θ ≤ q :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hκ) fun θ hθ =>
      ((psi_lt_iff 𝓕 P X hX hq hθ.1.le).2 hθ.2).le
  exact le_of_tendsto ht hev

theorem psi_gt_of_kap_lt {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {θ : ℝ} (hκθ : kap P X q < θ) : q < Shared.psi P X θ := by
  have hκ := kap_pos 𝓕 P X hX hq
  have hs := (psi_convexOn 𝓕 P X hX).slope_mono_adjacent (x := kap P X q / 2) (y := kap P X q)
    (z := θ) (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith)) (by linarith) hκθ
  rw [psi_kap 𝓕 P X hX hq] at hs
  have h1 : Shared.psi P X (kap P X q / 2) < q :=
    (psi_lt_iff 𝓕 P X hX hq (by linarith)).2 (by linarith)
  have h2 : 0 < (q - Shared.psi P X (kap P X q / 2)) / (kap P X q - kap P X q / 2) :=
    div_pos (by linarith) (by linarith)
  have h3 := (div_pos_iff_of_pos_right (by linarith : (0 : ℝ) < θ - kap P X q)).mp
    (lt_of_lt_of_le h2 hs)
  linarith

/-- W6: `κ(q) = Φ(q)`, the largest root of `ψ θ = q`. -/
theorem Phi_eq_kap {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) : Shared.Phi (Shared.psi P X) q = kap P X q := by
  unfold Shared.Phi
  refine IsGreatest.csSup_eq ⟨⟨(kap_pos 𝓕 P X hX hq).le, psi_kap 𝓕 P X hX hq⟩, ?_⟩
  rintro θ ⟨-, hθq⟩
  by_contra h
  push Not at h
  exact (psi_gt_of_kap_lt 𝓕 P X hX hq h).ne' hθq

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- `-R_s` as a real function of `(s, ω)`: `-(sup_{u ≤ s} X_u - X_s)`. -/
noncomputable def Ynr {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (p : ℝ × Ω) : ℝ :=
  -(sSup ((fun u => X u p.2) '' Set.Iic (Real.toNNReal p.1)) - X (Real.toNNReal p.1) p.2)

/-- The time weight `e^{-qs} ds` on `(0, ∞)`. -/
noncomputable abbrev nuq (q : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (Real.exp (-(q * s))))

lemma nuq_finite {q : ℝ} (hq : 0 < q) : IsFiniteMeasure (nuq q) := by
  refine isFiniteMeasure_withDensity ?_
  have h := (exp_neg_integrableOn_Ioi 0 hq).lintegral_lt_top.ne
  simpa only [neg_mul] using h

lemma rexpP_eq_Ynr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) {θ : ℝ} (hθ : 0 ≤ θ) (p : ℝ × Ω) :
    rexpP θ (Real.toNNReal p.1) (fun u => X u p.2) = ENNReal.ofReal (Real.exp (θ * Ynr X p)) := by
  rw [rexpP_eq_sup hθ _ _ (bddAbove_of_cadlag _ (hX.right_continuous p.2) (hX.left_limits p.2) _),
    Ynr, mul_neg]

lemma Ynr_nonpos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (p : ℝ × Ω) : Ynr X p ≤ 0 := by
  have hb := bddAbove_of_cadlag _ (hX.right_continuous p.2) (hX.left_limits p.2) (Real.toNNReal p.1)
  have : X (Real.toNNReal p.1) p.2 ≤ sSup ((fun u => X u p.2) '' Set.Iic (Real.toNNReal p.1)) :=
    le_csSup hb (Set.mem_image_of_mem _ (Set.mem_Iic.mpr le_rfl))
  unfold Ynr
  linarith

lemma measurable_Ynr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) : Measurable (Ynr X) := by
  have hXp : Measurable (fun ω (u : ℝ≥0) => X u ω) :=
    measurable_pi_lambda _ fun u => hX.measurable u
  have heq : Ynr X = fun p => Real.log
      (rexpJ 1 (fun z : ℝ × Ω => Real.toNNReal z.1) (fun z u => X u z.2) p).toReal := by
    funext p
    rw [rexpJ_eq _ _ _ p (hX.right_continuous p.2), rexpP_eq_Ynr hX zero_le_one, one_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
  rw [heq]
  exact Real.measurable_log.comp (ENNReal.measurable_toReal.comp
    (measurable_rexpJ 1 (measurable_real_toNNReal.comp measurable_fst) (hXp.comp measurable_snd)))

/-- `ρ_q(θ)` as a Lebesgue integral over `nuq q ⊗ P`. -/
lemma rho_eq_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {θ : ℝ} (hθ : 0 ≤ θ) (q : ℝ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (θ * Ynr X p)) ∂((nuq q).prod P) =
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) *
        ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P := by
  have hm : Measurable fun p : ℝ × Ω => ENNReal.ofReal (Real.exp (θ * Ynr X p)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_Ynr hX)))
  rw [lintegral_prod _ hm.aemeasurable, nuq,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_expWeight q) hm.lintegral_prod_right']
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply]
  congr 1
  exact lintegral_congr fun ω => (rexpP_eq_Ynr hX hθ (s, ω)).symm

lemma integrable_exp_Ynr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθ : 0 ≤ θ) :
    Integrable (fun p => Real.exp (θ * Ynr X p)) ((nuq q).prod P) := by
  haveI := nuq_finite hq
  refine Integrable.of_bound ((Real.measurable_exp.comp
    (measurable_const.mul (measurable_Ynr hX))).aestronglyMeasurable) 1
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ (Ynr_nonpos hX p))

/-- `ρ_q(θ) = ofReal (mgf (Ynr X) (nuq q ⊗ P) θ)` for `θ ≥ 0`. -/
lemma rho_eq_mgf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) *
        ∫⁻ ω, rexpP θ (Real.toNNReal s) (fun u => X u ω) ∂P) =
      ENNReal.ofReal (mgf (Ynr X) ((nuq q).prod P) θ) := by
  rw [← rho_eq_prod P hX hθ q, mgf, ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_Ynr P hX hq hθ) (Eventually.of_forall fun p => (Real.exp_pos _).le)]

lemma Ioi_subset_interior_Ynr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {q : ℝ} (hq : 0 < q) :
    Set.Ioi (0 : ℝ) ⊆ interior (integrableExpSet (Ynr X) ((nuq q).prod P)) :=
  interior_maximal (fun θ hθ => integrable_exp_Ynr P hX hq (le_of_lt hθ)) isOpen_Ioi

/-- W7 on `(0, κ)`: `ρ_q(θ) κ (q - ψ θ) = κ - θ`. -/
lemma rho_closed_lt {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθ : 0 ≤ θ) (hθκ : θ < kap P X q) :
    mgf (Ynr X) ((nuq q).prod P) θ * kap P X q * (q - Shared.psi P X θ) = kap P X q - θ := by
  obtain ⟨h, hψ⟩ := wh_closed 𝓕 P X hX hq hθ hθκ
  set κ := kap P X q
  set M := mgf (Ynr X) ((nuq q).prod P) θ
  have hM : 0 ≤ M := mgf_nonneg
  have hqψ : 0 < q - Shared.psi P X θ := by linarith
  have hκθ : 0 < κ - θ := by linarith
  have ha : 0 ≤ θ * (κ - θ)⁻¹ := mul_nonneg hθ (inv_nonneg.mpr hκθ.le)
  rw [rho_eq_mgf P hX.isSNLevy hq hθ, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one ha,
    ← ENNReal.ofReal_mul hM, ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.mpr hqψ.le)
      (mul_nonneg hM (by linarith))] at h
  have h2 : M * (1 + θ * (κ - θ)⁻¹) * (q - Shared.psi P X θ) = 1 := by
    rw [← h]; exact inv_mul_cancel₀ hqψ.ne'
  have hc : (κ - θ) * (κ - θ)⁻¹ = 1 := mul_inv_cancel₀ hκθ.ne'
  have key : (κ - θ) * (M * (1 + θ * (κ - θ)⁻¹) * (q - Shared.psi P X θ)) =
      M * κ * (q - Shared.psi P X θ) := by
    calc (κ - θ) * (M * (1 + θ * (κ - θ)⁻¹) * (q - Shared.psi P X θ))
        = M * (q - Shared.psi P X θ) * ((κ - θ) + θ * ((κ - θ) * (κ - θ)⁻¹)) := by ring
      _ = M * κ * (q - Shared.psi P X θ) := by rw [hc]; ring
  rw [h2, mul_one] at key
  exact key.symm

/-- W7 (analytic continuation): `ρ_q(θ) κ (q - ψ θ) = κ - θ` for every `θ > 0`. -/
theorem rho_closed {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθ : 0 < θ) :
    mgf (Ynr X) ((nuq q).prod P) θ * kap P X q * (q - Shared.psi P X θ) = kap P X q - θ := by
  have hκ := kap_pos 𝓕 P X hX hq
  set F : ℝ → ℝ := fun θ => mgf (Ynr X) ((nuq q).prod P) θ * kap P X q * (q - Shared.psi P X θ) -
    (kap P X q - θ) with hFdef
  have hA : AnalyticOnNhd ℝ F (Set.Ioi 0) := by
    have h1 : AnalyticOnNhd ℝ (mgf (Ynr X) ((nuq q).prod P)) (Set.Ioi 0) :=
      analyticOnNhd_mgf.mono (Ioi_subset_interior_Ynr P hX.isSNLevy hq)
    exact ((h1.mul analyticOnNhd_const).mul
      (analyticOnNhd_const.sub (psi_analytic 𝓕 P X hX))).sub
      (analyticOnNhd_const.sub analyticOnNhd_id)
  have hev : F =ᶠ[𝓝 (kap P X q / 2)] 0 := by
    refine Filter.mem_of_superset (Ioo_mem_nhds (by linarith : (0 : ℝ) < kap P X q / 2)
      (by linarith : kap P X q / 2 < kap P X q)) fun x hx => ?_
    simp only [Set.mem_setOf_eq, Pi.zero_apply, hFdef]
    rw [rho_closed_lt 𝓕 P X hX hq hx.1.le hx.2, sub_self]
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_Ioi 0).isPreconnected
    (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < kap P X q / 2)) hev (Set.mem_Ioi.mpr hθ)
  simp only [Pi.zero_apply, hFdef] at hz
  linarith

/-- `ρ_q(θ) = (θ - κ) / (κ (ψ θ - q))` beyond `κ`. -/
theorem rho_gt {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθκ : kap P X q < θ) :
    mgf (Ynr X) ((nuq q).prod P) θ =
      (θ - kap P X q) / (kap P X q * (Shared.psi P X θ - q)) := by
  have hκ := kap_pos 𝓕 P X hX hq
  have hψ := psi_gt_of_kap_lt 𝓕 P X hX hq hθκ
  have h := rho_closed 𝓕 P X hX hq (lt_trans hκ hθκ)
  have hd : kap P X q * (Shared.psi P X θ - q) ≠ 0 := (mul_pos hκ (by linarith)).ne'
  rw [eq_div_iff hd]
  linear_combination -h

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- `G(x) = E_μ[e^{-κR}; R ≤ x]` with `μ = e^{-qs}ds ⊗ P`, `R = -Ynr`. -/
noncomputable def Gq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (q x : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ p, (if -Ynr X p ≤ x then ENNReal.ofReal (Real.exp (kap P X q * Ynr X p)) else 0)
    ∂((nuq q).prod P)

/-- Candidate `W^{(q)}(x) = κ e^{κx} G(x)` for `x > 0`, `0` for `x ≤ 0`. -/
noncomputable def Wq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (q x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else kap P X q * Real.exp (kap P X q * x) * (Gq P X q x).toReal

lemma measurable_Gq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) (q : ℝ) : Measurable (Gq P X q) := by
  have hY := measurable_Ynr hX
  have hm : Measurable fun z : ℝ × (ℝ × Ω) =>
      if -Ynr X z.2 ≤ z.1 then ENNReal.ofReal (Real.exp (kap P X q * Ynr X z.2)) else 0 :=
    Measurable.ite (measurableSet_le (hY.comp measurable_snd).neg measurable_fst)
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (hY.comp measurable_snd)))) measurable_const
  exact hm.lintegral_prod_right'

lemma Gq_ne_top {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) (x : ℝ) : Gq P X q x ≠ ⊤ := by
  haveI := nuq_finite hq
  have hκ := kap_pos 𝓕 P X hX hq
  refine ne_top_of_le_ne_top (measure_ne_top ((nuq q).prod P) Set.univ) ?_
  rw [← lintegral_one]
  refine lintegral_mono fun p => ?_
  split_ifs
  · exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos hκ.le (Ynr_nonpos hX.isSNLevy p)))
  · exact bot_le

lemma Wq_nonneg {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) (x : ℝ) : 0 ≤ Wq P X q x := by
  have hκ := kap_pos 𝓕 P X hX hq
  unfold Wq
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg hκ.le (Real.exp_pos _).le) ENNReal.toReal_nonneg

lemma measurable_Wq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) (q : ℝ) : Measurable (Wq P X q) :=
  Measurable.ite measurableSet_Iic measurable_const
    ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id))).mul
      (ENNReal.measurable_toReal.comp (measurable_Gq P hX q)))

lemma lintegral_exp_Ioi_c {a : ℝ} (ha : a < 0) (r : ℝ) :
    ∫⁻ x in Set.Ioi r, ENNReal.ofReal (Real.exp (a * x)) = ENNReal.ofReal (-Real.exp (a * r) / a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi ha r)
    (Eventually.of_forall fun x => (Real.exp_pos _).le), integral_exp_mul_Ioi ha r]

lemma level_tail {κ θ r : ℝ} (hκ : 0 < κ) (hθ : κ < θ) (hr : 0 ≤ r) :
    ∫⁻ x in Set.Ioi (0 : ℝ), (if r ≤ x then ENNReal.ofReal (κ * Real.exp ((κ - θ) * x)) else 0) =
      ENNReal.ofReal (κ * (Real.exp ((κ - θ) * r) / (θ - κ))) := by
  have h1 : ∀ x : ℝ, (if r ≤ x then ENNReal.ofReal (κ * Real.exp ((κ - θ) * x)) else 0) =
      (Set.Ici r).indicator (fun x => ENNReal.ofReal (κ * Real.exp ((κ - θ) * x))) x := by
    intro x
    simp only [Set.indicator_apply, Set.mem_Ici]
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hset : (Set.Ici r ∩ Set.Ioi 0 : Set ℝ) =ᵐ[volume] Set.Ioi r := by
    rcases eq_or_lt_of_le hr with h | h
    · have : (Set.Ici r ∩ Set.Ioi 0 : Set ℝ) = Set.Ioi r := by
        rw [← h]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
        exact ⟨fun h => h.2, fun hx => ⟨hx.le, hx⟩⟩
      rw [this]
      exact EventuallyEq.rfl
    · have : (Set.Ici r ∩ Set.Ioi 0 : Set ℝ) = Set.Ici r := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
        exact ⟨fun h => h.1, fun hx => ⟨hx, lt_of_lt_of_le h hx⟩⟩
      rw [this]
      exact Ioi_ae_eq_Ici.symm
  rw [setLIntegral_congr hset]
  simp_rw [ENNReal.ofReal_mul hκ.le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_exp_Ioi_c (by linarith : κ - θ < 0) r]
  congr 2
  rw [neg_div, ← div_neg, neg_sub]

/-- W8a: the Laplace transform of `Wq` as a Lebesgue integral. -/
theorem lintegral_laplace_Wq {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθ : kap P X q < θ) :
    ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-θ * x) * Wq P X q x) =
      ENNReal.ofReal (Shared.psi P X θ - q)⁻¹ := by
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  have hκ := kap_pos 𝓕 P X hX hq
  set κ := kap P X q with hκdef
  have hY := measurable_Ynr hXL
  -- step 1: pointwise form on `(0, ∞)`
  have hstep1 : ∀ x ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-θ * x) * Wq P X q x) =
      ∫⁻ p, (if -Ynr X p ≤ x then ENNReal.ofReal (κ * Real.exp ((κ - θ) * x)) *
        ENNReal.ofReal (Real.exp (κ * Ynr X p)) else 0) ∂((nuq q).prod P) := by
    intro x hx
    have hG := Gq_ne_top 𝓕 P X hX hq x
    unfold Wq
    rw [if_neg (not_le.mpr hx)]
    have he : Real.exp (-θ * x) * (κ * Real.exp (κ * x) * (Gq P X q x).toReal) =
        (κ * Real.exp ((κ - θ) * x)) * (Gq P X q x).toReal := by
      rw [show (κ - θ) * x = κ * x + -θ * x by ring, Real.exp_add]; ring
    rw [he, ENNReal.ofReal_mul (mul_nonneg hκ.le (Real.exp_pos _).le), ENNReal.ofReal_toReal hG,
      Gq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun p => ?_
    split_ifs <;> first | rfl | simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hstep1]
  -- step 2: Tonelli
  have hmH : Measurable fun z : ℝ × (ℝ × Ω) =>
      if -Ynr X z.2 ≤ z.1 then ENNReal.ofReal (κ * Real.exp ((κ - θ) * z.1)) *
        ENNReal.ofReal (Real.exp (κ * Ynr X z.2)) else 0 :=
    Measurable.ite (measurableSet_le (hY.comp measurable_snd).neg measurable_fst)
      ((ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul measurable_fst)))).mul
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (measurable_const.mul (hY.comp measurable_snd))))) measurable_const
  rw [lintegral_lintegral_swap hmH.aemeasurable]
  -- step 3: inner level integral
  have hstep3 : ∀ p : ℝ × Ω, ∫⁻ x in Set.Ioi (0 : ℝ), (if -Ynr X p ≤ x then
      ENNReal.ofReal (κ * Real.exp ((κ - θ) * x)) * ENNReal.ofReal (Real.exp (κ * Ynr X p))
      else 0) = ENNReal.ofReal (κ / (θ - κ)) * ENNReal.ofReal (Real.exp (θ * Ynr X p)) := by
    intro p
    have hr : 0 ≤ -Ynr X p := neg_nonneg.mpr (Ynr_nonpos hXL p)
    have h1 : ∀ x : ℝ, (if -Ynr X p ≤ x then
        ENNReal.ofReal (κ * Real.exp ((κ - θ) * x)) * ENNReal.ofReal (Real.exp (κ * Ynr X p))
        else 0) = ENNReal.ofReal (Real.exp (κ * Ynr X p)) *
          (if -Ynr X p ≤ x then ENNReal.ofReal (κ * Real.exp ((κ - θ) * x)) else 0) := by
      intro x
      split_ifs <;> simp [mul_comm]
    simp_rw [h1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, level_tail hκ hθ hr,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (div_nonneg hκ.le (by linarith))]
    congr 1
    have hexp : Real.exp (κ * Ynr X p) * Real.exp ((κ - θ) * -Ynr X p) = Real.exp (θ * Ynr X p) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (κ * Ynr X p) * (κ * (Real.exp ((κ - θ) * -Ynr X p) / (θ - κ)))
        = κ / (θ - κ) * (Real.exp (κ * Ynr X p) * Real.exp ((κ - θ) * -Ynr X p)) := by ring
      _ = κ / (θ - κ) * Real.exp (θ * Ynr X p) := by rw [hexp]
  simp_rw [hstep3]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, rho_eq_prod P hXL (by linarith) q,
    rho_eq_mgf P hXL hq (by linarith), rho_gt 𝓕 P X hX hq hθ,
    ← ENNReal.ofReal_mul (div_nonneg hκ.le (by linarith))]
  congr 1
  have hψ := psi_gt_of_kap_lt 𝓕 P X hX hq hθ
  have h1 : θ - κ ≠ 0 := by linarith
  have h2 : Shared.psi P X θ - q ≠ 0 := by linarith
  rw [← hκdef]
  field_simp

/-- W8a: integrability and value of the Laplace transform of `Wq` beyond `κ = Φ(q)`. -/
theorem laplace_Wq {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {θ : ℝ} (hθ : kap P X q < θ) :
    IntegrableOn (fun x => Real.exp (-θ * x) * Wq P X q x) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi 0, Real.exp (-θ * x) * Wq P X q x = (Shared.psi P X θ - q)⁻¹ := by
  have hψ := psi_gt_of_kap_lt 𝓕 P X hX hq hθ
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun x => Real.exp (-θ * x) * Wq P X q x :=
    Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (Wq_nonneg 𝓕 P X hX hq x)
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (-θ * x) * Wq P X q x)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (measurable_Wq P hX.isSNLevy q)).aestronglyMeasurable
  have hL := lintegral_laplace_Wq 𝓕 P X hX hq hθ
  refine ⟨⟨hmeas, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, hL]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, hL,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (by linarith))]

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-- W8b reduction: if `R` has no atoms on `(0, ∞)` under `μ = e^{-qs}ds ⊗ P`, then `Wq` is continuous
on `(0, ∞)`. -/
theorem Wq_continuousOn {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q)
    (hat : ∀ x : ℝ, 0 < x → ((nuq q).prod P) {p | -Ynr X p = x} = 0) :
    ContinuousOn (Wq P X q) (Set.Ioi 0) := by
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  have hκ := kap_pos 𝓕 P X hX hq
  have hY := measurable_Ynr hXL
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  apply ContinuousAt.continuousWithinAt
  have hGc : ContinuousAt (Gq P X q) x := by
    unfold ContinuousAt Gq
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun y => Measurable.ite (measurableSet_le hY.neg measurable_const)
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hY)))
        measurable_const)
      (Eventually.of_forall fun y => Eventually.of_forall fun p => ?_)
      (by rw [lintegral_one]; exact measure_ne_top _ _) ?_
    · split_ifs
      · exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonneg_of_nonpos hκ.le (Ynr_nonpos hXL p)))
      · exact bot_le
    · have hae : ∀ᵐ p ∂((nuq q).prod P), -Ynr X p ≠ x :=
        ae_iff.2 (by simpa only [ne_eq, not_not] using hat x hx0)
      filter_upwards [hae] with p hp
      rcases lt_or_gt_of_ne hp with hlt | hgt
      · refine tendsto_const_nhds.congr' ((eventually_gt_nhds hlt).mono fun y hy => ?_)
        exact (if_pos hlt.le).trans (if_pos hy.le).symm
      · refine tendsto_const_nhds.congr' ((eventually_lt_nhds hgt).mono fun y hy => ?_)
        exact (if_neg (not_le.mpr hgt)).trans (if_neg (not_le.mpr hy)).symm
  have hW : ∀ᶠ y in 𝓝 x, kap P X q * Real.exp (kap P X q * y) * (Gq P X q y).toReal =
      Wq P X q y :=
    (eventually_gt_nhds hx0).mono fun y hy => by
      unfold Wq
      rw [if_neg (not_le.mpr hy)]
  have hc : ContinuousAt (fun y => kap P X q * Real.exp (kap P X q * y) * (Gq P X q y).toReal) x :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt.mul
      ((ENNReal.continuousAt_toReal (Gq_ne_top 𝓕 P X hX hq x)).comp hGc)
  exact hc.congr hW

lemma tilt_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) : Shared.tilt P X 0 = Shared.psi P X := by
  funext θ
  simp [Shared.tilt, Shared.psi]

/-- G0 for `q > 0`, `v = 0`, modulo the no-atom property of the reflected resolvent. -/
theorem isScaleFun_Wq {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q)
    (hat : ∀ x : ℝ, 0 < x → ((nuq q).prod P) {p | -Ynr X p = x} = 0) :
    Shared.IsScaleFun (Shared.tilt P X 0) q (Wq P X q) := by
  rw [tilt_zero]
  refine ⟨Wq_nonneg 𝓕 P X hX hq, fun x hx => ?_, Wq_continuousOn 𝓕 P X hX hq hat, fun θ hθ => ?_⟩
  · unfold Wq
    rw [if_pos hx]
  · rw [Phi_eq_kap 𝓕 P X hX hq] at hθ
    exact laplace_Wq 𝓕 P X hX hq hθ

end Avram2004.Markov92562e40
namespace Avram2004.Markov92562e40

open Filter Topology Complex

/-- Laplace (Lerch) uniqueness for finite measures carried by `(-∞, 0]`: equal real Laplace
transforms `∫ e^{θ y}` for all `θ > 0` force equal measures. -/
theorem ext_of_laplace {ν₁ ν₂ : Measure ℝ} [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : ν₁ (Set.Ioi 0) = 0) (h₂ : ν₂ (Set.Ioi 0) = 0)
    (h : ∀ θ : ℝ, 0 < θ → ∫ y, Real.exp (θ * y) ∂ν₁ = ∫ y, Real.exp (θ * y) ∂ν₂) :
    ν₁ = ν₂ := by
  have hae : ∀ {ν : Measure ℝ}, ν (Set.Ioi 0) = 0 → ∀ᵐ y ∂ν, y ≤ 0 := fun hν =>
    ae_iff.2 (by
      rw [show {a : ℝ | ¬ a ≤ 0} = Set.Ioi 0 from by ext; simp]
      exact hν)
  have hint : ∀ {ν : Measure ℝ} [IsFiniteMeasure ν], ν (Set.Ioi 0) = 0 →
      Set.Ioi (0 : ℝ) ⊆ interior (integrableExpSet id ν) := by
    intro ν _ hν
    refine interior_maximal (fun θ hθ => ?_) isOpen_Ioi
    refine Integrable.of_bound ((Real.measurable_exp.comp
      (measurable_const.mul measurable_id)).aestronglyMeasurable) 1 ?_
    filter_upwards [hae hν] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hθ) hy)
  set U : Set ℂ := {z | 0 < z.re} with hU
  have hA : ∀ {ν : Measure ℝ} [IsFiniteMeasure ν], ν (Set.Ioi 0) = 0 →
      AnalyticOnNhd ℂ (complexMGF id ν) U := by
    intro ν _ hν
    exact analyticOnNhd_complexMGF.mono fun z hz => hint hν hz
  have hUc : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage reLm).isPreconnected
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), complexMGF id ν₁ z = complexMGF id ν₂ z := by
    rw [frequently_iff_seq_forall]
    refine ⟨fun n : ℕ => ((1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ), ?_, fun n => ?_⟩
    · rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 (1 + 0)) := by
          refine tendsto_const_nhds.add ?_
          have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
            tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
          refine (h2.inv_tendsto_atTop).congr' (Eventually.of_forall fun n => ?_)
          simp only [Pi.inv_apply, one_div]
        rw [add_zero] at this
        have := (continuous_ofReal.tendsto 1).comp this
        simpa only [Function.comp_def, Complex.ofReal_one] using this
      · refine Eventually.of_forall fun n => ?_
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq
        have h3 : (1 + 1 / ((n : ℝ) + 2) : ℝ) = 1 := by exact_mod_cast heq
        have h4 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
    · have hpos : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 2) := by positivity
      rw [complexMGF_ofReal, complexMGF_ofReal]
      congr 1
      simpa only [mgf, id] using h _ hpos
  have hEq : Set.EqOn (complexMGF id ν₁) (complexMGF id ν₂) U :=
    (hA h₁).eqOn_of_preconnected_of_frequently_eq (hA h₂) hUc h1U hfreq
  have hlim : ∀ {ν : Measure ℝ} [IsFiniteMeasure ν], ν (Set.Ioi 0) = 0 → ∀ t : ℝ,
      Tendsto (fun ε : ℝ => complexMGF id ν ((ε : ℂ) + t * I)) (𝓝[>] 0)
        (𝓝 (∫ y, cexp (t * y * I) ∂ν)) := by
    intro ν _ hν t
    simp only [complexMGF, id]
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Eventually.of_forall fun ε => (by fun_prop : Continuous fun y : ℝ =>
        cexp (((ε : ℂ) + t * I) * y)).aestronglyMeasurable) ?_ (integrable_const _) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [hae hν] with y hy
      rw [Complex.norm_exp]
      have : (((ε : ℂ) + t * I) * (y : ℂ)).re = ε * y := by simp
      rw [this]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hε) hy)
    · refine Eventually.of_forall fun y => ?_
      have hc : Continuous fun ε : ℝ => cexp (((ε : ℂ) + t * I) * y) := by fun_prop
      have h0 : cexp ((((0 : ℝ) : ℂ) + t * I) * y) = cexp (t * y * I) := by
        congr 1
        push_cast
        ring
      rw [← h0]
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real, charFun_apply_real]
  refine tendsto_nhds_unique ((hlim h₁ t).congr' ?_) (hlim h₂ t)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hEq (show (0 : ℝ) < ((ε : ℂ) + t * I).re by simpa using hε)

end Avram2004.Markov92562e40
namespace Avram2004.Markov92562e40

open Filter Topology

/-- `E_x = {(t, ω) | ∃ u < t, x < X_u ω}` on `ℝ × Ω`. -/
def Ex {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x : ℝ) : Set (ℝ × Ω) :=
  {p | ∃ u, u < Real.toNNReal p.1 ∧ x < X u p.2}

lemma measurableSet_Ex {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (x : ℝ) : MeasurableSet (Ex X x) := by
  have : Ex X x = ⋃ r : ℚ, {p : ℝ × Ω | Real.toNNReal r < Real.toNNReal p.1} ∩
      {p : ℝ × Ω | x < X (Real.toNNReal r) p.2} := by
    ext p
    simp only [Ex, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact exists_rat_hit (fun u => X u p.2) (hX.right_continuous p.2) h
    · rintro ⟨r, h1, h2⟩
      exact ⟨_, h1, h2⟩
  rw [this]
  exact MeasurableSet.iUnion fun r => (measurableSet_lt measurable_const
    (measurable_real_toNNReal.comp measurable_fst)).inter
    (measurableSet_lt measurable_const ((hX.measurable _).comp measurable_snd))

/-- `E[e^{-q τ_x}; τ_x < ∞] = e^{-κ x}` for `x > 0`. -/
lemma laplace_exp {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 ≤ q) {x : ℝ} (hx : 0 < x) :
    ∫⁻ ω in {ω | ∃ u, x < X u ω}, expPass X q x ω ∂P =
      ENNReal.ofReal (Real.exp (-(kap P X q * x))) := by
  rw [laplace_rpow 𝓕 P X hX hq hx, laplace_eq_kap 𝓕 P X hX hq,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hx.le, ← Real.exp_mul, neg_mul]

/-- The joint Wiener-Hopf identity on `ℝ × Ω` (lintegral form). -/
lemma lintegral_Ex {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 ≤ q) {x : ℝ} (hx : 0 < x) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫⁻ p in Ex X x, ENNReal.ofReal (Real.exp (θ * Ynr X p)) ∂((nuq q).prod P) =
      ENNReal.ofReal (Real.exp (-(kap P X q * x))) *
        ∫⁻ p, ENNReal.ofReal (Real.exp (θ * Ynr X p)) ∂((nuq q).prod P) := by
  have hXL := hX.isSNLevy
  have hE := measurableSet_Ex hXL x
  have hm : Measurable fun p : ℝ × Ω => ENNReal.ofReal (Real.exp (θ * Ynr X p)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_Ynr hXL)))
  rw [rho_eq_prod P hXL hθ q, ← laplace_exp 𝓕 P X hX hq hx, ← wh_resolvent 𝓕 P X hX hx.le hθ q,
    ← lintegral_indicator hE, lintegral_prod _ (hm.indicator hE).aemeasurable, nuq,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_expWeight q)
      (hm.indicator hE).lintegral_prod_right']
  refine lintegral_congr fun s => ?_
  simp only [Pi.mul_apply]
  congr 1
  have hs : MeasurableSet {ω | ∃ u, u < Real.toNNReal s ∧ x < X u ω} :=
    measurable_prodMk_left hE
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun ω => ?_
  by_cases h : ∃ u, u < Real.toNNReal s ∧ x < X u ω
  · rw [Set.indicator_of_mem (show (s, ω) ∈ Ex X x from h),
      Set.indicator_of_mem (show ω ∈ {ω | ∃ u, u < Real.toNNReal s ∧ x < X u ω} from h)]
    exact (rexpP_eq_Ynr hXL hθ (s, ω)).symm
  · rw [Set.indicator_of_notMem (show (s, ω) ∉ Ex X x from h),
      Set.indicator_of_notMem (show ω ∉ {ω | ∃ u, u < Real.toNNReal s ∧ x < X u ω} from h)]

/-- Independence form of Wiener-Hopf: `μ(E_x ∩ {Ynr ∈ B}) = e^{-κx} μ(Ynr ∈ B)`. -/
theorem law_Ex {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {x : ℝ} (hx : 0 < x) {B : Set ℝ} (hB : MeasurableSet B) :
    ((nuq q).prod P) (Ex X x ∩ Ynr X ⁻¹' B) =
      ENNReal.ofReal (Real.exp (-(kap P X q * x))) * ((nuq q).prod P) (Ynr X ⁻¹' B) := by
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  have hY := measurable_Ynr hXL
  have hE := measurableSet_Ex hXL x
  set c := ENNReal.ofReal (Real.exp (-(kap P X q * x))) with hc
  set μ := (nuq q).prod P with hμ
  have hpre : Ynr X ⁻¹' Set.Ioi 0 = ∅ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_lt]
    exact Ynr_nonpos hXL p
  haveI : IsFiniteMeasure (c • μ.map (Ynr X)) :=
    ⟨by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  have hexp : ∀ θ : ℝ, Measurable fun y : ℝ => Real.exp (θ * y) := fun θ =>
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have key : (μ.restrict (Ex X x)).map (Ynr X) = c • μ.map (Ynr X) := by
    apply ext_of_laplace
    · rw [Measure.map_apply hY measurableSet_Ioi, hpre, measure_empty]
    · rw [Measure.smul_apply, Measure.map_apply hY measurableSet_Ioi, hpre, measure_empty,
        smul_zero]
    · intro θ hθ
      rw [integral_map hY.aemeasurable (hexp θ).aestronglyMeasurable, integral_smul_measure,
        integral_map hY.aemeasurable (hexp θ).aestronglyMeasurable,
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun p => (Real.exp_pos _).le)
          ((hexp θ).comp hY).aestronglyMeasurable,
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun p => (Real.exp_pos _).le)
          ((hexp θ).comp hY).aestronglyMeasurable]
      rw [lintegral_Ex 𝓕 P X hX hq.le hx hθ.le, ENNReal.toReal_mul, hc,
        ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have h : ((μ.restrict (Ex X x)).map (Ynr X)) B = (c • μ.map (Ynr X)) B := by rw [key]
  rw [Measure.map_apply hY hB, Measure.restrict_apply (hY hB), Measure.smul_apply,
    Measure.map_apply hY hB, smul_eq_mul] at h
  rw [Set.inter_comm]
  exact h

/-- Abstract block bound: `μ((A \ B) ∩ Y) ≤ κ (b - a) μ(Y)` from the two exponential laws. -/
lemma block_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {A B Y : Set α} (hB : MeasurableSet B) (hBA : B ⊆ A) {a b κ : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hκ : 0 ≤ κ)
    (hAY : μ (A ∩ Y) = ENNReal.ofReal (Real.exp (-(κ * a))) * μ Y)
    (hBY : μ (B ∩ Y) = ENNReal.ofReal (Real.exp (-(κ * b))) * μ Y) :
    μ ((A \ B) ∩ Y) ≤ ENNReal.ofReal (κ * (b - a)) * μ Y := by
  have hsplit : μ (B ∩ Y) + μ ((A \ B) ∩ Y) = μ (A ∩ Y) := by
    have h1 : (A ∩ Y) ∩ B = B ∩ Y := by
      ext z
      simp only [Set.mem_inter_iff]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hBA h.1, h.2⟩, h.1⟩⟩
    have h2 : (A ∩ Y) \ B = (A \ B) ∩ Y := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_diff]
      tauto
    rw [← h1, ← h2]
    exact measure_inter_add_diff _ hB
  have hreal : Real.exp (-(κ * a)) ≤ Real.exp (-(κ * b)) + κ * (b - a) := by
    have h1 := Real.add_one_le_exp (-(κ * (b - a)))
    have h2 : Real.exp (-(κ * b)) = Real.exp (-(κ * a)) * Real.exp (-(κ * (b - a))) := by
      rw [← Real.exp_add]
      ring_nf
    have hE0 := (Real.exp_pos (-(κ * a))).le
    have hE1 : Real.exp (-(κ * a)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hκ ha))
    have hd : 0 ≤ κ * (b - a) := mul_nonneg hκ (sub_nonneg.mpr hab)
    have h3 : Real.exp (-(κ * a)) * (1 - Real.exp (-(κ * (b - a)))) ≤
        Real.exp (-(κ * a)) * (κ * (b - a)) :=
      mul_le_mul_of_nonneg_left (by linarith) hE0
    have h4 : Real.exp (-(κ * a)) * (κ * (b - a)) ≤ κ * (b - a) :=
      mul_le_of_le_one_left hd hE1
    rw [h2]
    nlinarith
  have hne : μ (B ∩ Y) ≠ ⊤ := measure_ne_top _ _
  refine (ENNReal.add_le_add_iff_left hne).1 ?_
  rw [hsplit, hAY, hBY, ← add_mul, ← ENNReal.ofReal_add (Real.exp_pos _).le
    (mul_nonneg hκ (sub_nonneg.mpr hab))]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) _

/-- W8c(a): the `q`-resolvent of `X` has no atom at `0`: `∫ e^{-qt} P(X_t = 0) dt = 0`. -/
theorem resolvent_atom_zero {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) :
    ((nuq q).prod P) {p | X (Real.toNNReal p.1) p.2 = 0} = 0 := by
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  have hY := measurable_Ynr hXL
  have hκ := kap_pos 𝓕 P X hX hq
  set κ := kap P X q with hκdef
  set μ := (nuq q).prod P with hμ
  set Z := {p : ℝ × Ω | X (Real.toNNReal p.1) p.2 = 0} with hZ
  -- pointwise facts on `Z`
  have hb : ∀ p : ℝ × Ω, BddAbove ((fun u => X u p.2) '' Set.Iic (Real.toNNReal p.1)) := fun p =>
    bddAbove_of_cadlag _ (hXL.right_continuous p.2) (hXL.left_limits p.2) _
  have hYZ : ∀ p ∈ Z, Ynr X p = -sSup ((fun u => X u p.2) '' Set.Iic (Real.toNNReal p.1)) := by
    intro p hp
    simp only [hZ, Set.mem_setOf_eq] at hp
    simp only [Ynr, hp, sub_zero]
  have F1 : ∀ p ∈ Z, ∀ c : ℝ, -c ≤ Ynr X p → p ∉ Ex X c := by
    intro p hp c hc ⟨u, hu, hxu⟩
    have h1 : X u p.2 ≤ sSup ((fun u => X u p.2) '' Set.Iic (Real.toNNReal p.1)) :=
      le_csSup (hb p) (Set.mem_image_of_mem _ (Set.mem_Iic.mpr hu.le))
    rw [hYZ p hp] at hc
    linarith
  have F2 : ∀ p ∈ Z, ∀ c : ℝ, 0 ≤ c → Ynr X p < -c → p ∈ Ex X c := by
    intro p hp c hc0 hc
    rw [hYZ p hp] at hc
    have hlt : c < sSup ((fun u => X u p.2) '' Set.Iic (Real.toNNReal p.1)) := by linarith
    obtain ⟨y, ⟨u, hu, rfl⟩, hy⟩ := exists_lt_of_lt_csSup
      (Set.image_nonempty.mpr ⟨_, Set.mem_Iic.mpr le_rfl⟩) hlt
    refine ⟨u, lt_of_le_of_ne (Set.mem_Iic.mp hu) fun heq => ?_, hy⟩
    have : X (Real.toNNReal p.1) p.2 = 0 := hp
    rw [heq] at hy
    linarith
  -- the bound for each `ε > 0`
  have hbound : ∀ ε : ℝ, 0 < ε →
      μ Z ≤ ENNReal.ofReal (κ * ε) * μ Set.univ + ENNReal.ofReal (κ * ε) * μ Set.univ := by
    intro ε hε
    set E' : ℕ → Set (ℝ × Ω) := fun k => if k = 0 then Set.univ else Ex X (k * ε) with hE'
    have hE'm : ∀ k, MeasurableSet (E' k) := by
      intro k
      by_cases hk : k = 0
      · simp only [hE', hk, if_true]
        exact MeasurableSet.univ
      · simp only [hE', hk, if_false]
        exact measurableSet_Ex hXL _
    have hE'law : ∀ k : ℕ, ∀ B : Set ℝ, MeasurableSet B →
        μ (E' k ∩ Ynr X ⁻¹' B) = ENNReal.ofReal (Real.exp (-(κ * (k * ε)))) * μ (Ynr X ⁻¹' B) := by
      intro k B hB
      by_cases hk : k = 0
      · simp [hE', hk]
      · simp only [hE', hk, if_false]
        exact law_Ex 𝓕 P X hX hq (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)) hε) hB
    have hsucc : ∀ k : ℕ, E' (k + 1) = Ex X ((k + 1 : ℕ) * ε) := fun k => by
      simp only [hE', Nat.succ_ne_zero, if_false]
    set Yk : ℕ → Set (ℝ × Ω) := fun k => Ynr X ⁻¹' Set.Ico (-(((k : ℝ) + 1) * ε)) (-((k : ℝ) * ε))
      with hYk
    have hcover : Z ⊆ ((Set.univ \ Ex X ε) ∩ Ynr X ⁻¹' {0}) ∪
        ⋃ k : ℕ, (E' k \ E' (k + 1)) ∩ Yk k := by
      intro p hp
      rcases eq_or_lt_of_le (Ynr_nonpos hXL p) with h0 | hneg
      · left
        refine ⟨⟨Set.mem_univ _, F1 p hp ε (by rw [h0]; linarith)⟩, ?_⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact h0
      · right
        set S := -Ynr X p with hS
        have hSpos : 0 < S / ε := div_pos (by linarith) hε
        set n := ⌈S / ε⌉₊ with hn
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hSpos).ne'
        have hle : S / ε ≤ n := Nat.le_ceil _
        have hlt : (n : ℝ) < S / ε + 1 := Nat.ceil_lt_add_one hSpos.le
        have hk : ((n - 1 : ℕ) : ℝ) = n - 1 := by
          rw [Nat.cast_sub hn1, Nat.cast_one]
        refine Set.mem_iUnion.mpr ⟨n - 1, ⟨?_, ?_⟩, ?_⟩
        · by_cases hk0 : n - 1 = 0
          · simp only [hE', hk0, if_true]
            exact Set.mem_univ _
          · simp only [hE', hk0, if_false]
            refine F2 p hp _ (mul_nonneg (Nat.cast_nonneg _) hε.le) ?_
            rw [hk]
            have : ((n : ℝ) - 1) * ε < S := by
              have := (lt_div_iff₀ hε).1 (show (n : ℝ) - 1 < S / ε by linarith)
              linarith
            linarith
        · rw [hsucc]
          refine F1 p hp _ ?_
          have hn' : ((n - 1 + 1 : ℕ) : ℝ) = n := by
            rw [Nat.sub_add_cancel hn1]
          rw [hn']
          have : S ≤ n * ε := (div_le_iff₀ hε).1 hle
          linarith
        · simp only [hYk, Set.mem_preimage, Set.mem_Ico]
          rw [hk]
          have h1 : S ≤ n * ε := (div_le_iff₀ hε).1 hle
          have h2 : ((n : ℝ) - 1) * ε < S := by
            have := (lt_div_iff₀ hε).1 (show (n : ℝ) - 1 < S / ε by linarith)
            linarith
          constructor <;> nlinarith
    have hYkm : ∀ k, MeasurableSet (Yk k) := fun k => hY measurableSet_Ico
    have hdisj : Pairwise (Function.onFun Disjoint Yk) := by
      intro i j hij
      refine Disjoint.preimage _ ?_
      rw [Set.Ico_disjoint_Ico]
      rcases lt_or_gt_of_ne hij with h | h
      · have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
        have : -((j : ℝ) * ε) ≤ -(((i : ℝ) + 1) * ε) := by nlinarith
        exact (min_le_right _ _).trans (this.trans (le_max_left _ _))
      · have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
        have : -((i : ℝ) * ε) ≤ -(((j : ℝ) + 1) * ε) := by nlinarith
        exact (min_le_left _ _).trans (this.trans (le_max_right _ _))
    have hblk : ∀ k : ℕ, μ ((E' k \ E' (k + 1)) ∩ Yk k) ≤ ENNReal.ofReal (κ * ε) * μ (Yk k) := by
      intro k
      have h := block_bound μ (hE'm (k + 1)) ?_ (mul_nonneg (Nat.cast_nonneg k) hε.le)
        (show (k : ℝ) * ε ≤ ((k + 1 : ℕ) : ℝ) * ε by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hε.le) hκ.le
        (hE'law k (Set.Ico (-(((k : ℝ) + 1) * ε)) (-((k : ℝ) * ε))) measurableSet_Ico)
        (hE'law (k + 1) (Set.Ico (-(((k : ℝ) + 1) * ε)) (-((k : ℝ) * ε))) measurableSet_Ico)
      · have : ((k + 1 : ℕ) : ℝ) * ε - (k : ℝ) * ε = ε := by push_cast; ring
        rw [this] at h
        exact h
      · intro z hz
        by_cases hk : k = 0
        · simp only [hE', hk, if_true]
          exact Set.mem_univ _
        · rw [hsucc] at hz
          simp only [hE', hk, if_false]
          obtain ⟨u, hu, hxu⟩ := hz
          refine ⟨u, hu, lt_of_le_of_lt ?_ hxu⟩
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hε.le
    have hfirst : μ ((Set.univ \ Ex X ε) ∩ Ynr X ⁻¹' {0}) ≤
        ENNReal.ofReal (κ * ε) * μ Set.univ := by
      have h := block_bound μ (measurableSet_Ex hXL ε) (Set.subset_univ _) le_rfl hε.le hκ.le
        (show μ (Set.univ ∩ Ynr X ⁻¹' {0}) = ENNReal.ofReal (Real.exp (-(κ * 0))) *
            μ (Ynr X ⁻¹' {0}) by simp)
        (law_Ex 𝓕 P X hX hq hε (measurableSet_singleton 0))
      rw [sub_zero] at h
      exact h.trans (mul_le_mul_right (measure_mono (Set.subset_univ _)) _)
    calc μ Z ≤ μ (((Set.univ \ Ex X ε) ∩ Ynr X ⁻¹' {0}) ∪
          ⋃ k : ℕ, (E' k \ E' (k + 1)) ∩ Yk k) := measure_mono hcover
      _ ≤ μ ((Set.univ \ Ex X ε) ∩ Ynr X ⁻¹' {0}) +
          ∑' k : ℕ, μ ((E' k \ E' (k + 1)) ∩ Yk k) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
      _ ≤ ENNReal.ofReal (κ * ε) * μ Set.univ + ∑' k : ℕ, ENNReal.ofReal (κ * ε) * μ (Yk k) :=
          add_le_add hfirst (ENNReal.tsum_le_tsum hblk)
      _ ≤ ENNReal.ofReal (κ * ε) * μ Set.univ + ENNReal.ofReal (κ * ε) * μ Set.univ := by
          refine add_le_add le_rfl ?_
          rw [ENNReal.tsum_mul_left, ← measure_iUnion hdisj hYkm]
          exact mul_le_mul_right (measure_mono (Set.subset_univ _)) _
  -- let `ε → 0`
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (κ * (1 / ((n : ℝ) + 1))) * μ Set.univ +
      ENNReal.ofReal (κ * (1 / ((n : ℝ) + 1))) * μ Set.univ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (κ * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal
        ((tendsto_const_nhds (x := κ)).mul tendsto_one_div_add_atTop_nhds_zero_nat)
      simpa only [mul_zero, ENNReal.ofReal_zero] using this
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr (measure_ne_top μ Set.univ))
    rw [zero_mul] at h2
    simpa only [add_zero] using h2.add h2
  exact le_antisymm (ge_of_tendsto' htend fun n => hbound (1 / ((n : ℝ) + 1)) (by positivity))
    bot_le

end Avram2004.Markov92562e40
namespace Avram2004.Markov92562e40

open Filter Topology

/-- `ω ↦ Ynr X (s, ω)` is `𝓕_s`-measurable. -/
lemma measurable_Ynr_past {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) (s : ℝ) :
    Measurable[𝓕 (Real.toNNReal s)] (fun ω => Ynr X (s, ω)) := by
  have hXL := hX.isSNLevy
  have heq : (fun ω => Ynr X (s, ω)) =
      fun ω => Real.log (rexpQ 1 (Real.toNNReal s) (fun u => X u ω)).toReal := by
    funext ω
    rw [← rexpP_eq_rexpQ 1 _ _ (hXL.right_continuous ω), rexpP_eq_Ynr hXL zero_le_one (s, ω),
      one_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
  rw [heq]
  have hm : ∀ u, u ≤ Real.toNNReal s → Measurable[𝓕 (Real.toNNReal s)] (X u) := fun u hu =>
    (hX.adapted u).mono (𝓕.mono hu) le_rfl
  refine Real.measurable_log.comp (ENNReal.measurable_toReal.comp ?_)
  unfold rexpQ
  refine Measurable.min measurable_const (Measurable.iInf fun r => ?_)
  unfold rterm
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((((hm _ r.2).sub (hm _ le_rfl)).const_mul 1).neg))

/-- Path fact: if `R_s = y` and the post-`s` increments stay below `y` up to `h`, then
`R_{s+h} = y - (f(s+h) - f s)`. -/
lemma reflect_step (f : ℝ≥0 → ℝ) (hb : ∀ t, BddAbove (f '' Set.Iic t)) {s h : ℝ≥0} {y : ℝ}
    (hs : sSup (f '' Set.Iic s) - f s = y) (hlt : ∀ u, u ≤ h → f (s + u) - f s < y) :
    sSup (f '' Set.Iic (s + h)) - f (s + h) = y - (f (s + h) - f s) := by
  suffices hS : sSup (f '' Set.Iic (s + h)) = sSup (f '' Set.Iic s) by
    rw [hS]
    linarith
  apply le_antisymm
  · refine csSup_le (Set.image_nonempty.mpr ⟨s + h, Set.mem_Iic.mpr le_rfl⟩) ?_
    rintro _ ⟨u, hu, rfl⟩
    by_cases hus : u ≤ s
    · exact le_csSup (hb s) ⟨u, Set.mem_Iic.mpr hus, rfl⟩
    · push Not at hus
      have hu1 : u = s + (u - s) := (add_tsub_cancel_of_le hus.le).symm
      have hu2 : u - s ≤ h := tsub_le_iff_left.mpr (Set.mem_Iic.mp hu)
      have h3 := hlt (u - s) hu2
      rw [← hu1] at h3
      linarith
  · exact csSup_le_csSup (hb _) (Set.image_nonempty.mpr ⟨s, Set.mem_Iic.mpr le_rfl⟩)
      (Set.image_mono (Set.Iic_subset_Iic.mpr le_self_add))

/-- Markov bound for the reflected process at two times `s < s + h`, `h < δ`. -/
theorem markov_pair {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {y : ℝ} (hy : 0 < y) (s h δ : ℝ≥0) (hhδ : h < δ) :
    P ({ω | Ynr X ((s : ℝ), ω) = -y} ∩ {ω | Ynr X (((s + h : ℝ≥0) : ℝ), ω) = -y}) ≤
      P {ω | Ynr X ((s : ℝ), ω) = -y} *
        (P {ω | X h ω = 0} + P {ω | ∃ u, u < δ ∧ y / 2 < X u ω}) := by
  have hXL := hX.isSNLevy
  set A := {ω | Ynr X ((s : ℝ), ω) = -y} with hAdef
  have hAF : MeasurableSet[𝓕 s] A := by
    have h1 := measurable_Ynr_past 𝓕 P X hX (s : ℝ)
    rw [Real.toNNReal_coe] at h1
    exact h1 (measurableSet_singleton _)
  have hAm : MeasurableSet A := 𝓕.le s _ hAF
  have hA : ∀ t, MeasurableSet[𝓕 t] (A ∩ {ω | (fun _ : Ω => s) ω ≤ t}) := by
    intro t
    by_cases hst : s ≤ t
    · have : A ∩ {ω | (fun _ : Ω => s) ω ≤ t} = A := by
        ext ω
        simp [hst]
      rw [this]
      exact 𝓕.mono hst _ hAF
    · have : A ∩ {ω | (fun _ : Ω => s) ω ≤ t} = ∅ := by
        ext ω
        simp [hst]
      rw [this]
      exact @MeasurableSet.empty Ω (𝓕 t)
  set B1 : Set (ℝ≥0 → ℝ) := {f | f h = 0} with hB1
  set B2 : Set (ℝ≥0 → ℝ) := ⋃ r : ℚ, {f | Real.toNNReal r < δ ∧ y / 2 < f (Real.toNNReal r)}
    with hB2
  have hB1m : MeasurableSet B1 := (measurable_pi_apply h) (measurableSet_singleton 0)
  have hB2m : MeasurableSet B2 := by
    refine MeasurableSet.iUnion fun r => ?_
    by_cases hr : Real.toNNReal r < δ
    · simp only [hr, true_and]
      exact measurableSet_lt measurable_const (measurable_pi_apply _)
    · simp only [hr, false_and, Set.setOf_false]
      exact MeasurableSet.empty
  have hb : ∀ ω t, BddAbove ((fun u => X u ω) '' Set.Iic t) := fun ω t =>
    bddAbove_of_cadlag _ (hXL.right_continuous ω) (hXL.left_limits ω) t
  have hsub : A ∩ {ω | Ynr X (((s + h : ℝ≥0) : ℝ), ω) = -y} ⊆
      (A ∩ {ω | (fun u => X ((fun _ : Ω => s) ω + u) ω - X ((fun _ : Ω => s) ω) ω) ∈ B1}) ∪
      (A ∩ {ω | (fun u => X ((fun _ : Ω => s) ω + u) ω - X ((fun _ : Ω => s) ω) ω) ∈ B2}) := by
    rintro ω ⟨hA1, hA2⟩
    by_cases hall : ∀ u, u ≤ h → X (s + u) ω - X s ω < y
    · left
      refine ⟨hA1, ?_⟩
      show X (s + h) ω - X s ω = 0
      have e1 : sSup ((fun u => X u ω) '' Set.Iic s) - X s ω = y := by
        have := hA1
        simp only [hAdef, Set.mem_setOf_eq, Ynr, Real.toNNReal_coe] at this
        linarith
      have e2 : sSup ((fun u => X u ω) '' Set.Iic (s + h)) - X (s + h) ω = y := by
        have := hA2
        simp only [Set.mem_setOf_eq, Ynr, Real.toNNReal_coe] at this
        linarith
      have h3 : sSup ((fun u => X u ω) '' Set.Iic (s + h)) - X (s + h) ω =
          y - (X (s + h) ω - X s ω) := reflect_step (fun u => X u ω) (hb ω) e1 hall
      linarith
    · right
      push Not at hall
      obtain ⟨u, hu, hyu⟩ := hall
      refine ⟨hA1, ?_⟩
      obtain ⟨r, hr1, hr2⟩ := exists_rat_hit (fun u => X (s + u) ω - X s ω) (post_rc hXL s ω)
        ⟨u, lt_of_le_of_lt hu hhδ, by show y / 2 < X (s + u) ω - X s ω; linarith⟩
      exact Set.mem_iUnion.mpr ⟨r, hr1, hr2⟩
  have hc : Measurable (fun _ : Ω => s) := measurable_const
  calc P (A ∩ {ω | Ynr X (((s + h : ℝ≥0) : ℝ), ω) = -y})
      ≤ P (A ∩ {ω | (fun u => X ((fun _ : Ω => s) ω + u) ω - X ((fun _ : Ω => s) ω) ω) ∈ B1}) +
        P (A ∩ {ω | (fun u => X ((fun _ : Ω => s) ω + u) ω - X ((fun _ : Ω => s) ω) ω) ∈ B2}) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = P A * P {ω | (fun u => X u ω) ∈ B1} + P A * P {ω | (fun u => X u ω) ∈ B2} := by
        rw [strongMarkov_set 𝓕 P X hX _ hc A hAm hA B1 hB1m,
          strongMarkov_set 𝓕 P X hX _ hc A hAm hA B2 hB2m]
    _ ≤ P A * (P {ω | X h ω = 0} + P {ω | ∃ u, u < δ ∧ y / 2 < X u ω}) := by
        rw [mul_add]
        refine add_le_add le_rfl (mul_le_mul_right (measure_mono ?_) _)
        intro ω hω
        obtain ⟨r, hr1, hr2⟩ := Set.mem_iUnion.mp hω
        exact ⟨_, hr1, hr2⟩

/-- `P(X_h = 0) = 0` for Lebesgue-a.e. `h > 0` (from `resolvent_atom_zero`). -/
theorem ae_atom_zero {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) :
    ∀ᵐ h ∂(volume.restrict (Set.Ioi (0 : ℝ))), P {ω | X (Real.toNNReal h) ω = 0} = 0 := by
  have hXL := hX.isSNLevy
  have h0 := resolvent_atom_zero 𝓕 P X hX one_pos
  have hj : Measurable (fun p : ℝ × Ω => X (Real.toNNReal p.1) p.2) :=
    (measurable_joint_of_rc X hXL.measurable hXL.right_continuous).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet {p : ℝ × Ω | X (Real.toNNReal p.1) p.2 = 0} :=
    hj (measurableSet_singleton 0)
  haveI := nuq_finite (q := 1) one_pos
  rw [Measure.prod_apply hS, lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)] at h0
  have h1 : ∀ᵐ x ∂(nuq 1), P (Prod.mk x ⁻¹' {p : ℝ × Ω | X (Real.toNNReal p.1) p.2 = 0}) = 0 :=
    h0
  rw [nuq, ae_withDensity_iff (measurable_expWeight 1)] at h1
  filter_upwards [h1] with x hx
  exact hx (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- `P(∃ u < 1/(n+1), c < X_u) → 0` for `c > 0`. -/
theorem tendsto_exceed_small {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => P {ω | ∃ u, u < 1 / ((n : ℝ≥0) + 1) ∧ c < X u ω}) atTop (𝓝 0) := by
  set E : ℕ → Set Ω := fun n => {ω | ∃ u, u < 1 / ((n : ℝ≥0) + 1) ∧ c < X u ω} with hE
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    measurable_prodMk_right (measurableSet_exceedBefore hX _)
  have hanti : Antitone E := by
    intro n k hnk ω ⟨u, hu, hcu⟩
    refine ⟨u, lt_of_lt_of_le hu ?_, hcu⟩
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnk 1)
  have hempty : (⋂ n, E n) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    have hev : ∀ᶠ r in 𝓝[≥] (0 : ℝ≥0), X r ω < c := by
      have h0 : (fun r => X r ω) 0 < c := by
        show X 0 ω < c
        rw [hX.start_zero ω]
        exact hc
      exact (hX.right_continuous ω 0).eventually (Iio_mem_nhds h0)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ≥0) < u from hu)
    refine ⟨n, fun ⟨v, hv, hcv⟩ => ?_⟩
    have := hsub ⟨bot_le, lt_trans hv hn⟩
    exact absurd hcv (not_lt.mpr (le_of_lt this))
  have h := tendsto_measure_iInter_atTop (μ := P) (fun n => (hEm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at h
  exact h

end Avram2004.Markov92562e40
namespace Avram2004.Markov92562e40

open Filter Topology

/-- One-sided Lebesgue density along `δ_n = 1/(n+1)`: for a.e. `s`,
`(n+1) λ(A ∩ (s, s + δ_n]) → 1_A(s)`. -/
theorem density_tendsto {A : Set ℝ} (hA : MeasurableSet A) :
    ∀ᵐ s, Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) + 1) *
        volume (A ∩ Set.Ioc s (s + 1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (A.indicator (fun _ => (1 : ℝ≥0∞)) s)) := by
  set f : ℝ → ℝ := A.indicator (fun _ => (1 : ℝ)) with hfdef
  have hf : LocallyIntegrable f volume := (locallyIntegrable_const (1 : ℝ)).indicator hA
  have hII : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    (hf.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc |>
      fun h => (intervalIntegrable_iff.mpr h)
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf] with s hs
  have hd := hasDerivAt_iff_tendsto_slope.mp (hs 0)
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδ
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hseq : Tendsto (fun n => s + δ n) atTop (𝓝[≠] s) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (tendsto_const_nhds (x := s)).add tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [add_zero] using this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have := hδpos n
      intro h
      linarith
  have hlim := hd.comp hseq
  have hval : ∀ n, (slope (fun x => ∫ t in (0 : ℝ)..x, f t) s ∘ fun n => s + δ n) n =
      ((n : ℝ) + 1) * (volume (A ∩ Set.Ioc s (s + δ n))).toReal := by
    intro n
    simp only [Function.comp_apply, slope_def_field]
    have h1 : (∫ t in (0 : ℝ)..s + δ n, f t) - ∫ t in (0 : ℝ)..s, f t =
        ∫ t in s..s + δ n, f t :=
      intervalIntegral.integral_interval_sub_left (hII _ _) (hII _ _)
    have h2 : ∫ t in s..s + δ n, f t = (volume (A ∩ Set.Ioc s (s + δ n))).toReal := by
      rw [intervalIntegral.integral_of_le (by linarith [hδpos n]), hfdef,
        integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one,
        Measure.real, Measure.restrict_apply' measurableSet_Ioc]
    rw [h1, h2, add_sub_cancel_left]
    have : δ n = 1 / ((n : ℝ) + 1) := rfl
    rw [this, div_eq_mul_inv, one_div, inv_inv, mul_comm]
  have hlim' : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * (volume (A ∩ Set.Ioc s (s + δ n))).toReal)
      atTop (𝓝 (f s)) := hlim.congr hval
  have hlim'' := ENNReal.tendsto_ofReal hlim'
  have hfs : ENNReal.ofReal (f s) = A.indicator (fun _ => (1 : ℝ≥0∞)) s := by
    by_cases h : s ∈ A
    · simp [hfdef, h]
    · simp [hfdef, h]
  rw [hfs] at hlim''
  refine hlim''.congr fun n => ?_
  have hne : volume (A ∩ Set.Ioc s (s + δ n)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measure_mono Set.inter_subset_right)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hne]

end Avram2004.Markov92562e40
namespace Avram2004.Markov92562e40

open Filter Topology

/-- Translation of a lintegral over `(s, s + δ]` to `(0, δ]`. -/
lemma lintegral_Ioc_shift (f : ℝ → ℝ≥0∞) (s δ : ℝ) :
    ∫⁻ t in Set.Ioc s (s + δ), f t = ∫⁻ h in Set.Ioc 0 δ, f (s + h) := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
    ← lintegral_add_right_eq_self (μ := (volume : Measure ℝ)) _ s]
  refine lintegral_congr fun h => ?_
  have hiff : h + s ∈ Set.Ioc s (s + δ) ↔ h ∈ Set.Ioc 0 δ := by
    simp only [Set.mem_Ioc]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨a, b⟩
      exact ⟨by linarith, by linarith⟩
  by_cases hh : h ∈ Set.Ioc 0 δ
  · rw [Set.indicator_of_mem (hiff.2 hh), Set.indicator_of_mem hh, add_comm]
  · rw [Set.indicator_of_notMem (fun h' => hh (hiff.1 h')), Set.indicator_of_notMem hh]

/-- Two-time bound for the reflected process at a level `y > 0`, with `h ∈ (0, 1/(2n+2)]`. -/
lemma pair_bound {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {y : ℝ} (hy : 0 < y) (n : ℕ) {s h : ℝ} (hs : 0 < s)
    (hh : h ∈ Set.Ioc 0 (1 / (((2 * n + 1 : ℕ) : ℝ) + 1)))
    (h0 : P {ω | X (Real.toNNReal h) ω = 0} = 0) :
    P ({ω | Ynr X (s, ω) = -y} ∩ {ω | Ynr X (s + h, ω) = -y}) ≤
      P {ω | ∃ u, u < 1 / ((n : ℝ≥0) + 1) ∧ y / 2 < X u ω} := by
  have hδ : Real.toNNReal h < 1 / ((n : ℝ≥0) + 1) := by
    have h2 : 1 / (((2 * n + 1 : ℕ) : ℝ) + 1) < 1 / ((n : ℝ) + 1) :=
      one_div_lt_one_div_of_lt (by positivity)
        (by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have h3 : ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) = 1 / ((n : ℝ) + 1) := by
      rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    rw [Real.toNNReal_lt_iff_lt_coe hh.1.le, h3]
    exact lt_of_le_of_lt hh.2 h2
  have hM := markov_pair 𝓕 P X hX hy (Real.toNNReal s) (Real.toNNReal h) _ hδ
  have e1 : ((Real.toNNReal s : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.le
  have e2 : ((Real.toNNReal s + Real.toNNReal h : ℝ≥0) : ℝ) = s + h := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hs.le, Real.coe_toNNReal _ hh.1.le]
  rw [e2, e1, h0, zero_add] at hM
  calc _ ≤ _ := hM
    _ ≤ 1 * P {ω | ∃ u, u < 1 / ((n : ℝ≥0) + 1) ∧ y / 2 < X u ω} := by
        gcongr
        exact prob_le_one
    _ = _ := one_mul _

/-- W8c(b): the reflected `q`-resolvent has no atoms on `(0, ∞)`. -/
theorem hat {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) :
    ∀ x : ℝ, 0 < x → ((nuq q).prod P) {p | -Ynr X p = x} = 0 := by
  intro y hy
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  set D : Set (ℝ × Ω) := {p | Ynr X p = -y} with hDdef
  have hDeq : {p : ℝ × Ω | -Ynr X p = y} = D := by
    ext p
    simp only [hDdef, Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hDeq]
  have hD : MeasurableSet D := measurable_Ynr hXL (measurableSet_singleton _)
  have h1m : Measurable (D.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hD
  set δ : ℕ → ℝ := fun n => 1 / (((2 * n + 1 : ℕ) : ℝ) + 1) with hδdef
  set c : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (((2 * n + 1 : ℕ) : ℝ) + 1) with hcdef
  set fJ : (ℝ × Ω) × ℝ → ℝ≥0∞ := fun z =>
    D.indicator (fun _ => (1 : ℝ≥0∞)) z.1 * D.indicator (fun _ => (1 : ℝ≥0∞)) (z.1.1 + z.2, z.1.2)
    with hfJdef
  have hJ : Measurable fJ :=
    (h1m.comp measurable_fst).mul
      (h1m.comp ((measurable_fst.fst.add measurable_snd).prodMk measurable_fst.snd))
  set G : ℕ → ℝ × Ω → ℝ≥0∞ := fun n p => c n * ∫⁻ h in Set.Ioc 0 (δ n), fJ (p, h) with hGdef
  have hGm : ∀ n, Measurable (G n) := fun n => (hJ.lintegral_prod_right').const_mul _
  set e : ℕ → ℝ≥0∞ := fun n => P {ω | ∃ u, u < 1 / ((n : ℝ≥0) + 1) ∧ y / 2 < X u ω} with hedef
  have hac0 : nuq q ≪ volume.restrict (Set.Ioi (0 : ℝ)) := withDensity_absolutelyContinuous _ _
  have hac : nuq q ≪ volume :=
    hac0.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hk : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => (by omega : n ≤ 2 * n + 1)) tendsto_id
  -- the product indicator integrates to the two-time probability
  have hprodInd : ∀ s h : ℝ, ∫⁻ ω, fJ ((s, ω), h) ∂P =
      P ({ω | Ynr X (s, ω) = -y} ∩ {ω | Ynr X (s + h, ω) = -y}) := by
    intro s h
    have hm : MeasurableSet ({ω | Ynr X (s, ω) = -y} ∩ {ω | Ynr X (s + h, ω) = -y}) :=
      ((measurable_const.prodMk measurable_id) hD).inter
        ((measurable_const.prodMk measurable_id) hD)
    calc ∫⁻ ω, fJ ((s, ω), h) ∂P
        = ∫⁻ ω, ({ω | Ynr X (s, ω) = -y} ∩ {ω | Ynr X (s + h, ω) = -y}).indicator
            (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
          refine lintegral_congr fun ω => ?_
          show D.indicator (fun _ => (1 : ℝ≥0∞)) (s, ω) *
            D.indicator (fun _ => (1 : ℝ≥0∞)) (s + h, ω) = _
          by_cases ha : (s, ω) ∈ D
          · by_cases hb : (s + h, ω) ∈ D
            · rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb,
                Set.indicator_of_mem (show ω ∈ {ω | Ynr X (s, ω) = -y} ∩
                  {ω | Ynr X (s + h, ω) = -y} from ⟨ha, hb⟩), one_mul]
            · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (show ω ∉
                {ω | Ynr X (s, ω) = -y} ∩ {ω | Ynr X (s + h, ω) = -y} from fun h' => hb h'.2),
                mul_zero]
          · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (show ω ∉
              {ω | Ynr X (s, ω) = -y} ∩ {ω | Ynr X (s + h, ω) = -y} from fun h' => ha h'.1),
              zero_mul]
      _ = _ := by rw [lintegral_indicator_const hm, one_mul]
  -- step 1: Fatou in `s` along the density sequence
  have hpt : ∀ ω, nuq q ((fun s => (s, ω)) ⁻¹' D) ≤
      liminf (fun n => ∫⁻ s, G n (s, ω) ∂(nuq q)) atTop := by
    intro ω
    set S := (fun s => (s, ω)) ⁻¹' D with hSdef
    have hS : MeasurableSet S := (measurable_id.prodMk measurable_const) hD
    have hind : ∀ t, D.indicator (fun _ => (1 : ℝ≥0∞)) (t, ω) = S.indicator (fun _ => 1) t := by
      intro t
      by_cases ht : (t, ω) ∈ D
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ S from ht)]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ S from ht)]
    calc nuq q S = ∫⁻ s, S.indicator (fun _ => (1 : ℝ≥0∞)) s ∂(nuq q) := by
          rw [lintegral_indicator_const hS, one_mul]
      _ ≤ ∫⁻ s, liminf (fun n => G n (s, ω)) atTop ∂(nuq q) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hac.ae_le (density_tendsto hS)] with s hs
          by_cases hsS : s ∈ S
          · have hlim : Tendsto (fun n => G n (s, ω)) atTop (𝓝 1) := by
              have h2 := hs.comp hk
              rw [Set.indicator_of_mem hsS] at h2
              refine h2.congr fun n => ?_
              show c n * volume (S ∩ Set.Ioc s (s + δ n)) = c n * ∫⁻ h in Set.Ioc 0 (δ n), fJ ((s, ω), h)
              congr 1
              rw [show volume (S ∩ Set.Ioc s (s + δ n)) =
                  ∫⁻ t in Set.Ioc s (s + δ n), S.indicator (fun _ => (1 : ℝ≥0∞)) t by
                    rw [lintegral_indicator_const hS, one_mul, Measure.restrict_apply hS],
                lintegral_Ioc_shift]
              refine lintegral_congr fun h => ?_
              show S.indicator (fun _ => (1 : ℝ≥0∞)) (s + h) =
                D.indicator (fun _ => (1 : ℝ≥0∞)) (s, ω) * D.indicator (fun _ => (1 : ℝ≥0∞)) (s + h, ω)
              rw [Set.indicator_of_mem (show (s, ω) ∈ D from hsS), one_mul, hind]
            rw [Set.indicator_of_mem hsS, hlim.liminf_eq]
          · rw [Set.indicator_of_notMem hsS]
            exact zero_le
      _ ≤ liminf (fun n => ∫⁻ s, G n (s, ω) ∂(nuq q)) atTop :=
          lintegral_liminf_le fun n => (hGm n).comp (measurable_id.prodMk measurable_const)
  -- step 2: Tonelli + the two-time bound
  have hatom := ae_atom_zero 𝓕 P X hX
  have hC : ∀ n, ∫⁻ ω, ∫⁻ s, G n (s, ω) ∂(nuq q) ∂P ≤ e n * nuq q Set.univ := by
    intro n
    have hcδ : c n * ENNReal.ofReal (δ n) = 1 := by
      rw [hcdef, hδdef]
      simp only
      rw [← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel (by positivity),
        ENNReal.ofReal_one]
    calc ∫⁻ ω, ∫⁻ s, G n (s, ω) ∂(nuq q) ∂P = ∫⁻ s, ∫⁻ ω, G n (s, ω) ∂P ∂(nuq q) :=
          lintegral_lintegral_swap ((hGm n).comp measurable_swap).aemeasurable
      _ ≤ ∫⁻ _s, e n ∂(nuq q) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hac0.ae_le (ae_restrict_mem measurableSet_Ioi)] with s hs
          have hs0 : (0 : ℝ) < s := hs
          have hmeas : Measurable (fun ω => ∫⁻ h in Set.Ioc 0 (δ n), fJ ((s, ω), h)) :=
            hJ.lintegral_prod_right'.comp (measurable_const.prodMk measurable_id)
          calc ∫⁻ ω, G n (s, ω) ∂P
              = c n * ∫⁻ ω, (∫⁻ h in Set.Ioc 0 (δ n), fJ ((s, ω), h)) ∂P :=
                lintegral_const_mul _ hmeas
            _ = c n * ∫⁻ h in Set.Ioc 0 (δ n), (∫⁻ ω, fJ ((s, ω), h) ∂P) := by
                rw [lintegral_lintegral_swap (f := fun ω h => fJ ((s, ω), h)) (hJ.comp
                  ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).aemeasurable]
            _ ≤ c n * ∫⁻ _h in Set.Ioc 0 (δ n), e n := by
                refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
                filter_upwards [ae_restrict_mem measurableSet_Ioc,
                  ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Ioi_self hatom] with h hI h0
                rw [hprodInd s h]
                exact pair_bound 𝓕 P X hX hy n hs0 hI h0
            _ = e n := by
                rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
                  Real.volume_Ioc, sub_zero, mul_left_comm, hcδ, mul_one]
      _ = e n * nuq q Set.univ := lintegral_const _
  -- step 3: Fatou in `ω` and the limit
  have hlim0 : Tendsto (fun n => e n * nuq q Set.univ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const (tendsto_exceed_small P hXL (half_pos hy))
      (Or.inr (measure_ne_top (nuq q) Set.univ))
    simpa only [zero_mul] using this
  rw [Measure.prod_apply_symm hD]
  refine le_antisymm ?_ zero_le
  calc ∫⁻ ω, nuq q ((fun s => (s, ω)) ⁻¹' D) ∂P
      ≤ ∫⁻ ω, liminf (fun n => ∫⁻ s, G n (s, ω) ∂(nuq q)) atTop ∂P := lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ ω, ∫⁻ s, G n (s, ω) ∂(nuq q) ∂P) atTop :=
        lintegral_liminf_le fun n => (hGm n).lintegral_prod_left'
    _ ≤ liminf (fun n => e n * nuq q Set.univ) atTop :=
        liminf_le_liminf (Eventually.of_forall hC)
    _ = 0 := hlim0.liminf_eq

/-- G0 for `q > 0`, `v = 0`, unconditionally. -/
theorem isScaleFun_Wq' {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) :
    Shared.IsScaleFun (Shared.tilt P X 0) q (Wq P X q) :=
  isScaleFun_Wq 𝓕 P X hX hq (hat 𝓕 P X hX hq)

end Avram2004.Markov92562e40
namespace Avram2004.Markov92562e40

open Filter Topology

/-- Data of a scale function as a finite measure on `(-∞, 0)` (for Laplace uniqueness). -/
lemma scaleFun_measure {φ : ℝ → ℝ} {q : ℝ} {W : ℝ → ℝ} (hW : Shared.IsScaleFun φ q W)
    {θ0 : ℝ} (hθ0 : Shared.Phi φ q < θ0) :
    IsFiniteMeasure (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-θ0 * x) * W x))).map Neg.neg) ∧
      (((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-θ0 * x) * W x))).map Neg.neg) (Set.Ioi 0) = 0 ∧
      ∀ θ : ℝ, 0 < θ → ∫ y, Real.exp (θ * y) ∂(((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-θ0 * x) * W x))).map Neg.neg) = (φ (θ + θ0) - q)⁻¹ := by
  set μ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-θ0 * x) * W x)) with hμ
  have hint := (hW.2.2.2 θ0 hθ0).1
  have hWm : AEMeasurable W (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hW.2.2.1.aemeasurable measurableSet_Ioi
  have hgm : AEMeasurable (fun x => ENNReal.ofReal (Real.exp (-θ0 * x) * W x))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).aemeasurable.mul hWm)
  have hfin : IsFiniteMeasure μ := isFiniteMeasure_withDensity hint.lintegral_lt_top.ne
  refine ⟨inferInstance, ?_, fun θ hθ => ?_⟩
  · rw [Measure.map_apply measurable_neg measurableSet_Ioi]
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Ioi 0 = Set.Iio 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, neg_pos]
    rw [hpre]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply measurableSet_Iio, Set.Iio_inter_Ioi, Set.Ioo_self, measure_empty]
  · rw [integral_map measurable_neg.aemeasurable
      (f := fun y => Real.exp (θ * y))
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable,
      hμ, integral_withDensity_eq_integral_toReal_smul₀ hgm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have h2 := (hW.2.2.2 (θ + θ0) (by linarith)).2
    rw [← h2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (ENNReal.ofReal (Real.exp (-θ0 * x) * W x)).toReal • Real.exp (θ * -x) =
      Real.exp (-(θ + θ0) * x) * W x
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le (hW.1 x)), smul_eq_mul]
    have : -(θ + θ0) * x = -θ0 * x + θ * -x := by ring
    rw [this, Real.exp_add]
    ring

/-- Scale functions are unique (Laplace uniqueness + continuity on `(0, ∞)`). -/
theorem isScaleFun_unique {φ : ℝ → ℝ} {q : ℝ} {W₁ W₂ : ℝ → ℝ}
    (h₁ : Shared.IsScaleFun φ q W₁) (h₂ : Shared.IsScaleFun φ q W₂) : W₁ = W₂ := by
  have hθ0 : Shared.Phi φ q < Shared.Phi φ q + 1 := by linarith
  obtain ⟨hf₁, hs₁, hl₁⟩ := scaleFun_measure h₁ hθ0
  obtain ⟨hf₂, hs₂, hl₂⟩ := scaleFun_measure h₂ hθ0
  set θ0 := Shared.Phi φ q + 1
  have hν := ext_of_laplace hs₁ hs₂ fun θ hθ => (hl₁ θ hθ).trans (hl₂ θ hθ).symm
  have hinv : ∀ μ : Measure ℝ, (μ.map Neg.neg).map Neg.neg = μ := fun μ => by
    rw [Measure.map_map measurable_neg measurable_neg, neg_involutive.comp_self, Measure.map_id]
  have hμ := congrArg (fun ν : Measure ℝ => ν.map Neg.neg) hν
  simp only [hinv] at hμ
  have hm : ∀ W : ℝ → ℝ, Shared.IsScaleFun φ q W →
      AEMeasurable (fun x => ENNReal.ofReal (Real.exp (-θ0 * x) * W x))
        (volume.restrict (Set.Ioi (0 : ℝ))) := fun W hW =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).aemeasurable.mul
        (hW.2.2.1.aemeasurable measurableSet_Ioi))
  rw [withDensity_eq_iff (hm W₁ h₁) (hm W₂ h₂)
    ((h₁.2.2.2 θ0 hθ0).1.lintegral_lt_top.ne)] at hμ
  have hae : W₁ =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] W₂ := by
    filter_upwards [hμ] with x hx
    rw [ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (Real.exp_pos _).le (h₁.1 x))
      (mul_nonneg (Real.exp_pos _).le (h₂.1 x))] at hx
    exact mul_left_cancel₀ (Real.exp_pos _).ne' hx
  have hEq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi h₁.2.2.1 h₂.2.2.1
  funext x
  by_cases hx : x ≤ 0
  · rw [h₁.2.1 x hx, h₂.2.1 x hx]
  · exact hEq (show x ∈ Set.Ioi 0 from lt_of_not_ge hx)

/-- For `q > 0` the family's `W^{(q)}` (`Shared.W P X 0 q`) is the constructed `Wq`. -/
theorem W_eq_Wq {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) : Shared.W P X 0 q = Wq P X q := by
  have h := isScaleFun_Wq' 𝓕 P X hX hq
  have hex : ∃ W, Shared.IsScaleFun (Shared.tilt P X 0) q W := ⟨_, h⟩
  have hW : Shared.W P X 0 q = Shared.scaleFun (Shared.tilt P X 0) q := by
    funext x
    simp [Shared.W, Shared.scaleFunExt, hq.le]
  rw [hW]
  unfold Shared.scaleFun
  rw [dif_pos hex]
  exact isScaleFun_unique hex.choose_spec h

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

/-- Esscher density at time `t`. -/
noncomputable def essD {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (r : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (X t ω - r * (t : ℝ)))

lemma measurable_essD {Ω : Type*} [MeasurableSpace Ω] {X : ℝ≥0 → Ω → ℝ}
    (hXm : ∀ t, Measurable (X t)) (r : ℝ) (t : ℝ≥0) : Measurable (essD X r t) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hXm t).sub_const _))

lemma meas_ind_one {Ω : Type*} {M : MeasurableSpace Ω} {S : Set Ω} (hS : MeasurableSet[M] S) :
    Measurable[M] (S.indicator (1 : Ω → ℝ≥0∞)) :=
  measurable_const.indicator hS

/-- E1a: `E_Q f = E_P[e^{X_t - rt} f]` for `𝓕_t`-measurable `f ≥ 0`. -/
lemma esscher_lintegral {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {r : ℝ} (hQ : Shared.IsEsscher 𝓕 P Q X r)
    (hXm : ∀ t, Measurable (X t)) (t : ℝ≥0) {f : Ω → ℝ≥0∞} (hf : Measurable[𝓕 t] f) :
    ∫⁻ ω, f ω ∂Q = ∫⁻ ω, essD X r t ω * f ω ∂P := by
  rw [← lintegral_trim (𝓕.le t) hf, hQ t, lintegral_trim (𝓕.le t) hf]
  exact lintegral_withDensity_eq_lintegral_mul _ (measurable_essD hXm r t) (hf.mono (𝓕.le t) le_rfl)

lemma esscher_one {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (hXm : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    ∫⁻ ω, essD X r t ω ∂P = 1 := by
  have h := esscher_lintegral hQ hXm t (f := fun _ => 1) measurable_const
  rw [lintegral_const, measure_univ, one_mul] at h
  simpa only [mul_one] using h.symm

/-- Product split of the Esscher density over an `𝓕_s` event and a post-`s` increment event. -/
lemma esscher_split {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r) (s t : ℝ≥0)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) {C : Set ℝ} (hC : MeasurableSet C) :
    Q (A ∩ (fun ω => X (s + t) ω - X s ω) ⁻¹' C) =
      Q A * ∫⁻ ω, C.indicator (fun z => ENNReal.ofReal (Real.exp (z - r * (t : ℝ))))
        (X (s + t) ω - X s ω) ∂P := by
  have hXm := hX.isSNLevy.measurable
  have hadm : ∀ u v : ℝ≥0, u ≤ v → Measurable[𝓕 v] (X u) := fun u v huv =>
    (hX.adapted u).mono (𝓕.mono huv) le_rfl
  set Δ : Ω → ℝ := fun ω => X (s + t) ω - X s ω with hΔ
  have hΔm : Measurable[𝓕 (s + t)] Δ :=
    (hadm _ _ le_rfl).sub (hadm _ _ le_self_add)
  have hAB : MeasurableSet[𝓕 (s + t)] (A ∩ Δ ⁻¹' C) :=
    (𝓕.mono le_self_add _ hA).inter (hΔm hC)
  set φ : ℝ → ℝ≥0∞ := C.indicator (fun z => ENNReal.ofReal (Real.exp (z - r * (t : ℝ)))) with hφ
  have hφm : Measurable φ :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_id.sub_const _))).indicator hC
  have h1 : Q (A ∩ Δ ⁻¹' C) = ∫⁻ ω, (A ∩ Δ ⁻¹' C).indicator 1 ω ∂Q :=
    (lintegral_indicator_one (𝓕.le _ _ hAB)).symm
  have h2 : ∀ ω, essD X r (s + t) ω * (A ∩ Δ ⁻¹' C).indicator 1 ω =
      (essD X r s ω * A.indicator 1 ω) * φ (Δ ω) := by
    intro ω
    have hexp : essD X r (s + t) ω =
        essD X r s ω * ENNReal.ofReal (Real.exp (Δ ω - r * (t : ℝ))) := by
      simp only [essD, hΔ]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      push_cast
      ring
    by_cases ha : ω ∈ A
    · by_cases hc : Δ ω ∈ C
      · rw [Set.indicator_of_mem (show ω ∈ A ∩ Δ ⁻¹' C from ⟨ha, hc⟩), Set.indicator_of_mem ha,
          hφ, Set.indicator_of_mem hc, hexp]
        simp only [Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem (show ω ∉ A ∩ Δ ⁻¹' C from fun h => hc h.2), hφ,
          Set.indicator_of_notMem hc]
        simp
    · rw [Set.indicator_of_notMem (show ω ∉ A ∩ Δ ⁻¹' C from fun h => ha h.1),
        Set.indicator_of_notMem ha]
      simp
  have hind : Indep (𝓕 s) (MeasurableSpace.comap Δ (inferInstance : MeasurableSpace ℝ)) P :=
    (hX.indep_past s t).symm
  have hf1 : Measurable[𝓕 s] (fun ω => essD X r s ω * A.indicator 1 ω) := by
    refine Measurable.mul ?_ (meas_ind_one hA)
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hadm s s le_rfl).sub_const _))
  have hf2 : Measurable[MeasurableSpace.comap Δ (inferInstance : MeasurableSpace ℝ)]
      (fun ω => φ (Δ ω)) := hφm.comp (comap_measurable Δ)
  have hΔP : Measurable Δ := (hXm _).sub (hXm _)
  rw [h1, esscher_lintegral hQ hXm (s + t) (meas_ind_one hAB)]
  simp_rw [h2]
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace (𝓕.le s)
    hΔP.comap_le hind hf1 hf2]
  congr 1
  rw [← esscher_lintegral hQ hXm s (meas_ind_one hA), lintegral_indicator_one (𝓕.le _ _ hA)]

/-- E1b: under the Esscher measure the post-`s` increments are independent of `𝓕_s`. -/
theorem esscher_indep_past {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r) (s t : ℝ≥0) :
    Indep (MeasurableSpace.comap (fun ω => X (s + t) ω - X s ω) (inferInstance : MeasurableSpace ℝ))
      (𝓕 s) Q := by
  rw [Indep_iff]
  rintro B A ⟨C, hC, rfl⟩ hA
  rw [Set.inter_comm, esscher_split hX hQ s t hA hC]
  have hU := esscher_split hX hQ s t (A := Set.univ) MeasurableSet.univ hC
  rw [Set.univ_inter, measure_univ, one_mul] at hU
  rw [hU, mul_comm]

/-- E1c: under the Esscher measure the increments are stationary. -/
theorem esscher_stationary {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r) (s t : ℝ≥0) :
    IdentDistrib (fun ω => X (s + t) ω - X s ω) (X t) Q Q := by
  have hXm := hX.isSNLevy.measurable
  have hΔP : Measurable (fun ω => X (s + t) ω - X s ω) := (hXm _).sub (hXm _)
  refine ⟨hΔP.aemeasurable, (hXm t).aemeasurable, ?_⟩
  ext C hC
  rw [Measure.map_apply hΔP hC, Measure.map_apply (hXm t) hC]
  have hU := esscher_split hX hQ s t (A := Set.univ) MeasurableSet.univ hC
  rw [Set.univ_inter, measure_univ, one_mul] at hU
  rw [hU]
  set φ : ℝ → ℝ≥0∞ := C.indicator (fun z => ENNReal.ofReal (Real.exp (z - r * (t : ℝ)))) with hφ
  have hφm : Measurable φ :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_id.sub_const _))).indicator hC
  have hst := hX.isSNLevy.stationary_increments s t
  rw [← lintegral_map hφm hΔP, hst.map_eq, lintegral_map hφm (hXm t)]
  have hadm : Measurable[𝓕 t] (X t) := hX.adapted t
  rw [← lintegral_indicator_one ((hXm t) hC),
    esscher_lintegral hQ hXm t (meas_ind_one (hadm hC))]
  refine lintegral_congr fun ω => ?_
  by_cases hc : X t ω ∈ C
  · rw [hφ, Set.indicator_of_mem hc, Set.indicator_of_mem (show ω ∈ X t ⁻¹' C from hc)]
    simp [essD]
  · rw [hφ, Set.indicator_of_notMem hc, Set.indicator_of_notMem (show ω ∉ X t ⁻¹' C from hc)]
    simp

/-- Independence of increments from a filtration gives `iIndepFun` of the increments. -/
lemma iIndepFun_of_filtration {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {Q : Measure Ω} [IsProbabilityMeasure Q] {n : ℕ} (Y : Fin n → Ω → ℝ) (τ : Fin (n + 1) → ℝ≥0)
    (hτ : Monotone τ) (hYm : ∀ i, Measurable[𝓕 (τ i.succ)] (Y i))
    (hYi : ∀ i, Indep (MeasurableSpace.comap (Y i) (inferInstance : MeasurableSpace ℝ))
      (𝓕 (τ i.castSucc)) Q) :
    iIndepFun Y Q := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  have key : ∀ k, k ≤ n → Q (⋂ i ∈ S.filter (fun i => i.val < k), Y i ⁻¹' sets i) =
      ∏ i ∈ S.filter (fun i => i.val < k), Q (Y i ⁻¹' sets i) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ih' := ih (Nat.le_of_succ_le hk)
      set i0 : Fin n := ⟨k, hk⟩ with hi0def
      by_cases hi0 : i0 ∈ S
      · have hF : S.filter (fun i => i.val < k + 1) = insert i0 (S.filter (fun i => i.val < k)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hiS, hik⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hik with h | h
            · exact Or.inr ⟨hiS, h⟩
            · exact Or.inl (Fin.ext h)
          · rintro (rfl | ⟨hiS, hik⟩)
            · exact ⟨hi0, Nat.lt_succ_self k⟩
            · exact ⟨hiS, Nat.lt_succ_of_lt hik⟩
        have hnot : i0 ∉ S.filter (fun i => i.val < k) := by simp [i0]
        rw [hF, Finset.prod_insert hnot, Finset.set_biInter_insert, ← ih']
        have hA : MeasurableSet[𝓕 (τ i0.castSucc)]
            (⋂ i ∈ S.filter (fun i => i.val < k), Y i ⁻¹' sets i) := by
          refine Finset.measurableSet_biInter _ fun i hi => ?_
          have hik : i.val < k := (Finset.mem_filter.1 hi).2
          have hle : τ i.succ ≤ τ i0.castSucc := hτ (by rw [Fin.le_iff_val_le_val]; simp [i0]; omega)
          exact 𝓕.mono hle _ (hYm i (hsets i (Finset.mem_filter.1 hi).1))
        exact (Indep_iff _ _ Q).1 (hYi i0) _ _ ⟨sets i0, hsets i0 hi0, rfl⟩ hA
      · have hF : S.filter (fun i => i.val < k + 1) = S.filter (fun i => i.val < k) := by
          ext i
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hiS, hik⟩
            refine ⟨hiS, lt_of_le_of_ne (Nat.lt_succ_iff.1 hik) fun h => hi0 ?_⟩
            have : i = i0 := Fin.ext h
            exact this ▸ hiS
          · rintro ⟨hiS, hik⟩
            exact ⟨hiS, Nat.lt_succ_of_lt hik⟩
        rw [hF]
        exact ih'
  have hS : S.filter (fun i => i.val < n) = S := Finset.filter_true_of_mem fun i _ => i.isLt
  simpa [hS] using key n le_rfl

/-- E1d: independent increments under the Esscher measure. -/
theorem esscher_indepIncrements {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r) :
    HasIndepIncrements X Q := by
  intro n t ht
  have hadm : ∀ u v : ℝ≥0, u ≤ v → Measurable[𝓕 v] (X u) := fun u v huv =>
    (hX.adapted u).mono (𝓕.mono huv) le_rfl
  refine iIndepFun_of_filtration (𝓕 := 𝓕) _ t ht (fun i => ?_) (fun i => ?_)
  · exact (hadm _ _ le_rfl).sub (hadm _ _ (ht (by rw [Fin.le_iff_val_le_val]; simp)))
  · have h := esscher_indep_past hX hQ (t i.castSucc) (t i.succ - t i.castSucc)
    rwa [add_tsub_cancel_of_le (ht (by rw [Fin.le_iff_val_le_val]; simp))] at h

/-- `Q`-null `𝓕_t` events are `P`-null (the Esscher density is positive). -/
lemma esscher_null {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {r : ℝ} (hQ : Shared.IsEsscher 𝓕 P Q X r)
    (hXm : ∀ t, Measurable (X t)) (t : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[𝓕 t] A)
    (h : Q A = 0) : P A = 0 := by
  have hI : Measurable (A.indicator (1 : Ω → ℝ≥0∞)) := (meas_ind_one hA).mono (𝓕.le t) le_rfl
  have h1 := esscher_lintegral hQ hXm t (meas_ind_one hA)
  rw [lintegral_indicator_one (𝓕.le t _ hA), h, eq_comm,
    lintegral_eq_zero_iff (show Measurable (fun ω => essD X r t ω * A.indicator 1 ω) from
      (measurable_essD hXm r t).mul hI)] at h1
  rw [← lintegral_indicator_one (𝓕.le t _ hA), lintegral_eq_zero_iff hI]
  filter_upwards [h1] with ω hω
  have hpos : essD X r t ω ≠ 0 := by
    simp only [essD, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  simp only [Pi.zero_apply] at hω ⊢
  exact (mul_eq_zero.1 hω).resolve_left hpos

lemma exists_rat_near (f : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t) {t b : ℝ≥0}
    {S : Set ℝ} (hS : S ∈ nhds (f t)) (htb : t < b) :
    ∃ q : ℚ, t ≤ Real.toNNReal q ∧ Real.toNNReal q < b ∧ f (Real.toNNReal q) ∈ S := by
  have hev : ∀ᶠ r in nhdsWithin t (Set.Ici t), f r ∈ S := (hrc t).eventually hS
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
  have hlt : (t : ℝ) < ((min u b : ℝ≥0) : ℝ) := by exact_mod_cast lt_min hu htb
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  have hq0 : (0 : ℝ) ≤ q := le_trans t.2 hq1.le
  have hqe : ((Real.toNNReal q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
  have h1 : t ≤ Real.toNNReal q := by rw [← NNReal.coe_le_coe, hqe]; exact hq1.le
  have h2 : Real.toNNReal q < min u b := by rw [← NNReal.coe_lt_coe, hqe]; exact hq2
  exact ⟨q, h1, lt_of_lt_of_le h2 (min_le_right _ _), hsub ⟨h1, lt_of_lt_of_le h2 (min_le_left _ _)⟩⟩

lemma monotone_of_rat (f : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (h : ∀ q r : ℚ, Real.toNNReal q ≤ Real.toNNReal r → f (Real.toNNReal q) ≤ f (Real.toNNReal r)) :
    Monotone f := by
  intro s u hsu
  by_contra hlt'
  have hlt := not_le.1 hlt'
  rcases eq_or_lt_of_le hsu with rfl | hsu'
  · exact lt_irrefl _ hlt
  set c := (f u + f s) / 2
  obtain ⟨q, hq1, hq2, hq3⟩ := exists_rat_near f hrc (S := Set.Ioi c) (Ioi_mem_nhds (by
    simp only [c]; linarith)) hsu'
  obtain ⟨r, hr1, -, hr3⟩ := exists_rat_near f hrc (S := Set.Iio c) (Iio_mem_nhds (by
    simp only [c]; linarith)) (lt_add_one u)
  have := h q r (le_trans hq2.le hr1)
  simp only [Set.mem_Ioi, Set.mem_Iio] at hq3 hr3
  linarith

/-- E1e: under the Esscher measure the paths are not a.s. monotone. -/
theorem esscher_not_ae_monotone {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r) :
    ¬ (∀ᵐ ω ∂Q, Monotone fun t => X t ω) := by
  intro hmono
  apply hX.isSNLevy.not_ae_monotone
  have hXm := hX.isSNLevy.measurable
  have hpair : ∀ q r : ℚ, ∀ᵐ ω ∂P, Real.toNNReal q ≤ Real.toNNReal r →
      X (Real.toNNReal q) ω ≤ X (Real.toNNReal r) ω := by
    intro q r
    by_cases hqr : Real.toNNReal q ≤ Real.toNNReal r
    · have hA : MeasurableSet[𝓕 (Real.toNNReal r)]
          {ω | ¬ (X (Real.toNNReal q) ω ≤ X (Real.toNNReal r) ω)} :=
        (measurableSet_le ((hX.adapted _).mono (𝓕.mono hqr) le_rfl) (hX.adapted _)).compl
      have h1 : ∀ᵐ ω ∂Q, X (Real.toNNReal q) ω ≤ X (Real.toNNReal r) ω := by
        filter_upwards [hmono] with ω hω using hω hqr
      have h2 : ∀ᵐ ω ∂P, X (Real.toNNReal q) ω ≤ X (Real.toNNReal r) ω :=
        ae_iff.2 (esscher_null hQ hXm _ hA (ae_iff.1 h1))
      filter_upwards [h2] with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hqr
  have hall : ∀ᵐ ω ∂P, ∀ q r : ℚ, Real.toNNReal q ≤ Real.toNNReal r →
      X (Real.toNNReal q) ω ≤ X (Real.toNNReal r) ω := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; exact hpair q
  filter_upwards [hall] with ω hω
  exact monotone_of_rat _ (hX.isSNLevy.right_continuous ω) hω

/-- E1e': under the Esscher measure the paths are not a.s. antitone. -/
theorem esscher_not_ae_antitone {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r) :
    ¬ (∀ᵐ ω ∂Q, Antitone fun t => X t ω) := by
  intro hanti
  apply hX.isSNLevy.not_ae_antitone
  have hXm := hX.isSNLevy.measurable
  have hpair : ∀ q r : ℚ, ∀ᵐ ω ∂P, Real.toNNReal q ≤ Real.toNNReal r →
      -X (Real.toNNReal q) ω ≤ -X (Real.toNNReal r) ω := by
    intro q r
    by_cases hqr : Real.toNNReal q ≤ Real.toNNReal r
    · have hA : MeasurableSet[𝓕 (Real.toNNReal r)]
          {ω | ¬ (X (Real.toNNReal r) ω ≤ X (Real.toNNReal q) ω)} :=
        (measurableSet_le (hX.adapted _) ((hX.adapted _).mono (𝓕.mono hqr) le_rfl)).compl
      have h1 : ∀ᵐ ω ∂Q, X (Real.toNNReal r) ω ≤ X (Real.toNNReal q) ω := by
        filter_upwards [hanti] with ω hω using hω hqr
      have h2 : ∀ᵐ ω ∂P, X (Real.toNNReal r) ω ≤ X (Real.toNNReal q) ω :=
        ae_iff.2 (esscher_null hQ hXm _ hA (ae_iff.1 h1))
      filter_upwards [h2] with ω hω _ using neg_le_neg hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hqr
  have hall : ∀ᵐ ω ∂P, ∀ q r : ℚ, Real.toNNReal q ≤ Real.toNNReal r →
      -X (Real.toNNReal q) ω ≤ -X (Real.toNNReal r) ω := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; exact hpair q
  filter_upwards [hall] with ω hω
  have hm := monotone_of_rat (fun t => -X t ω)
    (fun t => (hX.isSNLevy.right_continuous ω t).neg) hω
  exact fun a b hab => neg_le_neg_iff.1 (hm hab)

/-- E1f: `X` is a spectrally negative Lévy process under the Esscher measure. -/
theorem esscher_isSNLevyWrt {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r) :
    Shared.IsSNLevyWrt 𝓕 Q X where
  isSNLevy :=
    { measurable := hX.isSNLevy.measurable
      start_zero := hX.isSNLevy.start_zero
      indep_increments := esscher_indepIncrements hX hQ
      stationary_increments := esscher_stationary hX hQ
      right_continuous := hX.isSNLevy.right_continuous
      left_limits := hX.isSNLevy.left_limits
      no_positive_jumps := hX.isSNLevy.no_positive_jumps
      not_ae_monotone := esscher_not_ae_monotone hX hQ
      not_ae_antitone := esscher_not_ae_antitone hX hQ }
  adapted := hX.adapted
  indep_past := esscher_indep_past hX hQ
  right_continuous_filtration := hX.right_continuous_filtration


/-- E1g: the Laplace exponent under the Esscher measure is the tilted exponent `ψ(θ+1) - ψ(1)`. -/
theorem esscher_psi {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r)
    (hψ : Shared.psi P X 1 = r) {θ : ℝ} (hθ : 0 ≤ θ) :
    Shared.psi Q X θ = Shared.tilt P X 1 θ := by
  have hXQ := esscher_isSNLevyWrt hX hQ
  have hXm := hX.isSNLevy.measurable
  have h1 := mgf_exp 𝓕 Q X hXQ hθ 1
  have h2 := mgf_exp 𝓕 P X hX (show 0 ≤ θ + 1 by linarith) 1
  have hm : Measurable[𝓕 1] (fun ω => ENNReal.ofReal (Real.exp (θ * X 1 ω))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hX.adapted 1).const_mul θ))
  rw [esscher_lintegral hQ hXm 1 hm] at h1
  have h3 : ∫⁻ ω, essD X r 1 ω * ENNReal.ofReal (Real.exp (θ * X 1 ω)) ∂P =
      ENNReal.ofReal (Real.exp (-r)) * ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ + 1) * X 1 ω)) ∂P := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ω => ?_
    simp only [essD, NNReal.coe_one, mul_one]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  rw [h3, h2, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add] at h1
  have h4 := (ENNReal.ofReal_eq_ofReal_iff (Real.exp_pos _).le (Real.exp_pos _).le).1 h1
  have h5 := Real.exp_injective h4
  simp only [NNReal.coe_one, one_mul] at h5
  unfold Shared.tilt
  rw [hψ]
  linarith

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-! ## R1: the `q`-resolvent of the reflected process `Y = refl s x X` -/

/-- The running supremum `S_t = sup_{u ≤ t} X_u` on `ℝ × Ω` (so `Ynr = X_t - S_t`). -/
noncomputable def supP {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (p : ℝ × Ω) : ℝ :=
  X (Real.toNNReal p.1) p.2 - Ynr X p

lemma supP_eq {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (p : ℝ × Ω) :
    supP X p = sSup ((fun u => X u p.2) '' Set.Iic (Real.toNNReal p.1)) := by
  unfold supP Ynr; ring

lemma measurable_supP {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) : Measurable (supP X) := by
  have hj := measurable_joint_of_rc X hX.measurable (fun ω t => hX.right_continuous ω t)
  have hc : Measurable (fun p : ℝ × Ω => X (Real.toNNReal p.1) p.2) :=
    hj.comp (measurable_real_toNNReal.prodMap measurable_id)
  exact hc.sub (measurable_Ynr hX)

lemma supP_bdd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (t : ℝ≥0) (ω : Ω) : BddAbove ((fun u => X u ω) '' Set.Iic t) :=
  bddAbove_of_cadlag (fun r => X r ω) (hX.right_continuous ω) (hX.left_limits ω) t

lemma supP_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (p : ℝ × Ω) : 0 ≤ supP X p := by
  rw [supP_eq]
  exact le_csSup_of_le (supP_bdd hX _ _) ⟨0, Set.mem_Iic.2 (by simp), rfl⟩
    (hX.start_zero p.2).symm.le

lemma supP_gt_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) {a : ℝ} (ha : 0 ≤ a) (p : ℝ × Ω) :
    a < supP X p ↔ p ∈ Ex X a := by
  rw [supP_eq, lt_csSup_iff (supP_bdd hX _ _)
    ⟨_, Real.toNNReal p.1, Set.mem_Iic.2 le_rfl, rfl⟩]
  have h := (exceed_before (fun u => X u p.2) (hX.start_zero p.2) (hX.left_limits p.2)
    (fun s hs => hX.no_positive_jumps p.2 s hs) ha (Real.toNNReal p.1)).symm
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, hb⟩
    exact h.1 ⟨u, Set.mem_Iic.1 hu, hb⟩
  · intro hp
    obtain ⟨u, hu, hb⟩ := h.2 hp
    exact ⟨_, ⟨u, Set.mem_Iic.2 hu, rfl⟩, hb⟩

/-- Pathwise: `Y_t = (y - S_t)^+ + (S_t - X_t)` with `y = s - x`. -/
lemma refl_eq_decomp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (s x : ℝ) (p : ℝ × Ω) :
    Shared.refl s x X (Real.toNNReal p.1) p.2 = max (s - x - supP X p) 0 - Ynr X p := by
  have hY : Ynr X p = X (Real.toNNReal p.1) p.2 - supP X p := by unfold supP; ring
  set t := Real.toNNReal p.1
  have hI : Set.Icc (0 : ℝ≥0) t = Set.Iic t := by
    ext u; simp only [Set.mem_Icc, Set.mem_Iic, zero_le, true_and]
  have himg : (fun u => x + X u p.2) '' Set.Iic t =
      (fun z => x + z) '' ((fun u => X u p.2) '' Set.Iic t) := (Set.image_image _ _ _).symm
  have hsup : sSup ((fun u => x + X u p.2) '' Set.Icc 0 t) = x + supP X p := by
    rw [hI, himg, supP_eq]
    exact ((monotone_id.const_add x).map_csSup_of_continuousAt
      (continuous_const.add continuous_id).continuousAt
      (⟨X t p.2, t, Set.mem_Iic.2 le_rfl, rfl⟩ : ((fun u => X u p.2) '' Set.Iic t).Nonempty)
      (supP_bdd hX t p.2)).symm
  unfold Shared.refl Shared.runMax
  rw [hsup, hY]
  simp only [max_def]
  split_ifs <;> linarith

/-- The exponential law with rate `κ` on `(0, ∞)`. -/
noncomputable abbrev expLaw (κ : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun a => ENNReal.ofReal (κ * Real.exp (-(κ * a))))

lemma expLaw_Ioi {κ : ℝ} (hκ : 0 < κ) (a : ℝ) :
    expLaw κ (Set.Ioi a) = ENNReal.ofReal (Real.exp (-(κ * max a 0))) := by
  rw [withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi]
  have h : ∀ z : ℝ, ENNReal.ofReal (κ * Real.exp (-(κ * z))) =
      ENNReal.ofReal κ * ENNReal.ofReal (Real.exp ((-κ) * z)) := by
    intro z; rw [← ENNReal.ofReal_mul hκ.le]; congr 2; ring
  simp_rw [h]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_exp_Ioi_c (by linarith : -κ < 0), ← ENNReal.ofReal_mul hκ.le]
  congr 1
  rw [neg_div_neg_eq, neg_mul]
  field_simp

lemma expLaw_lt_top {κ : ℝ} (hκ : 0 < κ) (a : ℝ) : expLaw κ (Set.Ioi a) < ⊤ := by
  rw [expLaw_Ioi hκ]; exact ENNReal.ofReal_lt_top

/-- Rectangles: `μ(S > a, Ynr ∈ B) = e^{-κ a⁺} μ(Ynr ∈ B)` under `μ = e^{-qs}ds ⊗ P`. -/
theorem joint_rect {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) (a : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    ((nuq q).prod P) ({p | a < supP X p} ∩ Ynr X ⁻¹' B) =
      ENNReal.ofReal (Real.exp (-(kap P X q * max a 0))) * ((nuq q).prod P) (Ynr X ⁻¹' B) := by
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  set μ := (nuq q).prod P with hμ
  have hpos : ∀ b : ℝ, 0 < b → μ ({p | b < supP X p} ∩ Ynr X ⁻¹' B) =
      ENNReal.ofReal (Real.exp (-(kap P X q * b))) * μ (Ynr X ⁻¹' B) := by
    intro b hb
    have hE : {p | b < supP X p} = Ex X b := by
      ext p; exact supP_gt_iff hXL hb.le p
    rw [hE]
    exact law_Ex 𝓕 P X hX hq hb hB
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hU : {p | a < supP X p} = Set.univ := by
      ext p; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le ha (supP_nonneg hXL p)
    rw [hU, Set.univ_inter, max_eq_right ha.le]
    simp
  · set s : ℕ → Set (ℝ × Ω) := fun n => {p | 1 / ((n : ℝ) + 1) < supP X p} ∩ Ynr X ⁻¹' B
    have hmono : Monotone s := by
      intro i j hij p hp
      have h1 : 1 / ((i : ℝ) + 1) < supP X p := hp.1
      have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
        one_div_le_one_div_of_le hi (by exact_mod_cast Nat.add_le_add_right hij 1)
      exact ⟨show 1 / ((j : ℝ) + 1) < supP X p from lt_of_le_of_lt hle h1, hp.2⟩
    have hU : (⋃ n, s n) = {p | 0 < supP X p} ∩ Ynr X ⁻¹' B := by
      ext p
      simp only [s, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · rintro ⟨n, h1, h2⟩
        exact ⟨lt_trans (by positivity) h1, h2⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt h1
        exact ⟨n, hn, h2⟩
    have hl1 := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU] at hl1
    have hfun : (μ ∘ s) = fun n : ℕ =>
        ENNReal.ofReal (Real.exp (-(kap P X q * (1 / ((n : ℝ) + 1))))) * μ (Ynr X ⁻¹' B) := by
      funext n; exact hpos _ (by positivity)
    rw [hfun] at hl1
    have hl2 : Tendsto (fun n : ℕ =>
        ENNReal.ofReal (Real.exp (-(kap P X q * (1 / ((n : ℝ) + 1))))) * μ (Ynr X ⁻¹' B)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-(kap P X q * 0))) * μ (Ynr X ⁻¹' B))) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr (measure_ne_top _ _))
      refine ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp ?_)
      exact ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _).neg)
    rw [tendsto_nhds_unique hl1 hl2, max_self]
  · rw [max_eq_left ha.le]
    exact hpos a ha

/-- The joint law of `(S, Ynr)` under `μ = e^{-qs}ds ⊗ P` is `Exp(κ) ⊗ law(Ynr)` (Wiener-Hopf). -/
theorem joint_law {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) :
    (expLaw (kap P X q)).prod (((nuq q).prod P).map (Ynr X)) =
      ((nuq q).prod P).map (fun p => (supP X p, Ynr X p)) := by
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  have hκ := kap_pos 𝓕 P X hX hq
  have hpair : Measurable (fun p : ℝ × Ω => (supP X p, Ynr X p)) :=
    (measurable_supP hXL).prodMk (measurable_Ynr hXL)
  have hC : MeasurableSpace.generateFrom (Set.range (Set.Ioi : ℝ → Set ℝ)) =
      (inferInstance : MeasurableSpace ℝ) :=
    (borel_eq_generateFrom_Ioi ℝ).symm.trans BorelSpace.measurable_eq.symm
  have h3C : (expLaw (kap P X q)).FiniteSpanningSetsIn (Set.range (Set.Ioi : ℝ → Set ℝ)) :=
    { set := fun n => Set.Ioi (-(n : ℝ))
      set_mem := fun n => ⟨_, rfl⟩
      finite := fun n => expLaw_lt_top hκ _
      spanning := by
        ext z
        simp only [Set.mem_iUnion, Set.mem_Ioi, Set.mem_univ, iff_true]
        obtain ⟨n, hn⟩ := exists_nat_gt (-z)
        exact ⟨n, by linarith⟩ }
  refine Measure.prod_eq_generateFrom hC MeasurableSpace.generateFrom_measurableSet isPiSystem_Ioi
    MeasurableSpace.isPiSystem_measurableSet h3C (Measure.toFiniteSpanningSetsIn _) ?_
  rintro _ ⟨a, rfl⟩ B hB
  rw [Measure.map_apply hpair (measurableSet_Ioi.prod hB),
    Measure.map_apply (measurable_Ynr hXL) hB, expLaw_Ioi hκ, Set.mk_preimage_prod]
  exact joint_rect 𝓕 P X hX hq a hB

/-- R1: the `q`-resolvent of the reflected process `Y = refl s x X`:
`∫ e^{-qt} E g(Y_t) dt = ∫ E_μ ∫ g((y - a)^+ + R) κe^{-κa} da` with `y = s - x`, `R = -Ynr`. -/
theorem refl_resolvent {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) (s x : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g (Shared.refl s x X (Real.toNNReal p.1) p.2) ∂((nuq q).prod P) =
      ∫⁻ p, ∫⁻ a, g (max (s - x - a) 0 - Ynr X p) ∂(expLaw (kap P X q)) ∂((nuq q).prod P) := by
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  set G : ℝ × ℝ → ℝ≥0∞ := fun z => g (max (s - x - z.1) 0 - z.2) with hG
  have hGm : Measurable G :=
    hg.comp (((measurable_const.sub measurable_fst).max measurable_const).sub measurable_snd)
  have hpair : Measurable (fun p : ℝ × Ω => (supP X p, Ynr X p)) :=
    (measurable_supP hXL).prodMk (measurable_Ynr hXL)
  have h1 : ∫⁻ p, g (Shared.refl s x X (Real.toNNReal p.1) p.2) ∂((nuq q).prod P) =
      ∫⁻ p, G (supP X p, Ynr X p) ∂((nuq q).prod P) := by
    refine lintegral_congr fun p => ?_
    simp only [hG, refl_eq_decomp hXL s x p]
  have hF : Measurable fun z : ℝ => ∫⁻ a, G (a, z) ∂(expLaw (kap P X q)) :=
    (hGm.comp (measurable_snd.prodMk measurable_fst)).lintegral_prod_right'
  rw [h1, ← lintegral_map hGm hpair, ← joint_law 𝓕 P X hX hq, lintegral_prod_symm _ hGm.aemeasurable,
    lintegral_map hF (measurable_Ynr hXL)]

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-! ## E2: scale functions under the Esscher measure -/

/-- `Φ_Q(β) = Φ(β + r) - 1` for the Esscher measure `Q = ℙ^1` (`r = ψ(1)`). -/
theorem kap_esscher {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r)
    (hψ : Shared.psi P X 1 = r) (hr : 0 ≤ r) {β : ℝ} (hβ : 0 < β) :
    kap Q X β = kap P X (β + r) - 1 := by
  have hXQ := esscher_isSNLevyWrt hX hQ
  have hp : 0 < β + r := by linarith
  have key : ∀ θ : ℝ, 0 ≤ θ → (θ < kap Q X β ↔ θ + 1 < kap P X (β + r)) := by
    intro θ hθ
    rw [← psi_lt_iff 𝓕 Q X hXQ hβ hθ, ← psi_lt_iff 𝓕 P X hX hp (by linarith),
      esscher_psi hX hQ hψ hθ]
    unfold Shared.tilt
    rw [hψ]
    constructor <;> intro h <;> linarith
  have hκQ := kap_pos 𝓕 Q X hXQ hβ
  have h1 : 1 < kap P X (β + r) := by
    rw [← psi_lt_iff 𝓕 P X hX hp zero_le_one, hψ]
    linarith
  apply le_antisymm
  · by_contra hc
    have hc' := not_le.1 hc
    have := (key _ (by linarith)).1 hc'
    linarith
  · by_contra hc
    have hc' := not_le.1 hc
    have := (key _ hκQ.le).2 (by linarith)
    exact lt_irrefl _ this

/-- `W_Q^{(β)}(x) = e^{-x} W^{(β + r)}(x)`: the scale function under the Esscher measure. -/
theorem Wq_esscher {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    {P Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {X : ℝ≥0 → Ω → ℝ} {r : ℝ}
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hQ : Shared.IsEsscher 𝓕 P Q X r)
    (hψ : Shared.psi P X 1 = r) (hr : 0 ≤ r) {β : ℝ} (hβ : 0 < β) :
    Wq Q X β = fun x => Real.exp (-x) * Wq P X (β + r) x := by
  have hXQ := esscher_isSNLevyWrt hX hQ
  have hp : 0 < β + r := by linarith
  have hT : Shared.tilt Q X 0 = Shared.psi Q X := by
    funext θ
    simp [Shared.tilt, Shared.psi]
  have hPhi : Shared.Phi (Shared.tilt Q X 0) β = kap Q X β := by
    rw [hT]; exact Phi_eq_kap 𝓕 Q X hXQ hβ
  refine isScaleFun_unique (isScaleFun_Wq' 𝓕 Q X hXQ hβ) ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact mul_nonneg (Real.exp_pos _).le (Wq_nonneg 𝓕 P X hX hp x)
  · intro x hx
    simp [Wq, hx]
  · exact (Real.continuous_exp.comp continuous_neg).continuousOn.mul
      (isScaleFun_Wq' 𝓕 P X hX hp).2.2.1
  · intro θ hθ
    have hθ0 : 0 ≤ θ := le_of_lt (lt_trans (kap_pos 𝓕 Q X hXQ hβ) (hPhi ▸ hθ))
    rw [hPhi, kap_esscher hX hQ hψ hr hβ] at hθ
    have hθ1 : kap P X (β + r) < θ + 1 := by linarith
    obtain ⟨hint, hval⟩ := laplace_Wq 𝓕 P X hX hp hθ1
    have hfun : (fun x => Real.exp (-θ * x) * (Real.exp (-x) * Wq P X (β + r) x)) =
        fun x => Real.exp (-(θ + 1) * x) * Wq P X (β + r) x := by
      funext x
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    beta_reduce
    refine ⟨by rw [hfun]; exact hint, ?_⟩
    rw [hfun, hval, hT, esscher_psi hX hQ hψ hθ0]
    unfold Shared.tilt
    rw [hψ]
    congr 1
    ring

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-! ## R2a: freezing an `𝓕_t`-measurable value against the post-`t` increment path -/

/-- Freezing lemma at a fixed time: `E F(V, X_{t+·} - X_t) = E [ (E F(v, X)) |_{v = V} ]`
for `V` `𝓕_t`-measurable. -/
theorem freeze {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (t : ℝ≥0) {V : Ω → ℝ} (hV : Measurable[𝓕 t] V) {F : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (V ω, postPath X t ω) ∂P = ∫⁻ ω, ∫⁻ ω', F (V ω, fun u => X u ω') ∂P ∂P := by
  have hXL := hX.isSNLevy
  have hXm := hXL.measurable
  have hV' : Measurable V := hV.mono (𝓕.le t) le_rfl
  have hpp : Measurable (postPath X t) :=
    measurable_pi_lambda _ fun u => (hXm _).sub (hXm _)
  have hpath : Measurable (fun ω (u : ℝ≥0) => X u ω) := measurable_pi_lambda _ fun u => hXm u
  have hind : IndepFun V (postPath X t) P := by
    have h1 := (indep_postIncrements_past 𝓕 P X hX t).symm
    have h2 : MeasurableSpace.comap (postPath X t) MeasurableSpace.pi =
        ⨆ u, MeasurableSpace.comap (fun ω => X (t + u) ω - X t ω)
          (inferInstance : MeasurableSpace ℝ) := by
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      congr 1
      funext u
      rw [MeasurableSpace.comap_comp]
      rfl
    show Indep (MeasurableSpace.comap V inferInstance)
      (MeasurableSpace.comap (postPath X t) MeasurableSpace.pi) P
    rw [h2]
    exact indep_of_indep_of_le_left h1 hV.comap_le
  have hmap : P.map (fun ω => (V ω, postPath X t ω)) = (P.map V).prod (P.map (postPath X t)) :=
    (indepFun_iff_map_prod_eq_prod_map_map' hV'.aemeasurable hpp.aemeasurable inferInstance
      inferInstance).1 hind
  have hid : P.map (postPath X t) = P.map (fun ω (u : ℝ≥0) => X u ω) :=
    (identDistrib_postIncrements P X hXL t).map_eq
  have hpair : Measurable (fun ω => (V ω, postPath X t ω)) := hV'.prodMk hpp
  calc ∫⁻ ω, F (V ω, postPath X t ω) ∂P
      = ∫⁻ z, F z ∂(P.map (fun ω => (V ω, postPath X t ω))) := (lintegral_map hF hpair).symm
    _ = ∫⁻ z, F z ∂((P.map V).prod (P.map (fun ω (u : ℝ≥0) => X u ω))) := by rw [hmap, hid]
    _ = ∫⁻ v, ∫⁻ w, F (v, w) ∂(P.map (fun ω (u : ℝ≥0) => X u ω)) ∂(P.map V) :=
        lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ ω, ∫⁻ w, F (V ω, w) ∂(P.map (fun ω (u : ℝ≥0) => X u ω)) ∂P :=
        lintegral_map hF.lintegral_prod_right' hV'
    _ = ∫⁻ ω, ∫⁻ ω', F (V ω, fun u => X u ω') ∂P ∂P := by
        refine lintegral_congr fun ω => ?_
        exact lintegral_map (hF.comp (measurable_const.prodMk measurable_id)) hpath

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-! ## R2b: the Markov resolvent identity for the reflected process `Y = refl y 0 X` -/

/-- Freezing lemma with a frozen variable in any measurable space. -/
theorem freezeE {Ω E : Type*} {m : MeasurableSpace Ω} [MeasurableSpace E] (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (t : ℝ≥0) {V : Ω → E} (hV : Measurable[𝓕 t] V) {F : E × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω, F (V ω, postPath X t ω) ∂P = ∫⁻ ω, ∫⁻ ω', F (V ω, fun u => X u ω') ∂P ∂P := by
  have hXL := hX.isSNLevy
  have hXm := hXL.measurable
  have hV' : Measurable V := hV.mono (𝓕.le t) le_rfl
  have hpp : Measurable (postPath X t) :=
    measurable_pi_lambda _ fun u => (hXm _).sub (hXm _)
  have hpath : Measurable (fun ω (u : ℝ≥0) => X u ω) := measurable_pi_lambda _ fun u => hXm u
  have hind : IndepFun V (postPath X t) P := by
    have h1 := (indep_postIncrements_past 𝓕 P X hX t).symm
    have h2 : MeasurableSpace.comap (postPath X t) MeasurableSpace.pi =
        ⨆ u, MeasurableSpace.comap (fun ω => X (t + u) ω - X t ω)
          (inferInstance : MeasurableSpace ℝ) := by
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      congr 1
      funext u
      rw [MeasurableSpace.comap_comp]
      rfl
    show Indep (MeasurableSpace.comap V inferInstance)
      (MeasurableSpace.comap (postPath X t) MeasurableSpace.pi) P
    rw [h2]
    exact indep_of_indep_of_le_left h1 hV.comap_le
  have hmap : P.map (fun ω => (V ω, postPath X t ω)) = (P.map V).prod (P.map (postPath X t)) :=
    (indepFun_iff_map_prod_eq_prod_map_map' hV'.aemeasurable hpp.aemeasurable inferInstance
      inferInstance).1 hind
  have hid : P.map (postPath X t) = P.map (fun ω (u : ℝ≥0) => X u ω) :=
    (identDistrib_postIncrements P X hXL t).map_eq
  have hpair : Measurable (fun ω => (V ω, postPath X t ω)) := hV'.prodMk hpp
  calc ∫⁻ ω, F (V ω, postPath X t ω) ∂P
      = ∫⁻ z, F z ∂(P.map (fun ω => (V ω, postPath X t ω))) := (lintegral_map hF hpair).symm
    _ = ∫⁻ z, F z ∂((P.map V).prod (P.map (fun ω (u : ℝ≥0) => X u ω))) := by rw [hmap, hid]
    _ = ∫⁻ v, ∫⁻ w, F (v, w) ∂(P.map (fun ω (u : ℝ≥0) => X u ω)) ∂(P.map V) :=
        lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ ω, ∫⁻ w, F (V ω, w) ∂(P.map (fun ω (u : ℝ≥0) => X u ω)) ∂P :=
        lintegral_map hF.lintegral_prod_right' hV'
    _ = ∫⁻ ω, ∫⁻ ω', F (V ω, fun u => X u ω') ∂P ∂P := by
        refine lintegral_congr fun ω => ?_
        exact lintegral_map (hF.comp (measurable_const.prodMk measurable_id)) hpath

/-- Freezing on an event `A ∈ 𝓕_t`. -/
lemma freeze_set {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (t : ℝ≥0) {V : Ω → ℝ} (hV : Measurable[𝓕 t] V) {A : Set Ω} (hA : MeasurableSet[𝓕 t] A)
    {G : ℝ × (ℝ≥0 → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω in A, G (V ω, postPath X t ω) ∂P = ∫⁻ ω in A, ∫⁻ ω', G (V ω, fun u => X u ω') ∂P ∂P := by
  have hAm : MeasurableSet A := 𝓕.le t A hA
  have hι𝓕 : Measurable[𝓕 t] (A.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hA
  have hF : Measurable (fun z : (ℝ≥0∞ × ℝ) × (ℝ≥0 → ℝ) => z.1.1 * G (z.1.2, z.2)) :=
    (measurable_fst.comp measurable_fst).mul
      (hG.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have h := freezeE 𝓕 P X hX t (V := fun ω => (A.indicator (fun _ => (1 : ℝ≥0∞)) ω, V ω))
    (hι𝓕.prodMk hV) hF
  have hL : ∀ g : Ω → ℝ≥0∞, ∫⁻ ω in A, g ω ∂P =
      ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * g ω ∂P := by
    intro g
    rw [← lintegral_indicator hAm]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  rw [hL, hL]
  refine h.trans ?_
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]

/-- `Y_t = (y - S_t)^+ + (S_t - X_t)` for `refl y 0`. -/
lemma refl_eq_Yform {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (y : ℝ) (p : ℝ × Ω) :
    Shared.refl y 0 X (Real.toNNReal p.1) p.2 = max (y - supP X p) 0 - Ynr X p := by
  have h := refl_eq_decomp hX y 0 p
  rw [sub_zero] at h
  exact h

lemma measurable_reflY {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) :
    Measurable (fun z : ℝ × (ℝ × Ω) => Shared.refl z.1 0 X (Real.toNNReal z.2.1) z.2.2) := by
  have heq : (fun z : ℝ × (ℝ × Ω) => Shared.refl z.1 0 X (Real.toNNReal z.2.1) z.2.2) =
      fun z => max (z.1 - supP X z.2) 0 - Ynr X z.2 :=
    funext fun z => refl_eq_Yform hX z.1 z.2
  rw [heq]
  exact ((measurable_fst.sub ((measurable_supP hX).comp measurable_snd)).max
    measurable_const).sub ((measurable_Ynr hX).comp measurable_snd)

/-- `Y_t` is `𝓕_t`-measurable. -/
lemma measurable_refl_past {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) (y : ℝ) (t : ℝ≥0) :
    Measurable[𝓕 t] (fun ω => Shared.refl y 0 X t ω) := by
  have hXL := hX.isSNLevy
  have heq : (fun ω => Shared.refl y 0 X t ω) =
      fun ω => max (y - (X t ω - Ynr X ((t : ℝ), ω))) 0 - Ynr X ((t : ℝ), ω) := by
    funext ω
    have h := refl_eq_Yform hXL y ((t : ℝ), ω)
    simp only [Real.toNNReal_coe] at h
    rw [h]
    unfold supP
    simp only [Real.toNNReal_coe]
  have hY := measurable_Ynr_past 𝓕 P X hX (t : ℝ)
  rw [Real.toNNReal_coe] at hY
  rw [heq]
  exact ((measurable_const.sub ((hX.adapted t).sub hY)).max measurable_const).sub hY

/-- Rational-time (path-space measurable) version of `max v (sup_{[0,r]} w) - w r`. -/
noncomputable def reflQ (r : ℝ≥0) (z : ℝ × (ℝ≥0 → ℝ)) : ℝ :=
  max (z.1 - z.2 r) (-Real.log (rexpQ 1 r z.2).toReal)

lemma measurable_reflQ (r : ℝ≥0) : Measurable (reflQ r) :=
  (measurable_fst.sub ((measurable_pi_apply r).comp measurable_snd)).max
    (Real.measurable_log.comp (ENNReal.measurable_toReal.comp
      ((measurable_rexpQ 1 r).comp measurable_snd))).neg

lemma reflQ_eq (r : ℝ≥0) (v : ℝ) (w : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt w (Set.Ici t) t)
    (hb : BddAbove (w '' Set.Iic r)) :
    reflQ r (v, w) = max v (sSup (w '' Set.Iic r)) - w r := by
  unfold reflQ
  rw [← rexpP_eq_rexpQ 1 r w hrc, rexpP_eq_sup zero_le_one r w hb, one_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp, neg_neg]
  exact max_sub_sub_right v _ (w r)

lemma refl_eq_reflQ {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ) (v : ℝ) (r : ℝ≥0) (ω : Ω)
    (hrc : ∀ t, ContinuousWithinAt (fun u => Z u ω) (Set.Ici t) t)
    (hb : BddAbove ((fun u => Z u ω) '' Set.Iic r)) :
    Shared.refl v 0 Z r ω = reflQ r (v, fun u => Z u ω) := by
  rw [reflQ_eq r v _ hrc hb]
  have hI : Set.Icc (0 : ℝ≥0) r = Set.Iic r := by
    ext u; simp only [Set.mem_Icc, Set.mem_Iic, zero_le, true_and]
  unfold Shared.refl Shared.runMax
  simp only [zero_add]
  rw [hI]

lemma runMax_bdd_G {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (x : ℝ) (t : ℝ≥0) (ω : Ω) :
    BddAbove ((fun u => x + X u ω) '' Set.Icc 0 t) := by
  obtain ⟨C, hC⟩ := supP_bdd hX t ω
  refine ⟨x + C, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have := hC ⟨u, Set.mem_Iic.2 hu.2, rfl⟩
  simp only at this ⊢
  linarith

lemma postPath_bdd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (t r : ℝ≥0) (ω : Ω) :
    BddAbove ((fun u => X (t + u) ω - X t ω) '' Set.Iic r) := by
  obtain ⟨C, hC⟩ := supP_bdd hX (t + r) ω
  refine ⟨C - X t ω, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have := hC ⟨t + u, Set.mem_Iic.2 (add_le_add le_rfl (Set.mem_Iic.1 hu)), rfl⟩
  simp only at this ⊢
  linarith

/-- Pathwise Markov shift of the reflected process. -/
lemma refl_shift_G {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (s x : ℝ) (t₀ u : ℝ≥0) (ω : Ω) :
    Shared.refl s x X (t₀ + u) ω =
      Shared.refl (Shared.refl s x X t₀ ω) 0 (fun v ω => X (t₀ + v) ω - X t₀ ω) u ω := by
  set S1 := (fun w => x + X w ω) '' Set.Icc 0 (t₀ + u) with hS1
  set A := (fun w => x + X w ω) '' Set.Icc 0 t₀ with hA
  set B := (fun v => X (t₀ + v) ω - X t₀ ω) '' Set.Icc 0 u with hB
  have hbS1 : BddAbove S1 := runMax_bdd_G hX x (t₀ + u) ω
  have hneA : A.Nonempty := ⟨_, ⟨0, ⟨le_refl 0, (zero_le : (0:ℝ≥0) ≤ t₀)⟩, rfl⟩⟩
  have hneB : B.Nonempty := ⟨_, ⟨0, ⟨le_refl 0, (zero_le : (0:ℝ≥0) ≤ u)⟩, rfl⟩⟩
  have hneS1 : S1.Nonempty := ⟨_, ⟨0, ⟨le_refl 0, zero_le⟩, rfl⟩⟩
  have hbA : BddAbove A := runMax_bdd_G hX x t₀ ω
  have hBle : ∀ b ∈ B, b ≤ sSup S1 - x - X t₀ ω := by
    rintro _ ⟨v, hv, rfl⟩
    have : x + X (t₀ + v) ω ≤ sSup S1 :=
      le_csSup hbS1 ⟨t₀ + v, ⟨zero_le, (add_le_add_iff_left t₀).2 hv.2⟩, rfl⟩
    simp only; linarith
  have hbB : BddAbove B := ⟨_, hBle⟩
  have hsup : sSup S1 = max (sSup A) (x + X t₀ ω + sSup B) := by
    apply le_antisymm
    · refine csSup_le hneS1 ?_
      rintro _ ⟨w, hw, rfl⟩
      by_cases hwt : w ≤ t₀
      · exact le_trans (le_csSup hbA ⟨w, ⟨hw.1, hwt⟩, rfl⟩) (le_max_left _ _)
      · have hlt : t₀ ≤ w := le_of_lt (lt_of_not_ge hwt)
        have hv : w - t₀ ∈ Set.Icc (0 : ℝ≥0) u := ⟨zero_le, by
          rw [tsub_le_iff_left]; exact hw.2⟩
        have hb := le_csSup hbB ⟨w - t₀, hv, rfl⟩
        simp only at hb
        rw [add_tsub_cancel_of_le hlt] at hb
        refine le_trans ?_ (le_max_right _ _)
        simp only; linarith
    · refine max_le ?_ ?_
      · exact csSup_le_csSup hbS1 hneA (Set.image_mono (Set.Icc_subset_Icc_right le_self_add))
      · have := csSup_le hneB hBle
        linarith
  unfold Shared.refl Shared.runMax
  simp only [zero_add]
  rw [← hS1, ← hA, ← hB, hsup]
  have key : max (max s (sSup A) - (x + X t₀ ω)) (sSup B)
      = max s (max (sSup A) (x + X t₀ ω + sSup B)) - (x + X t₀ ω) := by
    simp only [max_def]; split_ifs <;> linarith
  rw [key]; ring

/-- After time `t`, `Y` is the rational-sup functional of the post-`t` increment path. -/
lemma refl_post_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (y : ℝ) (t : ℝ≥0) {r : ℝ} (hr : 0 < r) (ω : Ω) :
    Shared.refl y 0 X (Real.toNNReal (r + t)) ω =
      reflQ (Real.toNNReal r) (Shared.refl y 0 X t ω, postPath X t ω) := by
  have ht : Real.toNNReal (r + t) = t + Real.toNNReal r := by
    rw [Real.toNNReal_add hr.le t.coe_nonneg, Real.toNNReal_coe, add_comm]
  rw [ht, refl_shift_G hX y 0 t (Real.toNNReal r) ω]
  exact refl_eq_reflQ _ _ _ _ (post_rc hX t ω) (postPath_bdd hX t _ ω)

lemma setLIntegral_Ioi_shift (g : ℝ → ℝ≥0∞) (a : ℝ) :
    ∫⁻ s in Set.Ioi a, g s = ∫⁻ r in Set.Ioi (0 : ℝ), g (r + a) := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  have h2 : ∫⁻ s, (Set.Ioi a).indicator g s =
      ∫⁻ r, (Set.Ioi a).indicator g (r + a) :=
    (lintegral_add_right_eq_self ((Set.Ioi a).indicator g) a).symm
  rw [h2]
  refine lintegral_congr fun r => ?_
  by_cases hr : 0 < r
  · rw [Set.indicator_of_mem (show r + a ∈ Set.Ioi a by simp [hr]),
      Set.indicator_of_mem (show r ∈ Set.Ioi (0 : ℝ) from hr)]
  · rw [Set.indicator_of_notMem (show r + a ∉ Set.Ioi a by simp; linarith),
      Set.indicator_of_notMem (show r ∉ Set.Ioi (0 : ℝ) from hr)]

/-- The `β`-resolvent of `f` for the reflected process started at `y`. -/
noncomputable def resU {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (β : ℝ) (f : ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(β * r))) *
    ∫⁻ ω, f (Shared.refl y 0 X (Real.toNNReal r) ω) ∂P

lemma measurable_resK {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun z : ℝ × ℝ => ∫⁻ ω, f (Shared.refl z.1 0 X (Real.toNNReal z.2) ω) ∂P) := by
  have h : Measurable (fun q : (ℝ × ℝ) × Ω =>
      f (Shared.refl q.1.1 0 X (Real.toNNReal q.1.2) q.2)) :=
    (hf.comp (measurable_reflY hX)).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact h.lintegral_prod_right'

lemma measurable_resU {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) (β : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (resU P X β f) := by
  have hc : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-(β * r)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)
  have h : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp (-(β * z.2))) *
      ∫⁻ ω, f (Shared.refl z.1 0 X (Real.toNNReal z.2) ω) ∂P) :=
    (hc.comp measurable_snd).mul (measurable_resK hX hf)
  exact h.lintegral_prod_right'

/-- R2: Markov resolvent identity on `A ∈ 𝓕_t`:
`E[1_A ∫_t^∞ e^{-βs} f(Y_s) ds] = e^{-βt} E[1_A u(Y_t)]` with `u = resU`. -/
theorem markov_resolvent {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    (β y : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) (t : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[𝓕 t] A) :
    ∫⁻ ω in A, (∫⁻ s in Set.Ioi (t : ℝ), ENNReal.ofReal (Real.exp (-(β * s))) *
        f (Shared.refl y 0 X (Real.toNNReal s) ω)) ∂P =
      ENNReal.ofReal (Real.exp (-(β * t))) *
        ∫⁻ ω in A, resU P X β f (Shared.refl y 0 X t ω) ∂P := by
  have hXL := hX.isSNLevy
  have hXm := hXL.measurable
  have hYt𝓕 := measurable_refl_past 𝓕 P X hX y t
  have hYtm : Measurable (fun ω => Shared.refl y 0 X t ω) := hYt𝓕.mono (𝓕.le t) le_rfl
  have hc : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-(β * r)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)
  have hJ : Measurable (fun p : ℝ × Ω => f (Shared.refl y 0 X (Real.toNNReal p.1) p.2)) :=
    (hf.comp (measurable_reflY hXL)).comp (measurable_const.prodMk measurable_id)
  have hK := measurable_resK (P := P) hXL hf
  have hct : ∀ r : ℝ, ENNReal.ofReal (Real.exp (-(β * (r + t)))) =
      ENNReal.ofReal (Real.exp (-(β * t))) * ENNReal.ofReal (Real.exp (-(β * r))) := by
    intro r
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  -- the inner (fixed `r > 0`) freezing step
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      ∫⁻ ω in A, f (Shared.refl y 0 X (Real.toNNReal (r + t)) ω) ∂P =
        ∫⁻ ω in A, ∫⁻ ω', f (Shared.refl (Shared.refl y 0 X t ω) 0 X (Real.toNNReal r) ω') ∂P
          ∂P := by
    intro r hr
    have hr' : 0 < r := hr
    have hG : Measurable (fun z : ℝ × (ℝ≥0 → ℝ) => f (reflQ (Real.toNNReal r) z)) :=
      hf.comp (measurable_reflQ _)
    calc ∫⁻ ω in A, f (Shared.refl y 0 X (Real.toNNReal (r + t)) ω) ∂P
        = ∫⁻ ω in A, f (reflQ (Real.toNNReal r) (Shared.refl y 0 X t ω, postPath X t ω)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [refl_post_eq hXL y t hr' ω]
      _ = ∫⁻ ω in A, ∫⁻ ω', f (reflQ (Real.toNNReal r)
            (Shared.refl y 0 X t ω, fun u => X u ω')) ∂P ∂P :=
          freeze_set 𝓕 P X hX t hYt𝓕 hA hG
      _ = _ := by
          refine lintegral_congr fun ω => lintegral_congr fun ω' => ?_
          rw [refl_eq_reflQ X _ _ ω' (hXL.right_continuous ω') (supP_bdd hXL _ ω')]
  have hAm : MeasurableSet A := 𝓕.le t A hA
  calc ∫⁻ ω in A, (∫⁻ s in Set.Ioi (t : ℝ), ENNReal.ofReal (Real.exp (-(β * s))) *
        f (Shared.refl y 0 X (Real.toNNReal s) ω)) ∂P
      = ∫⁻ ω in A, (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(β * (r + t)))) *
          f (Shared.refl y 0 X (Real.toNNReal (r + t)) ω)) ∂P := by
        refine lintegral_congr fun ω => ?_
        exact setLIntegral_Ioi_shift
          (fun s => ENNReal.ofReal (Real.exp (-(β * s))) *
            f (Shared.refl y 0 X (Real.toNNReal s) ω)) t
    _ = ∫⁻ r in Set.Ioi (0 : ℝ), ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(β * (r + t)))) *
          f (Shared.refl y 0 X (Real.toNNReal (r + t)) ω) ∂P := by
        refine lintegral_lintegral_swap ?_
        exact ((hc.comp (measurable_snd.add_const _)).mul
          (hJ.comp ((measurable_snd.add_const _).prodMk measurable_fst))).aemeasurable
    _ = ∫⁻ r in Set.Ioi (0 : ℝ), ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(β * (r + t)))) *
          ∫⁻ ω', f (Shared.refl (Shared.refl y 0 X t ω) 0 X (Real.toNNReal r) ω') ∂P ∂P := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hinner r hr]
    _ = ∫⁻ ω in A, (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(β * (r + t)))) *
          ∫⁻ ω', f (Shared.refl (Shared.refl y 0 X t ω) 0 X (Real.toNNReal r) ω') ∂P) ∂P := by
        refine lintegral_lintegral_swap ?_
        exact ((hc.comp (measurable_fst.add_const _)).mul
          (hK.comp ((hYtm.comp measurable_snd).prodMk measurable_fst))).aemeasurable
    _ = ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-(β * t))) *
          resU P X β f (Shared.refl y 0 X t ω) ∂P := by
        refine lintegral_congr fun ω => ?_
        simp_rw [hct, mul_assoc]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- `resU` is the `nuq β ⊗ P` integral used by `refl_resolvent`. -/
lemma resU_eq_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {β : ℝ} (hβ : 0 < β) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) (y : ℝ) :
    resU P X β f y = ∫⁻ p, f (Shared.refl y 0 X (Real.toNNReal p.1) p.2) ∂((nuq β).prod P) := by
  have := nuq_finite hβ
  have hJ : Measurable (fun p : ℝ × Ω => f (Shared.refl y 0 X (Real.toNNReal p.1) p.2)) :=
    (hf.comp (measurable_reflY hX)).comp (measurable_const.prodMk measurable_id)
  have hc : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-(β * r)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)
  rw [lintegral_prod _ hJ.aemeasurable, lintegral_withDensity_eq_lintegral_mul _ hc
    hJ.lintegral_prod_right']
  rfl

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-! ## C5: the supermartingale from a resolvent representation of `h` -/

lemma reflY_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (y : ℝ) (t : ℝ≥0) (ω : Ω) : 0 ≤ Shared.refl y 0 X t ω := by
  have h := refl_eq_Yform hX y ((t : ℝ), ω)
  simp only [Real.toNNReal_coe] at h
  rw [h]
  have := Ynr_nonpos hX ((t : ℝ), ω)
  have := le_max_right (y - supP X ((t : ℝ), ω)) 0
  linarith

lemma reflY_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) {y : ℝ} (hy : 0 ≤ y) (ω : Ω) : Shared.refl y 0 X 0 ω = y := by
  unfold Shared.refl Shared.runMax
  have hI : Set.Icc (0 : ℝ≥0) 0 = {0} := Set.Icc_self 0
  rw [hI, Set.image_singleton, csSup_singleton]
  simp [hX.start_zero ω, max_eq_left hy]

/-- `refl s x = refl (s - x) 0`. -/
lemma refl_sx {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (s x : ℝ) (t : ℝ≥0) (ω : Ω) :
    Shared.refl s x X t ω = Shared.refl (s - x) 0 X t ω := by
  have h1 := refl_eq_decomp hX s x ((t : ℝ), ω)
  have h2 := refl_eq_Yform hX (s - x) ((t : ℝ), ω)
  simp only [Real.toNNReal_coe] at h1 h2
  rw [h1, h2]

lemma runSup_rc (w : ℝ≥0 → ℝ) (hrc : ∀ t, ContinuousWithinAt w (Set.Ici t) t)
    (hb : ∀ t, BddAbove (w '' Set.Iic t)) (u : ℝ≥0) :
    ContinuousWithinAt (fun v => sSup (w '' Set.Iic v)) (Set.Ici u) u := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hw⟩ := Metric.continuousWithinAt_iff.1 (hrc u) (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun {v} hv hvd => ?_⟩
  have huv : u ≤ v := hv
  have hne : ∀ z : ℝ≥0, (w '' Set.Iic z).Nonempty := fun z => ⟨w z, z, Set.mem_Iic.2 le_rfl, rfl⟩
  have hge : sSup (w '' Set.Iic u) ≤ sSup (w '' Set.Iic v) :=
    csSup_le_csSup (hb v) (hne u) (Set.image_mono (Set.Iic_subset_Iic.2 huv))
  have hle : sSup (w '' Set.Iic v) ≤ sSup (w '' Set.Iic u) + ε / 2 := by
    refine csSup_le (hne v) ?_
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzu : z ≤ u
    · have := le_csSup (hb u) ⟨z, Set.mem_Iic.2 hzu, rfl⟩
      linarith
    · have hzu' : u ≤ z := le_of_lt (lt_of_not_ge hzu)
      have hzd : dist z u < δ := by
        rw [NNReal.dist_eq] at hvd ⊢
        have h0 : (u : ℝ) ≤ v := NNReal.coe_le_coe.2 huv
        have h1 : (u : ℝ) ≤ z := NNReal.coe_le_coe.2 hzu'
        have h2 : (z : ℝ) ≤ v := NNReal.coe_le_coe.2 (Set.mem_Iic.1 hz)
        rw [abs_of_nonneg (sub_nonneg.2 h0)] at hvd
        rw [abs_of_nonneg (sub_nonneg.2 h1)]
        linarith
      have h3 := hw (Set.mem_Ici.2 hzu') hzd
      rw [Real.dist_eq] at h3
      have := le_csSup (hb u) ⟨u, Set.mem_Iic.2 le_rfl, rfl⟩
      have := (abs_lt.1 h3).2
      linarith
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hge)]
  linarith

lemma reflY_rc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (y : ℝ) (ω : Ω) (u : ℝ≥0) :
    ContinuousWithinAt (fun v => Shared.refl y 0 X v ω) (Set.Ici u) u := by
  have heq : (fun v => Shared.refl y 0 X v ω) =
      fun v => max y (sSup ((fun z => X z ω) '' Set.Iic v)) - X v ω := by
    funext v
    rw [refl_eq_reflQ X y v ω (hX.right_continuous ω) (supP_bdd hX v ω),
      reflQ_eq v y _ (hX.right_continuous ω) (supP_bdd hX v ω)]
  rw [heq]
  exact (continuousWithinAt_const.max (runSup_rc _ (hX.right_continuous ω)
    (fun t => supP_bdd hX t ω) u)).sub (hX.right_continuous ω u)

lemma measurable_lintegral_rc {Ω : Type*} [MeasurableSpace Ω] (Y' : ℝ≥0 → Ω → ℝ)
    (hm : ∀ v, Measurable (Y' v))
    (hrc : ∀ ω v, ContinuousWithinAt (fun r => Y' r ω) (Set.Ici v) v) (S : Set ℝ)
    {φ : ℝ × ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (fun ω => ∫⁻ u in S, φ (u, Y' (Real.toNNReal u) ω)) := by
  have hj : Measurable (fun p : ℝ≥0 × Ω => Y' p.1 p.2) := measurable_joint_of_rc Y' hm hrc
  have hG : Measurable (fun q : Ω × ℝ => φ (q.2, Y' (Real.toNNReal q.2) q.1)) :=
    hφ.comp (measurable_snd.prodMk
      (hj.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)))
  exact hG.lintegral_prod_right'

/-- The running integral up to `t` is `𝓕_t`-measurable. -/
lemma measurable_runInt_past {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X) (y : ℝ) (t : ℝ≥0)
    {φ : ℝ × ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable[𝓕 t] (fun ω => ∫⁻ u in Set.Ioc (0 : ℝ) t,
      φ (u, Shared.refl y 0 X (Real.toNNReal u) ω)) := by
  have hXL := hX.isSNLevy
  have hm : ∀ v, Measurable[𝓕 t] (fun ω => Shared.refl y 0 X (min v t) ω) := fun v =>
    (measurable_refl_past 𝓕 P X hX y (min v t)).mono (𝓕.mono (min_le_right v t)) le_rfl
  have hrc : ∀ ω v, ContinuousWithinAt (fun r => Shared.refl y 0 X (min r t) ω)
      (Set.Ici v) v := by
    intro ω v
    have h1 := reflY_rc hXL y ω (min v t)
    have h2 : ContinuousWithinAt (fun r : ℝ≥0 => min r t) (Set.Ici v) v :=
      (continuous_id.min continuous_const).continuousWithinAt
    exact ContinuousWithinAt.comp (g := fun v => Shared.refl y 0 X v ω)
      (f := fun r : ℝ≥0 => min r t) h1 h2
      (fun r hr => Set.mem_Ici.2 (min_le_min (Set.mem_Ici.1 hr) le_rfl))
  have heq : (fun ω => ∫⁻ u in Set.Ioc (0 : ℝ) t, φ (u, Shared.refl y 0 X (Real.toNNReal u) ω)) =
      fun ω => ∫⁻ u in Set.Ioc (0 : ℝ) t,
        φ (u, (fun v ω => Shared.refl y 0 X (min v t) ω) (Real.toNNReal u) ω) := by
    funext ω
    refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have : min (Real.toNNReal u) t = Real.toNNReal u :=
      min_eq_left ((Real.toNNReal_le_iff_le_coe).2 hu.2)
    simp only [this]
  rw [heq]
  exact @measurable_lintegral_rc Ω (𝓕 t) (fun v ω => Shared.refl y 0 X (min v t) ω) hm hrc _ φ hφ

/-- The integrand of the running term. -/
noncomputable def runG {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (lam β y : ℝ) (ω : Ω) (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (lam * Real.exp (-(β * u) + Shared.refl y 0 X (Real.toNNReal u) ω))

/-- The integrand of the resolvent. -/
noncomputable def resF {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (β : ℝ) (f : ℝ → ℝ≥0∞) (y : ℝ) (ω : Ω)
    (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(β * s))) * f (Shared.refl y 0 X (Real.toNNReal s) ω)

/-- The lintegral form of `U`. -/
noncomputable def Lproc {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (β lam y : ℝ) (f : ℝ → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(β * t))) * resU Q X β f (Shared.refl y 0 X t ω) +
    ∫⁻ u in Set.Ioc (0 : ℝ) t, runG X lam β y ω u

lemma alg4 (a b c d : ℝ≥0∞) (h : c ≤ d) : a + (b + c) ≤ d + a + b := by
  calc a + (b + c) ≤ a + (b + d) := add_le_add le_rfl (add_le_add le_rfl h)
    _ = d + a + b := by rw [add_comm b d, ← add_assoc, add_comm a d]

set_option maxHeartbeats 1000000 in
/-- C5 core: `∫_A L_j ≤ ∫_A L_i` for `A ∈ 𝓕_i`, `i ≤ j`. -/
theorem super_core {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 Q X)
    (β lam y : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfl : ∀ z, 0 ≤ z → ENNReal.ofReal (lam * Real.exp z) ≤ f z)
    {i j : ℝ≥0} (hij : i ≤ j) {A : Set Ω} (hA : MeasurableSet[𝓕 i] A) :
    ∫⁻ ω in A, Lproc Q X β lam y f j ω ∂Q ≤ ∫⁻ ω in A, Lproc Q X β lam y f i ω ∂Q := by
  have hXL := hX.isSNLevy
  have hAj : MeasurableSet[𝓕 j] A := 𝓕.mono hij A hA
  have hYp : Measurable (fun p : ℝ × Ω => Shared.refl y 0 X (Real.toNNReal p.1) p.2) :=
    (measurable_reflY hXL).comp (measurable_const.prodMk measurable_id)
  have hgm : Measurable (fun q : Ω × ℝ => runG X lam β y q.1 q.2) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      ((measurable_const.mul measurable_snd).neg.add
        (hYp.comp (measurable_snd.prodMk measurable_fst)))))
  have hFm : Measurable (fun q : Ω × ℝ => resF X β f y q.1 q.2) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul measurable_snd).neg)).mul
      (hf.comp (hYp.comp (measurable_snd.prodMk measurable_fst)))
  have hgF : ∀ ω u, runG X lam β y ω u ≤ resF X β f y ω u := by
    intro ω u
    unfold runG resF
    calc ENNReal.ofReal (lam * Real.exp (-(β * u) + Shared.refl y 0 X (Real.toNNReal u) ω))
        = ENNReal.ofReal (Real.exp (-(β * u))) *
            ENNReal.ofReal (lam * Real.exp (Shared.refl y 0 X (Real.toNNReal u) ω)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, Real.exp_add]; congr 1; ring
      _ ≤ _ := by gcongr; exact hfl _ (reflY_nonneg hXL y _ ω)
  have hIm : ∀ S : Set ℝ, Measurable (fun ω => ∫⁻ u in S, runG X lam β y ω u) := fun S =>
    hgm.lintegral_prod_right'
  have hJm : ∀ S : Set ℝ, Measurable (fun ω => ∫⁻ u in S, resF X β f y ω u) := fun S =>
    hFm.lintegral_prod_right'
  have hRm : ∀ t : ℝ≥0, Measurable (fun ω => ENNReal.ofReal (Real.exp (-(β * t))) *
      resU Q X β f (Shared.refl y 0 X t ω)) := fun t =>
    ((measurable_resU hXL β hf).comp
      ((measurable_refl_past 𝓕 Q X hX y t).mono (𝓕.le t) le_rfl)).const_mul _
  have hij' : (i : ℝ) ≤ j := NNReal.coe_le_coe.2 hij
  have hd1 : Disjoint (Set.Ioc (0 : ℝ) i) (Set.Ioc (i : ℝ) j) :=
    Set.disjoint_left.2 fun x hx1 hx2 => absurd hx1.2 (not_le.2 hx2.1)
  have hd2 : Disjoint (Set.Ioc (i : ℝ) j) (Set.Ioi (j : ℝ)) :=
    Set.disjoint_left.2 fun x hx1 hx2 => absurd hx1.2 (not_le.2 hx2)
  have hsplitI : ∀ ω, ∫⁻ u in Set.Ioc (0 : ℝ) j, runG X lam β y ω u =
      (∫⁻ u in Set.Ioc (0 : ℝ) i, runG X lam β y ω u) +
        ∫⁻ u in Set.Ioc (i : ℝ) j, runG X lam β y ω u := by
    intro ω
    have hU : Set.Ioc (0 : ℝ) i ∪ Set.Ioc (i : ℝ) j = Set.Ioc (0 : ℝ) j :=
      Set.Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg i) hij'
    rw [← hU, lintegral_union measurableSet_Ioc hd1]
  have hsplitF : ∀ ω, ∫⁻ u in Set.Ioi (i : ℝ), resF X β f y ω u =
      (∫⁻ u in Set.Ioc (i : ℝ) j, resF X β f y ω u) +
        ∫⁻ u in Set.Ioi (j : ℝ), resF X β f y ω u := by
    intro ω
    have hU : Set.Ioc (i : ℝ) j ∪ Set.Ioi (j : ℝ) = Set.Ioi (i : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hij'
    rw [← hU, lintegral_union measurableSet_Ioi hd2]
  have hMi : ∫⁻ ω in A, (∫⁻ s in Set.Ioi (i : ℝ), resF X β f y ω s) ∂Q =
      ENNReal.ofReal (Real.exp (-(β * i))) * ∫⁻ ω in A, resU Q X β f (Shared.refl y 0 X i ω) ∂Q :=
    markov_resolvent 𝓕 Q X hX β y hf i hA
  have hMj : ∫⁻ ω in A, (∫⁻ s in Set.Ioi (j : ℝ), resF X β f y ω s) ∂Q =
      ENNReal.ofReal (Real.exp (-(β * j))) * ∫⁻ ω in A, resU Q X β f (Shared.refl y 0 X j ω) ∂Q :=
    markov_resolvent 𝓕 Q X hX β y hf j hAj
  unfold Lproc
  rw [lintegral_add_left (hRm j), lintegral_add_left (hRm i),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hMi, ← hMj]
  simp_rw [hsplitI, hsplitF]
  rw [lintegral_add_left (hIm (Set.Ioc (0 : ℝ) i)), lintegral_add_left (hJm (Set.Ioc (i : ℝ) j))]
  have hmono : ∫⁻ ω in A, (∫⁻ u in Set.Ioc (i : ℝ) j, runG X lam β y ω u) ∂Q ≤
      ∫⁻ ω in A, (∫⁻ u in Set.Ioc (i : ℝ) j, resF X β f y ω u) ∂Q :=
    lintegral_mono fun ω => lintegral_mono fun u => hgF ω u
  exact alg4 _ _ _ _ hmono

/-- A pathwise bound for `Y` on `[0, t]`. -/
lemma reflY_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (y : ℝ) (t : ℝ≥0) (ω : Ω) :
    ∃ M : ℝ, ∀ u : ℝ≥0, u ≤ t → Shared.refl y 0 X u ω ≤ M := by
  obtain ⟨C1, hC1⟩ := supP_bdd hX t ω
  obtain ⟨C2, hC2⟩ := bddAbove_of_cadlag (fun r => -X r ω)
    (fun s => (hX.right_continuous ω s).neg)
    (fun s hs => by
      obtain ⟨l, hl⟩ := hX.left_limits ω s hs
      exact ⟨-l, hl.neg⟩) t
  refine ⟨max y C1 + C2, fun u hu => ?_⟩
  rw [refl_eq_reflQ X y u ω (hX.right_continuous ω) (supP_bdd hX u ω),
    reflQ_eq u y _ (hX.right_continuous ω) (supP_bdd hX u ω)]
  have hS : sSup ((fun z => X z ω) '' Set.Iic u) ≤ C1 :=
    csSup_le ⟨X u ω, u, Set.mem_Iic.2 le_rfl, rfl⟩ (by
      rintro _ ⟨z, hz, rfl⟩
      exact hC1 ⟨z, Set.mem_Iic.2 ((Set.mem_Iic.1 hz).trans hu), rfl⟩)
  have hX2 : -X u ω ≤ C2 := hC2 ⟨u, Set.mem_Iic.2 hu, rfl⟩
  have := max_le_max (le_refl y) hS
  linarith

set_option maxHeartbeats 1000000 in
/-- `ofReal U_t = L_t` pathwise, with `U ≥ 0`. -/
lemma U_eq_L {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy Q X) (β lam y : ℝ) (hlam : 0 ≤ lam) (h : ℝ → ℝ) (f : ℝ → ℝ≥0∞)
    (hh : ∀ z, 0 ≤ z → 0 ≤ h z ∧ ENNReal.ofReal (h z) = resU Q X β f z) (t : ℝ≥0) (ω : Ω) :
    0 ≤ Real.exp (-β * (t : ℝ)) * h (Shared.refl y 0 X t ω)
      + lam * ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω) ∧
    ENNReal.ofReal (Real.exp (-β * (t : ℝ)) * h (Shared.refl y 0 X t ω)
      + lam * ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω)) =
      Lproc Q X β lam y f t ω := by
  obtain ⟨hh0, hh1⟩ := hh _ (reflY_nonneg hX y t ω)
  have hYp : Measurable (fun p : ℝ × Ω => Shared.refl y 0 X (Real.toNNReal p.1) p.2) :=
    (measurable_reflY hX).comp (measurable_const.prodMk measurable_id)
  have hem : Measurable (fun u : ℝ => Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω)) :=
    Real.measurable_exp.comp ((measurable_const.mul measurable_id).add
      (hYp.comp (measurable_id.prodMk measurable_const)))
  obtain ⟨M, hM⟩ := reflY_bound hX y t ω
  have hfin : ∫⁻ u in Set.Ioc (0 : ℝ) t,
      ENNReal.ofReal (Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ u in Set.Ioc (0 : ℝ) t,
      ENNReal.ofReal (Real.exp (|β| * t + M))) ?_ ?_
    · rw [setLIntegral_const, Real.volume_Ioc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · refine setLIntegral_mono' measurableSet_Ioc fun u hu => ?_
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have h1 : -β * u ≤ |β| * t := by
        have := neg_abs_le β
        have hu0 : 0 ≤ u := hu.1.le
        have hut : u ≤ (t : ℝ) := hu.2
        nlinarith [abs_nonneg β]
      have h2 := hM (Real.toNNReal u) ((Real.toNNReal_le_iff_le_coe).2 hu.2)
      linarith
  have hint : ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω) =
      (∫⁻ u in Set.Ioc (0 : ℝ) t,
        ENNReal.ofReal (Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω))).toReal := by
    rw [intervalIntegral.integral_of_le t.coe_nonneg,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun u => (Real.exp_pos _).le)
        hem.aestronglyMeasurable]
  have hI0 : 0 ≤ ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω) := by
    rw [hint]; exact ENNReal.toReal_nonneg
  have hA0 : 0 ≤ Real.exp (-β * (t : ℝ)) * h (Shared.refl y 0 X t ω) :=
    mul_nonneg (Real.exp_pos _).le hh0
  refine ⟨add_nonneg hA0 (mul_nonneg hlam hI0), ?_⟩
  have hRHS : Lproc Q X β lam y f t ω =
      ENNReal.ofReal (Real.exp (-(β * t))) * ENNReal.ofReal (h (Shared.refl y 0 X t ω)) +
        ENNReal.ofReal lam * ∫⁻ u in Set.Ioc (0 : ℝ) t,
          ENNReal.ofReal (Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω)) := by
    rw [Lproc, ← hh1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    refine lintegral_congr fun u => ?_
    rw [runG, ← ENNReal.ofReal_mul hlam, neg_mul]
  rw [hRHS, ENNReal.ofReal_add hA0 (mul_nonneg hlam hI0), ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_mul hlam, hint, ENNReal.ofReal_toReal hfin, neg_mul]

/-- C5: `U_t = e^{-βt} h(Y_t) + λ ∫_0^t e^{-βu + Y_u} du` is a `Q`-supermartingale whenever
`h = resU f` on `[0, ∞)` for some Borel `f ≥ λ e^z`. -/
theorem super_of_resolvent {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 Q X)
    (β lam y : ℝ) (hlam : 0 ≤ lam) (hy : 0 ≤ y) (h : ℝ → ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfl : ∀ z, 0 ≤ z → ENNReal.ofReal (lam * Real.exp z) ≤ f z)
    (hh : ∀ z, 0 ≤ z → 0 ≤ h z ∧ ENNReal.ofReal (h z) = resU Q X β f z) :
    Supermartingale (fun (t : ℝ≥0) ω => Real.exp (-β * (t : ℝ)) * h (Shared.refl y 0 X t ω)
      + lam * ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω)) 𝓕 Q := by
  have hXL := hX.isSNLevy
  set U : ℝ≥0 → Ω → ℝ := fun t ω => Real.exp (-β * (t : ℝ)) * h (Shared.refl y 0 X t ω)
      + lam * ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-β * u + Shared.refl y 0 X u.toNNReal ω)
    with hUdef
  have hUL := U_eq_L hXL β lam y hlam h f hh
  have hUt : ∀ t, U t = fun ω => (Lproc Q X β lam y f t ω).toReal := by
    intro t; funext ω
    rw [← (hUL t ω).2, ENNReal.toReal_ofReal (hUL t ω).1]
  have hL𝓕 : ∀ t, Measurable[𝓕 t] (Lproc Q X β lam y f t) := by
    intro t
    have hφ : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (lam * Real.exp (-(β * z.1) + z.2))) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
        ((measurable_const.mul measurable_fst).neg.add measurable_snd)))
    exact ((measurable_resU hXL β hf).comp (measurable_refl_past 𝓕 Q X hX y t)).const_mul _
      |>.add (measurable_runInt_past 𝓕 Q X hX y t hφ)
  have hLm : ∀ t, Measurable (Lproc Q X β lam y f t) := fun t => (hL𝓕 t).mono (𝓕.le t) le_rfl
  have hadp : Adapted 𝓕 U := fun t => by
    rw [hUt t]; exact ENNReal.measurable_toReal.comp (hL𝓕 t)
  have hL0 : ∫⁻ ω, Lproc Q X β lam y f 0 ω ∂Q = resU Q X β f y := by
    have : ∀ ω, Lproc Q X β lam y f 0 ω = resU Q X β f y := by
      intro ω
      unfold Lproc
      simp [reflY_zero hXL hy ω]
    simp only [this, lintegral_const, measure_univ, mul_one]
  have hfin0 : resU Q X β f y ≠ ⊤ := by
    rw [← (hh y hy).2]; exact ENNReal.ofReal_ne_top
  have hfinL : ∀ t, ∫⁻ ω, Lproc Q X β lam y f t ω ∂Q ≠ ⊤ := by
    intro t
    have h0 := super_core 𝓕 Q X hX β lam y hf hfl (show (0 : ℝ≥0) ≤ t from zero_le') (A := Set.univ) MeasurableSet.univ
    rw [Measure.restrict_univ, hL0] at h0
    exact ne_top_of_le_ne_top hfin0 h0
  have hint : ∀ t, Integrable (U t) Q := by
    intro t
    rw [hUt t]
    exact integrable_toReal_of_lintegral_ne_top (hLm t).aemeasurable (hfinL t)
  have hsetI : ∀ t (A : Set Ω), MeasurableSet A →
      ∫ ω in A, U t ω ∂Q = (∫⁻ ω in A, Lproc Q X β lam y f t ω ∂Q).toReal := by
    intro t A hA
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => (hUL t ω).1)
      (hint t).aestronglyMeasurable.restrict]
    congr 1
    exact lintegral_congr fun ω => (hUL t ω).2
  have hsub : Submartingale (-U) 𝓕 Q := by
    refine submartingale_of_setIntegral_le (hadp.stronglyAdapted.neg) (fun t => (hint t).neg) ?_
    intro i j hij A hA
    have hAm : MeasurableSet A := 𝓕.le i A hA
    simp only [Pi.neg_apply, integral_neg, neg_le_neg_iff]
    rw [hsetI j A hAm, hsetI i A hAm]
    refine ENNReal.toReal_mono ?_ (super_core 𝓕 Q X hX β lam y hf hfl hij hA)
    exact ne_top_of_le_ne_top (hfinL i) (setLIntegral_le_lintegral A _)
  have := hsub.neg
  simpa using this

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-! ## R3a: the `Q`-resolvent of `e^z k(z)` through the Esscher density and the Wiener-Hopf law -/

/-- The integrand `e^{max(y, a)} k((y - a)^+ - w)` (with `a` the running sup, `w = Ynr`). -/
noncomputable def wG (k : ℝ → ℝ≥0∞) (y : ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (z.1 + max (y - z.1) 0)) * k (max (y - z.1) 0 - z.2)

lemma measurable_wG {k : ℝ → ℝ≥0∞} (hk : Measurable k) (y : ℝ) : Measurable (wG k y) :=
  (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_fst.add
    ((measurable_const.sub measurable_fst).max measurable_const)))).mul
    (hk.comp (((measurable_const.sub measurable_fst).max measurable_const).sub measurable_snd))

/-- R3a: `resU_Q(e^z k)(y) = ∫_{law R} ∫_{Exp(κ)} e^{max(y,a)} k((y-a)^+ + R)`, `κ = κ_P(β + r)`. -/
theorem resU_esscher {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) {rr : ℝ} (hQ : Shared.IsEsscher 𝓕 P Q X rr)
    (β : ℝ) (hp : 0 < β + rr) {k : ℝ → ℝ≥0∞} (hk : Measurable k) (y : ℝ) :
    resU Q X β (fun z => ENNReal.ofReal (Real.exp z) * k z) y =
      ∫⁻ w, ∫⁻ a, wG k y (a, w)
        ∂(expLaw (kap P X (β + rr))) ∂(((nuq (β + rr)).prod P).map (Ynr X)) := by
  have hXL := hX.isSNLevy
  have hXm := hXL.measurable
  have := nuq_finite hp
  have hGm := measurable_wG hk y
  have hpair : Measurable (fun p : ℝ × Ω => (supP X p, Ynr X p)) :=
    (measurable_supP hXL).prodMk (measurable_Ynr hXL)
  have hH : Measurable (fun p : ℝ × Ω => wG k y (supP X p, Ynr X p)) := hGm.comp hpair
  have hc : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-((β + rr) * r)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)
  have h1 : ∀ r ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(β * r))) *
      ∫⁻ ω, ENNReal.ofReal (Real.exp (Shared.refl y 0 X (Real.toNNReal r) ω)) *
        k (Shared.refl y 0 X (Real.toNNReal r) ω) ∂Q =
      ENNReal.ofReal (Real.exp (-((β + rr) * r))) * ∫⁻ ω, wG k y (supP X (r, ω), Ynr X (r, ω)) ∂P := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
    have hY𝓕 := measurable_refl_past 𝓕 P X hX y (Real.toNNReal r)
    have hmeas : Measurable[𝓕 (Real.toNNReal r)] (fun ω =>
        ENNReal.ofReal (Real.exp (Shared.refl y 0 X (Real.toNNReal r) ω)) *
          k (Shared.refl y 0 X (Real.toNNReal r) ω)) :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hY𝓕)).mul (hk.comp hY𝓕)
    rw [esscher_lintegral hQ hXm (Real.toNNReal r) hmeas,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ω => ?_
    have hY := refl_eq_Yform hXL y (r, ω)
    have hcoe : ((Real.toNNReal r : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr0
    have hX' : X (Real.toNNReal r) ω = supP X (r, ω) + Ynr X (r, ω) := by unfold supP; ring
    simp only [essD, wG] at hY ⊢
    rw [hY, hcoe, hX']
    calc ENNReal.ofReal (Real.exp (-(β * r))) *
          (ENNReal.ofReal (Real.exp (supP X (r, ω) + Ynr X (r, ω) - rr * r)) *
            (ENNReal.ofReal (Real.exp (max (y - supP X (r, ω)) 0 - Ynr X (r, ω))) *
              k (max (y - supP X (r, ω)) 0 - Ynr X (r, ω))))
        = ENNReal.ofReal (Real.exp (-(β * r)) * Real.exp (supP X (r, ω) + Ynr X (r, ω) - rr * r) *
            Real.exp (max (y - supP X (r, ω)) 0 - Ynr X (r, ω))) *
              k (max (y - supP X (r, ω)) 0 - Ynr X (r, ω)) := by
          rw [ENNReal.ofReal_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le,
            ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ = ENNReal.ofReal (Real.exp (-((β + rr) * r)) *
            Real.exp (supP X (r, ω) + max (y - supP X (r, ω)) 0)) *
              k (max (y - supP X (r, ω)) 0 - Ynr X (r, ω)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 3
          ring
      _ = _ := by rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; ring
  calc resU Q X β (fun z => ENNReal.ofReal (Real.exp z) * k z) y
      = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-((β + rr) * r))) *
          ∫⁻ ω, wG k y (supP X (r, ω), Ynr X (r, ω)) ∂P :=
        setLIntegral_congr_fun measurableSet_Ioi h1
    _ = ∫⁻ p, wG k y (supP X p, Ynr X p) ∂((nuq (β + rr)).prod P) := by
        rw [lintegral_prod _ hH.aemeasurable,
          lintegral_withDensity_eq_lintegral_mul _ hc hH.lintegral_prod_right']
        rfl
    _ = ∫⁻ z, wG k y z ∂(((nuq (β + rr)).prod P).map (fun p => (supP X p, Ynr X p))) :=
        (lintegral_map hGm hpair).symm
    _ = ∫⁻ z, wG k y z ∂((expLaw (kap P X (β + rr))).prod (((nuq (β + rr)).prod P).map (Ynr X))) := by
        rw [joint_law 𝓕 P X hX hp]
    _ = _ := lintegral_prod_symm _ hGm.aemeasurable

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology

/-! ## R3b: the law of `R = -Ynr` under `nuq q ⊗ P` through the scale function -/

lemma lint_exp_tail {κ R u : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hRu : R ≤ u) :
    ∫⁻ x in Set.Ioc (0 : ℝ) u, (if R ≤ x then ENNReal.ofReal (κ * Real.exp (κ * x)) else 0) =
      ENNReal.ofReal (Real.exp (κ * u) - Real.exp (κ * R)) := by
  have hcont : Continuous (fun x : ℝ => κ * Real.exp (κ * x)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hind : (fun x : ℝ => if R ≤ x then ENNReal.ofReal (κ * Real.exp (κ * x)) else 0) =
      (Set.Ici R).indicator (fun x => ENNReal.ofReal (κ * Real.exp (κ * x))) := by
    funext x; simp only [Set.indicator, Set.mem_Ici]
  rw [hind, setLIntegral_indicator measurableSet_Ici, Set.inter_comm]
  have hset : ∫⁻ x in Set.Ioc (0 : ℝ) u ∩ Set.Ici R, ENNReal.ofReal (κ * Real.exp (κ * x)) =
      ∫⁻ x in Set.Ioc R u, ENNReal.ofReal (κ * Real.exp (κ * x)) := by
    rcases hR.eq_or_lt with h0 | hpos
    · subst h0
      congr 2
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici]
      constructor
      · rintro ⟨h1, -⟩; exact h1
      · rintro h1; exact ⟨h1, h1.1.le⟩
    · have he : Set.Ioc (0 : ℝ) u ∩ Set.Ici R = Set.Icc R u := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
        constructor
        · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
      rw [he]
      exact setLIntegral_congr Ioc_ae_eq_Icc.symm
  rw [hset, ← ofReal_integral_eq_lintegral_ofReal
    ((hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
    (ae_of_all _ fun x => mul_nonneg hκ (Real.exp_pos _).le),
    ← intervalIntegral.integral_of_le hRu]
  congr 1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => Real.exp (κ * x))
    (fun x _ => by
      have h := ((hasDerivAt_id x).const_mul κ).exp
      simp only [id, mul_one] at h
      rw [mul_comm] at h
      exact h)
    (hcont.intervalIntegrable _ _)

/-- `e^{κ Y} 1{-Y ≤ x}` (the integrand of `Gq`). -/
noncomputable def gR {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (κ x : ℝ) (p : ℝ × Ω) : ℝ≥0∞ :=
  if -Ynr X p ≤ x then ENNReal.ofReal (Real.exp (κ * Ynr X p)) else 0

/-- R3b (ENNReal form): `e^{κu} G(u) = ∫_0^u κe^{κx} G(x) dx + μ{R ≤ u}`, i.e.
`μ{R ≤ u} = W(u)/κ - ∫_0^u W` for `u > 0`. -/
theorem rho_le_enn {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (Real.exp (kap P X q * u)) * Gq P X q u =
      (∫⁻ x in Set.Ioc (0 : ℝ) u, ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x)) *
        Gq P X q x) + ((nuq q).prod P) {p | -Ynr X p ≤ u} := by
  have hXL := hX.isSNLevy
  have := nuq_finite hq
  have hκ : 0 < kap P X q := kap_pos 𝓕 P X hX hq
  have hY := measurable_Ynr hXL
  have hgR : Measurable (fun z : ℝ × (ℝ × Ω) => gR X (kap P X q) z.1 z.2) :=
    Measurable.ite (measurableSet_le (hY.comp measurable_snd).neg measurable_fst)
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (hY.comp measurable_snd)))) measurable_const
  have hk : Measurable (fun x : ℝ => ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
  have hφ : Measurable (fun z : ℝ × (ℝ × Ω) =>
      ENNReal.ofReal (kap P X q * Real.exp (kap P X q * z.1)) * gR X (kap P X q) z.1 z.2) :=
    (hk.comp measurable_fst).mul hgR
  have hG : ∀ x, Gq P X q x = ∫⁻ p, gR X (kap P X q) x p ∂((nuq q).prod P) := fun x => rfl
  have hswap : (∫⁻ x in Set.Ioc (0 : ℝ) u, ∫⁻ p,
      ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x)) * gR X (kap P X q) x p
        ∂((nuq q).prod P)) =
      ∫⁻ p, (∫⁻ x in Set.Ioc (0 : ℝ) u,
        ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x)) * gR X (kap P X q) x p)
          ∂((nuq q).prod P) :=
    lintegral_lintegral_swap (by exact hφ.aemeasurable)
  have hset : ((nuq q).prod P) {p | -Ynr X p ≤ u} =
      ∫⁻ p, (if -Ynr X p ≤ u then 1 else 0) ∂((nuq q).prod P) := by
    have hmS : MeasurableSet {p : ℝ × Ω | -Ynr X p ≤ u} := measurableSet_le hY.neg measurable_const
    rw [← lintegral_indicator_one hmS]
    congr 1
  have hin : ∀ x, ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x)) * Gq P X q x =
      ∫⁻ p, ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x)) * gR X (kap P X q) x p
        ∂((nuq q).prod P) := by
    intro x; rw [hG, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hInm : Measurable (fun p : ℝ × Ω => ∫⁻ x in Set.Ioc (0 : ℝ) u,
      ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x)) * gR X (kap P X q) x p) :=
    (hφ.comp (measurable_snd.prodMk measurable_fst)).lintegral_prod_right'
  simp_rw [hin]
  rw [hswap, hset, hG u, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left hInm]
  refine lintegral_congr fun p => ?_
  have hR0 : 0 ≤ -Ynr X p := by have := Ynr_nonpos hXL p; linarith
  by_cases hRu : -Ynr X p ≤ u
  · have hrw : ∀ x, ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x)) * gR X (kap P X q) x p =
        ENNReal.ofReal (Real.exp (kap P X q * Ynr X p)) *
          (if -Ynr X p ≤ x then ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x)) else 0) := by
      intro x; unfold gR; split_ifs <;> simp [mul_comm]
    simp_rw [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lint_exp_tail hκ.le hR0 hRu]
    unfold gR
    simp only [hRu, if_true]
    have hnn : 0 ≤ Real.exp (kap P X q * Ynr X p) *
        (Real.exp (kap P X q * u) - Real.exp (kap P X q * -Ynr X p)) :=
      mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left hRu hκ.le)))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add hnn zero_le_one]
    congr 1
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    have h0 : kap P X q * Ynr X p + kap P X q * -Ynr X p = 0 := by ring
    rw [h0, Real.exp_zero]
    ring_nf
  · have hz : ∫⁻ x in Set.Ioc (0 : ℝ) u,
        ENNReal.ofReal (kap P X q * Real.exp (kap P X q * x)) * gR X (kap P X q) x p = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0) (fun x hx => by
        have : ¬ (-Ynr X p ≤ x) := fun h => hRu (h.trans hx.2)
        simp [gR, this])]
      exact lintegral_zero
    rw [hz]
    unfold gR
    simp [hRu]

end Avram2004.Markov92562e40

set_option autoImplicit false

open MeasureTheory Filter Topology Set

namespace Avram2004.Markov92562e40

/-- Abstract `Z(x) = 1 + p ∫_{(-∞,x]} W`. -/
noncomputable def Zf (W : ℝ → ℝ) (p x : ℝ) : ℝ := 1 + p * ∫ z in Set.Iic x, W z

section R3c

variable {W : ℝ → ℝ}

lemma W_integrableOn_Iic (hW0 : ∀ x ≤ 0, W x = 0) (hWi : ∀ b, IntegrableOn W (Ioc 0 b))
    (b : ℝ) : IntegrableOn W (Iic b) := by
  have h0 : IntegrableOn W (Iic 0) :=
    (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Iic 0)).congr_fun
      (fun x hx => (hW0 x hx).symm) measurableSet_Iic
  refine (h0.union (hWi (max b 0))).mono_set ?_
  intro x hx
  by_cases h : x ≤ 0
  · exact Or.inl h
  · exact Or.inr ⟨lt_of_not_ge h, le_trans hx (le_max_left _ _)⟩

lemma W_intervalIntegrable (hW0 : ∀ x ≤ 0, W x = 0) (hWi : ∀ b, IntegrableOn W (Ioc 0 b))
    (a b : ℝ) : IntervalIntegrable W volume a b :=
  ⟨(W_integrableOn_Iic hW0 hWi b).mono_set Ioc_subset_Iic_self,
    (W_integrableOn_Iic hW0 hWi a).mono_set Ioc_subset_Iic_self⟩

lemma setIntegral_Iic_W (hW0 : ∀ x ≤ 0, W x = 0) (x : ℝ) :
    ∫ z in Set.Iic x, W z = ∫ z in (0:ℝ)..(max x 0), W z := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, intervalIntegral.integral_same]
    exact setIntegral_eq_zero_of_forall_eq_zero (fun z hz => hW0 z (le_trans hz hx))
  · rw [max_eq_left hx, intervalIntegral.integral_of_le hx]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic
      Ioc_subset_Iic_self ?_
    intro z hz
    have : ¬ (0 < z) := fun h => hz.2 ⟨h, hz.1⟩
    exact hW0 z (le_of_not_gt this)

lemma Zf_le_zero (hW0 : ∀ x ≤ 0, W x = 0) (p : ℝ) {x : ℝ} (hx : x ≤ 0) : Zf W p x = 1 := by
  unfold Zf
  rw [setIntegral_Iic_W hW0, max_eq_right hx, intervalIntegral.integral_same]
  ring

lemma Zf_pos_eq (hW0 : ∀ x ≤ 0, W x = 0) (p : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Zf W p x = 1 + p * ∫ z in (0:ℝ)..x, W z := by
  unfold Zf
  rw [setIntegral_Iic_W hW0, max_eq_left hx]

lemma continuous_Zf (hW0 : ∀ x ≤ 0, W x = 0) (hWi : ∀ b, IntegrableOn W (Ioc 0 b)) (p : ℝ) :
    Continuous (Zf W p) := by
  have h : Zf W p = fun x => 1 + p * ∫ z in (0:ℝ)..(max x 0), W z := by
    funext x; unfold Zf; rw [setIntegral_Iic_W hW0]
  rw [h]
  exact continuous_const.add (continuous_const.mul
    ((intervalIntegral.continuous_primitive (W_intervalIntegrable hW0 hWi) 0).comp
      (continuous_id.max continuous_const)))

lemma hasDerivAt_Zf (hW0 : ∀ x ≤ 0, W x = 0) (hWc : ContinuousOn W (Ioi 0))
    (hWi : ∀ b, IntegrableOn W (Ioc 0 b)) (p : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (Zf W p) (p * W u) u := by
  rcases lt_or_gt_of_ne hu with hneg | hpos
  · have hev : (fun _ : ℝ => (1 : ℝ)) =ᶠ[𝓝 u] Zf W p := by
      filter_upwards [Iio_mem_nhds hneg] with x hx
      exact (Zf_le_zero hW0 p (le_of_lt hx)).symm
    rw [hW0 u hneg.le, mul_zero]
    exact (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq hev.symm
  · have hI : HasDerivAt (fun x => ∫ z in (0:ℝ)..x, W z) (W u) u :=
      intervalIntegral.integral_hasDerivAt_right (W_intervalIntegrable hW0 hWi 0 u)
        (hWc.stronglyMeasurableAtFilter isOpen_Ioi u hpos)
        (hWc.continuousAt (Ioi_mem_nhds hpos))
    have h2 : HasDerivAt (fun x => 1 + p * ∫ z in (0:ℝ)..x, W z) (p * W u) u :=
      (hI.const_mul p).const_add 1
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hpos] with x hx
    exact Zf_pos_eq hW0 p (le_of_lt hx)

/-- R3c key identity: `∫_0^y κ e^{-κa} G(c+a) da = Z(c) - e^{-κy} Z(c+y)` when
`G = Z - (p/κ) W` off `0`. -/
lemma exp_G_identity (hW0 : ∀ x ≤ 0, W x = 0) (hWc : ContinuousOn W (Ioi 0))
    (hWi : ∀ b, IntegrableOn W (Ioc 0 b)) (p : ℝ) {κ : ℝ} (hκ : κ ≠ 0) {G : ℝ → ℝ}
    (hG : ∀ u, u ≠ 0 → G u = Zf W p u - p / κ * W u) (c y : ℝ) (hy : 0 ≤ y) :
    ∫ a in (0:ℝ)..y, κ * Real.exp (-(κ * a)) * G (c + a) =
      Zf W p c - Real.exp (-(κ * y)) * Zf W p (c + y) := by
  set φ : ℝ → ℝ := fun a => Real.exp (-(κ * a)) * Zf W p (c + a) with hφ
  set φ' : ℝ → ℝ := fun a => -κ * Real.exp (-(κ * a)) * Zf W p (c + a)
      + Real.exp (-(κ * a)) * (p * W (c + a)) with hφ'
  have hZc := continuous_Zf hW0 hWi p
  have hexp : ∀ a, HasDerivAt (fun a : ℝ => Real.exp (-(κ * a))) (-κ * Real.exp (-(κ * a))) a := by
    intro a
    have h1 : HasDerivAt (fun a : ℝ => -(κ * a)) (-κ) a := by
      have := ((hasDerivAt_id a).const_mul κ).neg
      simp only [id, mul_one] at this
      exact this
    have := h1.exp
    rw [mul_comm] at this
    exact this
  have hFTC : ∫ a in (0:ℝ)..y, φ' a = φ y - φ 0 := by
    refine integral_eq_of_hasDerivAt_off_countable_of_le φ φ' hy (Set.countable_singleton (-c))
      ?_ ?_ ?_
    · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)).mul
        (hZc.comp (continuous_const.add continuous_id))).continuousOn
    · intro a ha
      have hne : c + a ≠ 0 := by
        intro h; exact ha.2 (by simp; linarith)
      have hZ := (hasDerivAt_Zf hW0 hWc hWi p hne).comp_const_add c a
      exact (hexp a).mul hZ
    · have hc1 : Continuous (fun a : ℝ => -κ * Real.exp (-(κ * a)) * Zf W p (c + a)) :=
        (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)).mul
          (hZc.comp (continuous_const.add continuous_id))
      have hWs : IntervalIntegrable (fun a => W (c + a)) volume 0 y := by
        have := (W_intervalIntegrable hW0 hWi c (c + y)).comp_add_left c
        simpa using this
      have hW2 : IntervalIntegrable (fun a => Real.exp (-(κ * a)) * (p * W (c + a))) volume 0 y :=
        (hWs.const_mul p).continuousOn_mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
      exact (hc1.intervalIntegrable 0 y).add hW2
  have hae : ∀ᵐ a ∂(volume : Measure ℝ), a ∈ Set.uIoc (0:ℝ) y →
      κ * Real.exp (-(κ * a)) * G (c + a) = -φ' a := by
    have hne : ∀ᵐ a ∂(volume : Measure ℝ), a ≠ -c := by
      rw [ae_iff]; simp
    filter_upwards [hne] with a ha _
    have h0 : c + a ≠ 0 := by intro h; exact ha (by linarith)
    rw [hG _ h0, hφ']
    field_simp
    ring
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_neg, hFTC, hφ]
  simp only [mul_zero, neg_zero, Real.exp_zero, one_mul, add_zero]
  ring

/-- Abstract κ_* facts. -/
lemma kappa_facts {H Hr : ℝ → ℝ} {T ks : ℝ} (hks : ks = sInf {x | 0 ≤ x ∧ H x ≤ T})
    (hH0 : T < H 0) (hHr : ∀ u, 0 < u → Hr u = H u)
    (hrc : ∀ u, 0 ≤ u → ContinuousWithinAt Hr (Ici u) u) (hHc : ContinuousOn H (Ioi 0))
    (hne : ∃ x, 0 ≤ x ∧ H x ≤ T) :
    0 ≤ ks ∧ Hr ks ≤ T ∧ (Hr ks < T → ks = 0) := by
  set S := {x | 0 ≤ x ∧ H x ≤ T} with hSdef
  have hS : S.Nonempty := hne
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  have h0 : 0 ≤ ks := hks ▸ le_csInf hS (fun x hx => hx.1)
  have hpos_of_mem : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h] at hx; exact absurd hx.2 (not_le.mpr hH0)
    · exact h
  refine ⟨h0, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hev : ∀ᶠ x in 𝓝[≥] ks, Hr x ∈ Ioi T := (hrc ks h0).eventually (Ioi_mem_nhds hlt)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have hlt' : sInf S < u := hks ▸ hu
    obtain ⟨x, hxS, hxu⟩ := exists_lt_of_csInf_lt hS hlt'
    have hkx : ks ≤ x := hks ▸ csInf_le hbdd hxS
    have h1 : T < Hr x := hsub ⟨hkx, hxu⟩
    rw [hHr x (hpos_of_mem x hxS)] at h1
    exact absurd hxS.2 (not_le.mpr h1)
  · intro hlt
    by_contra hne0
    have hpos : 0 < ks := lt_of_le_of_ne h0 (Ne.symm hne0)
    have hHk : H ks < T := by rw [← hHr ks hpos]; exact hlt
    have hca : ContinuousAt H ks := hHc.continuousAt (Ioi_mem_nhds hpos)
    have hev : ∀ᶠ x in 𝓝 ks, H x < T := hca.eventually (Iio_mem_nhds hHk)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    set x := ks - min ε ks / 2 with hx
    have hm : 0 < min ε ks := lt_min hε hpos
    have hxlt : x < ks := by rw [hx]; linarith
    have hxpos : 0 ≤ x := by
      have : min ε ks ≤ ks := min_le_right _ _
      rw [hx]; linarith
    have hdist : dist x ks < ε := by
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have : min ε ks ≤ ε := min_le_left _ _
      rw [hx]; linarith
    have hxS : x ∈ S := ⟨hxpos, (hball hdist).le⟩
    have := hks ▸ csInf_le hbdd hxS
    linarith

end R3c

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology Set

lemma measurable_expDens (κ : ℝ) :
    Measurable (fun a : ℝ => ENNReal.ofReal (κ * Real.exp (-(κ * a)))) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul
    (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg))

/-- Inner `a`-integral of `wG` against `Exp(κ)`. -/
lemma expLaw_wG {κ : ℝ} (hκ : 1 < κ) (k : ℝ → ℝ≥0∞) {y : ℝ} (hy : 0 ≤ y) (w : ℝ) :
    ∫⁻ a, wG k y (a, w) ∂(expLaw κ) =
      ENNReal.ofReal (Real.exp y) *
        (∫⁻ a in Set.Ioo 0 y, ENNReal.ofReal (κ * Real.exp (-(κ * a))) * k (y - a - w))
      + ENNReal.ofReal (κ * Real.exp ((1 - κ) * y) / (κ - 1)) * k (-w) := by
  have hκ0 : 0 < κ := by linarith
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_expDens κ)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← lintegral_inter_add_sdiff _ _ (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) y)),
    Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
  congr 1
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) y)) ?_
    intro a ha
    have hm : max (y - a) 0 = y - a := max_eq_left (by linarith [ha.2])
    simp only [Pi.mul_apply, wG, hm, add_sub_cancel]
    try ring
  · have h2 : EqOn (fun a => ((fun a : ℝ => ENNReal.ofReal (κ * Real.exp (-(κ * a)))) *
        fun a => wG k y (a, w)) a)
        (fun a => k (-w) * ENNReal.ofReal κ * ENNReal.ofReal (Real.exp ((1 - κ) * a)))
        (Ioi 0 \ Ioo 0 y) := by
      intro a ha
      have hya : y ≤ a := by
        by_contra h; exact ha.2 ⟨ha.1, lt_of_not_ge h⟩
      have hm : max (y - a) 0 = 0 := max_eq_right (by linarith)
      simp only [Pi.mul_apply, wG, hm, add_zero, zero_sub]
      have e : ENNReal.ofReal (κ * Real.exp (-(κ * a))) * ENNReal.ofReal (Real.exp a) =
          ENNReal.ofReal κ * ENNReal.ofReal (Real.exp ((1 - κ) * a)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hκ0.le, mul_assoc,
          ← Real.exp_add]
        ring_nf
      calc _ = (ENNReal.ofReal (κ * Real.exp (-(κ * a))) * ENNReal.ofReal (Real.exp a)) * k (-w) := by
            ring
        _ = _ := by rw [e]; ring
    have hme : Measurable (fun a : ℝ => ENNReal.ofReal (Real.exp ((1 - κ) * a))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
    rw [setLIntegral_congr_fun (measurableSet_Ioi.diff measurableSet_Ioo) h2,
      lintegral_const_mul _ hme]
    have hsq : ∫⁻ a in Ioi 0 \ Ioo 0 y, ENNReal.ofReal (Real.exp ((1 - κ) * a)) =
        ∫⁻ a in Ioi y, ENNReal.ofReal (Real.exp ((1 - κ) * a)) := by
      apply le_antisymm
      · calc _ ≤ ∫⁻ a in Ici y, ENNReal.ofReal (Real.exp ((1 - κ) * a)) := by
              apply lintegral_mono_set
              intro a ha
              by_contra h
              exact ha.2 ⟨ha.1, lt_of_not_ge h⟩
          _ = _ := (setLIntegral_congr Ioi_ae_eq_Ici).symm
      · apply lintegral_mono_set
        intro a ha
        exact ⟨lt_of_le_of_lt hy ha, fun h => absurd h.2 (not_lt.mpr (le_of_lt ha))⟩
    rw [hsq, lintegral_exp_Ioi_c (by linarith : 1 - κ < 0), mul_assoc,
      ← ENNReal.ofReal_mul hκ0.le, mul_comm]
    congr 2
    have h1 : (1:ℝ) - κ ≠ 0 := by linarith
    have h2 : κ - 1 ≠ 0 := by linarith
    field_simp
    ring

/-- Outer integral over the law `ρ` of `Ynr`. -/
lemma lint_wG_split {κ : ℝ} (hκ : 1 < κ) {k : ℝ → ℝ≥0∞} (hk : Measurable k) {y : ℝ} (hy : 0 ≤ y)
    (ρ : Measure ℝ) [SFinite ρ] :
    ∫⁻ w, ∫⁻ a, wG k y (a, w) ∂(expLaw κ) ∂ρ =
      ENNReal.ofReal (Real.exp y) * (∫⁻ a in Set.Ioo 0 y,
          ENNReal.ofReal (κ * Real.exp (-(κ * a))) * ∫⁻ w, k (y - a - w) ∂ρ)
      + ENNReal.ofReal (κ * Real.exp ((1 - κ) * y) / (κ - 1)) * ∫⁻ w, k (-w) ∂ρ := by
  simp_rw [expLaw_wG hκ k hy]
  rw [lintegral_add_right _ (show Measurable (fun w : ℝ =>
      ENNReal.ofReal (κ * Real.exp ((1 - κ) * y) / (κ - 1)) * k (-w)) from
      (hk.comp measurable_neg).const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 2
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun a => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · exact (((measurable_expDens κ).comp measurable_snd).mul
      (hk.comp ((measurable_const.sub measurable_snd).sub measurable_fst))).aemeasurable

/-- The resolvent weight `k(z) = λ + (p-λ)1{z>κ*} + c 1{z=0}` (`f = e^z k`). -/
noncomputable def kCR (lam p ks c : ℝ) (z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal lam + (if ks < z then ENNReal.ofReal (p - lam) else 0) +
    (if z = 0 then ENNReal.ofReal c else 0)

lemma measurable_kCR (lam p ks c : ℝ) : Measurable (kCR lam p ks c) := by
  have h1 : Measurable (fun z : ℝ => if ks < z then ENNReal.ofReal (p - lam) else 0) :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have h2 : Measurable (fun z : ℝ => if z = 0 then ENNReal.ofReal c else 0) :=
    Measurable.ite (measurableSet_singleton (0:ℝ)) measurable_const measurable_const
  exact ((measurable_const : Measurable (fun _ : ℝ => ENNReal.ofReal lam)).add h1).add h2

lemma lint_kCR (lam p ks c t : ℝ) (ρ : Measure ℝ) :
    ∫⁻ w, kCR lam p ks c (t - w) ∂ρ = ENNReal.ofReal lam * ρ univ +
      ENNReal.ofReal (p - lam) * ρ {w | ks < t - w} + ENNReal.ofReal c * ρ {w | t - w = 0} := by
  have hm1 : MeasurableSet {w : ℝ | ks < t - w} :=
    measurableSet_lt measurable_const (measurable_const.sub measurable_id)
  have hm2 : MeasurableSet {w : ℝ | t - w = 0} :=
    measurableSet_eq_fun (measurable_const.sub measurable_id) measurable_const
  have e1 : (fun w => if ks < t - w then ENNReal.ofReal (p - lam) else 0) =
      {w : ℝ | ks < t - w}.indicator (fun _ => ENNReal.ofReal (p - lam)) := by
    funext w; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have e2 : (fun w => if t - w = 0 then ENNReal.ofReal c else 0) =
      {w : ℝ | t - w = 0}.indicator (fun _ => ENNReal.ofReal c) := by
    funext w; simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  unfold kCR
  rw [lintegral_add_right _ (show Measurable (fun w : ℝ => if t - w = 0 then ENNReal.ofReal c else 0)
      from e2 ▸ (measurable_const.indicator hm2)),
    lintegral_add_right _ (show Measurable (fun w : ℝ => if ks < t - w then ENNReal.ofReal (p - lam)
      else 0) from e1 ▸ (measurable_const.indicator hm1)), lintegral_const, e1, e2,
    lintegral_indicator_const hm1, lintegral_indicator_const hm2]

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology Set

/-- `G(u) = 1 - p ρ{R ≤ u}` for the law `ρ` of `Ynr = -R`. -/
noncomputable def Gρ (ρ : Measure ℝ) (p u : ℝ) : ℝ := 1 - p * (ρ {w | -w ≤ u}).toReal

section R3e

set_option linter.unusedSectionVars false

variable {ρ : Measure ℝ} [IsFiniteMeasure ρ] {p : ℝ}

lemma toReal_rho_le (hρu : ρ univ = ENNReal.ofReal (1 / p)) (hp : 0 < p) (u : ℝ) :
    (ρ {w | -w ≤ u}).toReal ≤ 1 / p := by
  have h := measure_mono (μ := ρ) (subset_univ {w : ℝ | -w ≤ u})
  rw [hρu] at h
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

lemma Gρ_nonneg (hρu : ρ univ = ENNReal.ofReal (1 / p)) (hp : 0 < p) (u : ℝ) : 0 ≤ Gρ ρ p u := by
  unfold Gρ
  have h1 := toReal_rho_le hρu hp u
  have h2 : p * (ρ {w | -w ≤ u}).toReal ≤ p * (1 / p) := mul_le_mul_of_nonneg_left h1 hp.le
  rw [mul_one_div_cancel hp.ne'] at h2
  linarith

lemma Gρ_neg (hρpos : ρ {w | 0 < w} = 0) {u : ℝ} (hu : u < 0) : Gρ ρ p u = 1 := by
  unfold Gρ
  have : ρ {w | -w ≤ u} = 0 := by
    refine measure_mono_null ?_ hρpos
    intro w hw
    simp only [mem_ofPred_eq] at hw ⊢
    linarith
  rw [this]; simp

lemma Gρ_antitone (hp : 0 ≤ p) : Antitone (Gρ ρ p) := by
  intro u v huv
  unfold Gρ
  have h : ρ {w | -w ≤ u} ≤ ρ {w | -w ≤ v} := by
    refine measure_mono ?_
    intro w hw
    simp only [mem_ofPred_eq] at hw ⊢
    linarith
  have := ENNReal.toReal_mono (measure_ne_top ρ _) h
  nlinarith

lemma rhoG_gt (hρu : ρ univ = ENNReal.ofReal (1 / p)) (hp : 0 < p) (ks t : ℝ) :
    ρ {w | ks < t - w} = ENNReal.ofReal (Gρ ρ p (ks - t) / p) := by
  have hs : {w : ℝ | ks < t - w} = {w | -w ≤ ks - t}ᶜ := by
    ext w; simp only [mem_ofPred_eq, mem_compl_iff, not_le]; constructor <;> intro h <;> linarith
  have hm : MeasurableSet {w : ℝ | -w ≤ ks - t} := measurableSet_le measurable_neg measurable_const
  rw [hs, measure_compl hm (measure_ne_top ρ _), hρu,
    ← ENNReal.ofReal_toReal (measure_ne_top ρ {w : ℝ | -w ≤ ks - t}),
    ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
  congr 1
  unfold Gρ
  field_simp

lemma rho_eq_pos (hρpos : ρ {w | 0 < w} = 0) {t : ℝ} (ht : 0 < t) : ρ {w | t - w = 0} = 0 := by
  refine measure_mono_null ?_ hρpos
  intro w hw
  simp only [mem_ofPred_eq] at hw ⊢
  linarith

lemma rho_eq_zero (hρpos : ρ {w | 0 < w} = 0) :
    ρ {w : ℝ | (0:ℝ) - w = 0} = ENNReal.ofReal (ρ {w | -w ≤ 0}).toReal := by
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  apply le_antisymm
  · refine measure_mono ?_
    intro w hw
    simp only [mem_ofPred_eq] at hw ⊢
    linarith
  · calc ρ {w : ℝ | -w ≤ 0} ≤ ρ ({w : ℝ | (0:ℝ) - w = 0} ∪ {w | 0 < w}) := by
          refine measure_mono ?_
          intro w hw
          simp only [mem_ofPred_eq, mem_union] at hw ⊢
          rcases eq_or_lt_of_le (neg_nonpos.mp hw) with h | h
          · left; linarith
          · right; exact h
      _ ≤ _ + _ := measure_union_le _ _
      _ = _ := by rw [hρpos, add_zero]

end R3e

lemma Zf_smul (W : ℝ → ℝ) (p q x : ℝ) : Zf (fun z => q * W z) p x = 1 + q * (Zf W p x - 1) := by
  unfold Zf; rw [integral_const_mul]; ring

set_option maxHeartbeats 1000000 in
/-- R3c assembled for an abstract law `ρ`: the resolvent of `f = e^z kCR` is `h`. -/
lemma resolvent_value {ρ : Measure ℝ} [IsFiniteMeasure ρ] {p lam κ ks c : ℝ} {W : ℝ → ℝ}
    (hlam : 0 < lam) (hpl : lam < p) (hκ : 1 < κ)
    (hρu : ρ univ = ENNReal.ofReal (1 / p)) (hρpos : ρ {w | 0 < w} = 0)
    (hW0 : ∀ x ≤ 0, W x = 0) (hWc : ContinuousOn W (Ioi 0)) (hWi : ∀ b, IntegrableOn W (Ioc 0 b))
    (hGW : ∀ u, 0 < u → Gρ ρ p u = Zf W p u - p / κ * W u)
    (hks1 : κ * Gρ ρ p ks - (κ - 1) * Zf W p ks ≤ -lam / (p - lam))
    (hks2 : κ * Gρ ρ p ks - (κ - 1) * Zf W p ks < -lam / (p - lam) → ks = 0)
    (hc : c = -(lam + (p - lam) * (κ * Gρ ρ p ks - (κ - 1) * Zf W p ks)) /
      (p * κ * (ρ {w | -w ≤ 0}).toReal))
    {y : ℝ} (hy : 0 ≤ y) :
    ∫⁻ w, ∫⁻ a, wG (kCR lam p ks c) y (a, w) ∂(expLaw κ) ∂ρ =
      ENNReal.ofReal ((p - lam) * Real.exp y * Zf W p (ks - y) / p + lam * Real.exp y / p) := by
  have hp : 0 < p := by linarith
  have hpl' : 0 < p - lam := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : κ - 1 ≠ 0 := by linarith
  have hm0nn : 0 ≤ (ρ {w : ℝ | -w ≤ 0}).toReal := ENNReal.toReal_nonneg
  have hΔle : lam + (p - lam) * (κ * Gρ ρ p ks - (κ - 1) * Zf W p ks) ≤ 0 := by
    have h1 := mul_le_mul_of_nonneg_left hks1 hpl'.le
    have h2 : (p - lam) * (-lam / (p - lam)) = -lam := by field_simp
    linarith
  have hcnn : 0 ≤ c := by
    rw [hc]; exact div_nonneg (by linarith) (by positivity)
  have hkey : lam + (p - lam) * (κ * Gρ ρ p ks - (κ - 1) * Zf W p ks) +
      p * κ * c * (ρ {w : ℝ | -w ≤ 0}).toReal = 0 := by
    by_cases hm : (ρ {w : ℝ | -w ≤ 0}).toReal = 0
    · have hc0 : c = 0 := by rw [hc, hm, mul_zero, div_zero]
      rw [hc0, mul_zero, zero_mul, add_zero]
      by_contra hne
      have hlt := lt_of_le_of_ne hΔle hne
      have hHlt : κ * Gρ ρ p ks - (κ - 1) * Zf W p ks < -lam / (p - lam) := by
        by_contra h
        push Not at h
        have h1 := mul_le_mul_of_nonneg_left h hpl'.le
        have h2 : (p - lam) * (-lam / (p - lam)) = -lam := by field_simp
        linarith
      have hks : ks = 0 := hks2 hHlt
      have hZ0 : Zf W p 0 = 1 := Zf_le_zero hW0 p le_rfl
      have hG0 : Gρ ρ p 0 = 1 := by unfold Gρ; rw [hm]; ring
      rw [hks, hZ0, hG0] at hHlt
      have : -lam / (p - lam) < 0 := div_neg_of_neg_of_pos (by linarith) hpl'
      linarith
    · rw [hc]; field_simp; ring
  have hcm : c * (ρ {w : ℝ | -w ≤ 0}).toReal =
      -(lam + (p - lam) * (κ * Gρ ρ p ks - (κ - 1) * Zf W p ks)) / (p * κ) := by
    rw [eq_div_iff (by positivity)]; linear_combination hkey
  -- the inner weight
  set g : ℝ → ℝ := fun a => κ * Real.exp (-(κ * a)) *
    (lam / p + (p - lam) / p * Gρ ρ p (ks - y + a)) with hg
  have hq : 0 ≤ (p - lam) / p := div_nonneg hpl'.le hp.le
  have hgnn : ∀ a, 0 ≤ g a := fun a => mul_nonneg (by positivity)
    (add_nonneg (by positivity) (mul_nonneg hq (Gρ_nonneg hρu hp _)))
  have hpt : EqOn (fun a => ENNReal.ofReal (κ * Real.exp (-(κ * a))) *
      ∫⁻ w, kCR lam p ks c (y - a - w) ∂ρ) (fun a => ENNReal.ofReal (g a)) (Ioo 0 y) := by
    intro a ha
    simp only
    rw [lint_kCR, rhoG_gt hρu hp, rho_eq_pos hρpos (by linarith [ha.2] : 0 < y - a), hρu,
      mul_zero, add_zero, show ks - (y - a) = ks - y + a by ring,
      ← ENNReal.ofReal_mul hlam.le, ← ENNReal.ofReal_mul hpl'.le,
      ← ENNReal.ofReal_add (by positivity)
        (mul_nonneg hpl'.le (div_nonneg (Gρ_nonneg hρu hp _) hp.le)),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hg]
    ring
  have hanti : Antitone (fun a => lam / p + (p - lam) / p * Gρ ρ p (ks - y + a)) := by
    intro a b hab
    have := Gρ_antitone (ρ := ρ) hp.le (show ks - y + a ≤ ks - y + b by linarith)
    simp only
    nlinarith
  have hII : IntervalIntegrable g volume 0 y :=
    hanti.intervalIntegrable.continuousOn_mul
      ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg))).continuousOn
  have hgi : IntegrableOn g (Ioo 0 y) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mp hII).mono_set Ioo_subset_Ioc_self
  -- W' = q W, G' = λ/p + q G
  have hW0' : ∀ x ≤ 0, (fun z => (p - lam) / p * W z) x = 0 := by
    intro x hx; simp only [hW0 x hx, mul_zero]
  have hWc' : ContinuousOn (fun z => (p - lam) / p * W z) (Ioi 0) := continuousOn_const.mul hWc
  have hWi' : ∀ b, IntegrableOn (fun z => (p - lam) / p * W z) (Ioc 0 b) :=
    fun b => (hWi b).const_mul _
  have hG' : ∀ u, u ≠ 0 → (fun u => lam / p + (p - lam) / p * Gρ ρ p u) u =
      Zf (fun z => (p - lam) / p * W z) p u - p / κ * (fun z => (p - lam) / p * W z) u := by
    intro u hu
    simp only
    rw [Zf_smul]
    rcases lt_or_gt_of_ne hu with hneg | hpos
    · rw [Gρ_neg hρpos hneg, Zf_le_zero hW0 p hneg.le, hW0 u hneg.le]
      field_simp; ring
    · rw [hGW u hpos]
      field_simp; ring
  have hgint := exp_G_identity hW0' hWc' hWi' p hκ0.ne' hG' (ks - y) y hy
  beta_reduce at hgint
  have hEF : Real.exp ((1 - κ) * y) = Real.exp y * Real.exp (-(κ * y)) := by
    rw [← Real.exp_add]; ring_nf
  set C := κ * Real.exp ((1 - κ) * y) / (κ - 1) with hC
  have hCnn : 0 ≤ C := div_nonneg (by positivity) (by linarith)
  have hB : 0 ≤ lam * (1 / p) + (p - lam) * (Gρ ρ p ks / p) + c * (ρ {w : ℝ | -w ≤ 0}).toReal :=
    add_nonneg (add_nonneg (by positivity)
      (mul_nonneg hpl'.le (div_nonneg (Gρ_nonneg hρu hp _) hp.le))) (mul_nonneg hcnn hm0nn)
  have hIg : 0 ≤ ∫ a in Ioo 0 y, g a := setIntegral_nonneg measurableSet_Ioo (fun a _ => hgnn a)
  have hR : Real.exp y * (∫ a in Ioo 0 y, g a) + C * (lam * (1 / p) + (p - lam) * (Gρ ρ p ks / p)
      + c * (ρ {w : ℝ | -w ≤ 0}).toReal) =
      (p - lam) * Real.exp y * Zf W p (ks - y) / p + lam * Real.exp y / p := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hy, hgint, Zf_smul,
      Zf_smul, show ks - y + y = ks by ring, hcm, hC, hEF]
    field_simp
    ring
  have hneg : ∫⁻ w, kCR lam p ks c (-w) ∂ρ = ∫⁻ w, kCR lam p ks c (0 - w) ∂ρ := by simp
  rw [lint_wG_split hκ (measurable_kCR lam p ks c) hy ρ, hneg, lint_kCR, rhoG_gt hρu hp,
    rho_eq_zero hρpos, hρu, sub_zero, setLIntegral_congr_fun measurableSet_Ioo hpt,
    ← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hgnn), ← hR,
    ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le hIg) (mul_nonneg hCnn hB),
    ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul hCnn,
    ENNReal.ofReal_add (add_nonneg (by positivity)
      (mul_nonneg hpl'.le (div_nonneg (Gρ_nonneg hρu hp _) hp.le))) (mul_nonneg hcnn hm0nn),
    ENNReal.ofReal_add (by positivity)
      (mul_nonneg hpl'.le (div_nonneg (Gρ_nonneg hρu hp _) hp.le)),
    ENNReal.ofReal_mul hlam.le, ENNReal.ofReal_mul hpl'.le, ENNReal.ofReal_mul hcnn]

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology Set

lemma nuq_univ {q : ℝ} (hq : 0 < q) : nuq q univ = ENNReal.ofReal (1 / q) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h := lintegral_exp_Ioi_c (by linarith : -q < 0) 0
  simp only [mul_zero, Real.exp_zero] at h
  simp_rw [← neg_mul]
  rw [h, neg_div_neg_eq]

lemma rhoP_univ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} (hX : Shared.IsSNLevy P X) {q : ℝ} (hq : 0 < q) :
    (((nuq q).prod P).map (Ynr X)) univ = ENNReal.ofReal (1 / q) := by
  haveI := nuq_finite hq
  rw [Measure.map_apply (measurable_Ynr hX) MeasurableSet.univ, preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := P), mul_one, nuq_univ hq]

lemma rhoP_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : Shared.IsSNLevy P X) (q : ℝ) :
    (((nuq q).prod P).map (Ynr X)) {w | 0 < w} = 0 := by
  rw [show {w : ℝ | 0 < w} = Ioi 0 from rfl, Measure.map_apply (measurable_Ynr hX) measurableSet_Ioi]
  have : Ynr X ⁻¹' Ioi (0:ℝ) = ∅ := by
    ext z
    simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false, not_lt]
    exact Ynr_nonpos hX z
  rw [this, measure_empty]

lemma Z_eq_Zf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (p : ℝ) :
    Shared.Z P X 0 p = Zf (Shared.W P X 0 p) p := rfl

lemma W_integrableOn_Ioc_of_scale {φ : ℝ → ℝ} {q : ℝ} {W : ℝ → ℝ}
    (h : Shared.IsScaleFun φ q W) (b : ℝ) : IntegrableOn W (Ioc 0 b) := by
  set θ := |Shared.Phi φ q| + 1 with hθ
  have hθgt : θ > Shared.Phi φ q := by have := le_abs_self (Shared.Phi φ q); linarith
  have hint := (h.2.2.2 θ hθgt).1
  have h1 : IntegrableOn (fun x => Real.exp (-θ * x) * W x) (Icc 0 b) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (f := fun x => Real.exp (-θ * x) * W x)).mpr
      (hint.mono_set Ioc_subset_Ioi_self)
  have h2 := h1.mul_continuousOn
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    (isCompact_Icc : IsCompact (Icc (0:ℝ) b)) (g' := fun x => Real.exp (θ * x))
  refine (h2.mono_set Ioc_subset_Icc_self).congr_fun ?_ measurableSet_Ioc
  intro x _
  simp only [Function.comp_apply]
  rw [mul_comm, ← mul_assoc, ← Real.exp_add]
  simp

/-- R3b real form: `Gρ = Z - (p/κ) W` on `(0,∞)`. -/
lemma Gρ_eq {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) {u : ℝ} (hu : 0 < u) :
    Gρ (((nuq q).prod P).map (Ynr X)) q u =
      Zf (Wq P X q) q u - q / kap P X q * Wq P X q u := by
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  have hκ := kap_pos 𝓕 P X hX hq
  have hrho := rho_le_enn 𝓕 P X hX hq hu
  have hGqt := Gq_ne_top 𝓕 P X hX hq
  set κ := kap P X q with hκdef
  have hW0 : ∀ x ≤ 0, Wq P X q x = 0 := fun x hx => by unfold Wq; rw [if_pos hx]
  have hset : (((nuq q).prod P).map (Ynr X)) {w | -w ≤ u} = ((nuq q).prod P) {z | -Ynr X z ≤ u} :=
    Measure.map_apply (measurable_Ynr hXL) (measurableSet_le measurable_neg measurable_const)
  have hpt : EqOn (fun x => ENNReal.ofReal (κ * Real.exp (κ * x)) * Gq P X q x)
      (fun x => ENNReal.ofReal (Wq P X q x)) (Ioc 0 u) := by
    intro x hx
    simp only
    unfold Wq
    rw [if_neg (not_le.mpr hx.1),
      ENNReal.ofReal_mul (show 0 ≤ kap P X q * Real.exp (kap P X q * x) by positivity),
      ENNReal.ofReal_toReal (hGqt x)]
  rw [setLIntegral_congr_fun measurableSet_Ioc hpt] at hrho
  have hfin : (ENNReal.ofReal (Real.exp (κ * u)) * Gq P X q u) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hGqt u)
  rw [hrho] at hfin
  have hA := (ENNReal.add_ne_top.mp hfin).1
  have hB := (ENNReal.add_ne_top.mp hfin).2
  have hreal := congrArg ENNReal.toReal hrho
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_add hA hB,
    ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (Wq_nonneg 𝓕 P X hX hq))
      (measurable_Wq P hXL q).aestronglyMeasurable] at hreal
  have hWu : Wq P X q u = κ * Real.exp (κ * u) * (Gq P X q u).toReal := by
    unfold Wq; rw [if_neg (not_le.mpr hu)]
  have hZ : Zf (Wq P X q) q u = 1 + q * ∫ x in Ioc 0 u, Wq P X q x := by
    rw [Zf_pos_eq hW0 q hu.le, intervalIntegral.integral_of_le hu.le]
  unfold Gρ
  rw [hset, hZ, hWu]
  have hc : q / κ * (κ * Real.exp (κ * u) * (Gq P X q u).toReal) =
      q * (Real.exp (κ * u) * (Gq P X q u).toReal) := by field_simp
  rw [hc]
  linear_combination q * hreal

/-- Right-continuity of `Gρ`. -/
lemma Gρ_rc {ρ : Measure ℝ} [IsFiniteMeasure ρ] (p u : ℝ) :
    ContinuousWithinAt (Gρ ρ p) (Ici u) u := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  have hT : Tendsto (fun r => ρ {w | -w ≤ r}) (𝓝[>] u) (𝓝 (ρ {w | -w ≤ u})) := by
    have h := tendsto_measure_biInter_gt (μ := ρ) (s := fun r => {w : ℝ | -w ≤ r}) (a := u)
      (fun r _ => (measurableSet_le measurable_neg measurable_const).nullMeasurableSet)
      (fun i j _ hij w hw => le_trans hw hij) ⟨u + 1, by linarith, measure_ne_top _ _⟩
    have hI : (⋂ r > u, {w : ℝ | -w ≤ r}) = {w | -w ≤ u} := by
      ext w
      simp only [mem_iInter, mem_ofPred_eq]
      constructor
      · intro hw
        by_contra hc
        push Not at hc
        obtain ⟨r, hr1, hr2⟩ := exists_between hc
        exact absurd (hw r hr1) (not_le.mpr hr2)
      · intro hw r hr; linarith
    beta_reduce at h
    rw [hI] at h
    exact h
  have hT2 := (ENNReal.tendsto_toReal (measure_ne_top ρ {w : ℝ | -w ≤ u})).comp hT
  exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul hT2) : Tendsto
    (fun r => 1 - p * (ρ {w | -w ≤ r}).toReal) _ _)

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Filter Topology Set

lemma Gq_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (q : ℝ)
    {x y : ℝ} (hxy : x ≤ y) : Gq P X q x ≤ Gq P X q y := by
  unfold Gq
  refine lintegral_mono fun z => ?_
  by_cases h : -Ynr X z ≤ x
  · rw [if_pos h, if_pos (le_trans h hxy)]
  · rw [if_neg h]; exact bot_le

lemma Gq_pos_somewhere {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) : ∃ u0 : ℝ, 0 < u0 ∧ 0 < (Gq P X q u0).toReal := by
  have hXL := hX.isSNLevy
  haveI := nuq_finite hq
  have hY := measurable_Ynr hXL
  by_contra hcon
  push Not at hcon
  have hz : ∀ n : ℕ, Gq P X q ((n : ℝ) + 1) = 0 := by
    intro n
    have h1 := hcon ((n : ℝ) + 1) (by positivity)
    have h2 := (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm h1 ENNReal.toReal_nonneg)
    exact h2.resolve_right (Gq_ne_top 𝓕 P X hX hq _)
  have hae : ∀ n : ℕ, ∀ᵐ z ∂((nuq q).prod P),
      (if -Ynr X z ≤ (n : ℝ) + 1 then ENNReal.ofReal (Real.exp (kap P X q * Ynr X z)) else 0) = 0 := by
    intro n
    have hm : Measurable (fun z => if -Ynr X z ≤ (n : ℝ) + 1 then
        ENNReal.ofReal (Real.exp (kap P X q * Ynr X z)) else (0 : ℝ≥0∞)) :=
      Measurable.ite (measurableSet_le hY.neg measurable_const)
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hY)))
        measurable_const
    have := hz n
    unfold Gq at this
    exact (lintegral_eq_zero_iff hm).mp this
  rw [← ae_all_iff] at hae
  have hfalse : ∀ᵐ z ∂((nuq q).prod P), False := by
    filter_upwards [hae] with z hz'
    obtain ⟨n, hn⟩ := exists_nat_ge (-Ynr X z)
    have := hz' n
    rw [if_pos (by linarith)] at this
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' this
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at hfalse
  have h1 : ((nuq q).prod P) univ = ENNReal.ofReal (1 / q) := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := P), mul_one, nuq_univ hq]
  rw [hfalse] at h1
  simp only [Measure.coe_zero, Pi.zero_apply] at h1
  have h2 := ENNReal.ofReal_eq_zero.mp h1.symm
  have h3 : 0 < 1 / q := by positivity
  linarith

lemma exists_Wq_ge {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {q : ℝ} (hq : 0 < q) (M : ℝ) : ∃ u, 0 < u ∧ M ≤ Wq P X q u := by
  obtain ⟨u0, hu0, hg0⟩ := Gq_pos_somewhere 𝓕 P X hX hq
  have hκ := kap_pos 𝓕 P X hX hq
  set κ := kap P X q with hκdef
  set g0 := (Gq P X q u0).toReal with hg0def
  set u := max u0 (M / (κ * κ * g0)) with hu
  have hupos : 0 < u := lt_of_lt_of_le hu0 (le_max_left _ _)
  refine ⟨u, hupos, ?_⟩
  have hGu : g0 ≤ (Gq P X q u).toReal :=
    ENNReal.toReal_mono (Gq_ne_top 𝓕 P X hX hq u) (Gq_mono P X q (le_max_left _ _))
  have hWu : Wq P X q u = κ * Real.exp (κ * u) * (Gq P X q u).toReal := by
    unfold Wq; rw [if_neg (not_le.mpr hupos)]
  have hexp : κ * u + 1 ≤ Real.exp (κ * u) := Real.add_one_le_exp _
  have hpos : 0 < κ * κ * g0 := by positivity
  calc M = κ * κ * g0 * (M / (κ * κ * g0)) := by field_simp
    _ ≤ κ * κ * g0 * u := mul_le_mul_of_nonneg_left (le_max_right _ _) hpos.le
    _ ≤ κ * Real.exp (κ * u) * g0 := by nlinarith
    _ ≤ κ * Real.exp (κ * u) * (Gq P X q u).toReal :=
        mul_le_mul_of_nonneg_left hGu (by positivity)
    _ = Wq P X q u := hWu.symm

set_option maxHeartbeats 1000000 in
/-- The κ_* facts for the concrete scale functions. -/
lemma ks_facts {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ) (hX : Shared.IsSNLevyWrt 𝓕 P X)
    {p lam : ℝ} (hlam : 0 < lam) (hpl : lam < p) (hκ1 : 1 < kap P X p) :
    kap P X p * Gρ (((nuq p).prod P).map (Ynr X)) p (Canadized.kappaLow P X p lam) -
        (kap P X p - 1) * Zf (Shared.W P X 0 p) p (Canadized.kappaLow P X p lam) ≤
        -lam / (p - lam) ∧
      (kap P X p * Gρ (((nuq p).prod P).map (Ynr X)) p (Canadized.kappaLow P X p lam) -
        (kap P X p - 1) * Zf (Shared.W P X 0 p) p (Canadized.kappaLow P X p lam) <
        -lam / (p - lam) → Canadized.kappaLow P X p lam = 0) := by
  have hp : 0 < p := by linarith
  have hpl' : 0 < p - lam := by linarith
  have hXL := hX.isSNLevy
  haveI := nuq_finite hp
  have hWeq := W_eq_Wq 𝓕 P X hX hp
  have hsc := isScaleFun_Wq' 𝓕 P X hX hp
  have hW0 : ∀ x ≤ 0, Wq P X p x = 0 := hsc.2.1
  have hWi := W_integrableOn_Ioc_of_scale hsc
  have hκ0 : 0 < kap P X p := by linarith
  rw [hWeq]
  set κ := kap P X p with hκdef
  set ρ := ((nuq p).prod P).map (Ynr X) with hρ
  have hT : -lam / (p - lam) < 0 := div_neg_of_neg_of_pos (by linarith) hpl'
  have hks : Canadized.kappaLow P X p lam =
      sInf {x | 0 ≤ x ∧ (fun x => Zf (Wq P X p) p x - p * Wq P X p x) x ≤ -lam / (p - lam)} := by
    simp only [Canadized.kappaLow, Z_eq_Zf, hWeq]
  have hGW : ∀ u, 0 < u → Gρ ρ p u = Zf (Wq P X p) p u - p / κ * Wq P X p u :=
    fun u hu => Gρ_eq 𝓕 P X hX hp hu
  have hle1 : ∀ u, Gρ ρ p u ≤ 1 := by
    intro u; unfold Gρ
    have := mul_nonneg hp.le (ENNReal.toReal_nonneg (a := ρ {w | -w ≤ u}))
    linarith
  have key := kappa_facts (H := fun x => Zf (Wq P X p) p x - p * Wq P X p x)
    (Hr := fun u => κ * Gρ ρ p u - (κ - 1) * Zf (Wq P X p) p u) (T := -lam / (p - lam)) hks
    (by rw [Zf_le_zero hW0 p le_rfl, hW0 0 le_rfl]; linarith)
    (by
      intro u hu; rw [hGW u hu]; field_simp; ring)
    (fun u _ => (continuousWithinAt_const.mul (Gρ_rc p u)).sub
      (continuousWithinAt_const.mul (continuous_Zf hW0 hWi p).continuousWithinAt))
    ((continuous_Zf hW0 hWi p).continuousOn.sub (continuousOn_const.mul hsc.2.2.1))
    (by
      obtain ⟨u, hu, hWu⟩ := exists_Wq_ge 𝓕 P X hX hp
        ((1 - -lam / (p - lam)) * κ / ((κ - 1) * p))
      refine ⟨u, hu.le, ?_⟩
      have hc0 : 0 ≤ p - p / κ := by
        have : p / κ ≤ p := div_le_self hp.le hκ1.le
        linarith
      have hWu' : 1 - -lam / (p - lam) ≤ (p - p / κ) * Wq P X p u := by
        have h1 := mul_le_mul_of_nonneg_left hWu hc0
        have h2 : (p - p / κ) * ((1 - -lam / (p - lam)) * κ / ((κ - 1) * p)) =
            1 - -lam / (p - lam) := by
          have : κ - 1 ≠ 0 := by linarith
          field_simp
        linarith
      have hH : Zf (Wq P X p) p u - p * Wq P X p u = Gρ ρ p u - (p - p / κ) * Wq P X p u := by
        rw [hGW u hu]; ring
      rw [hH]
      linarith [hle1 u])
  exact ⟨key.2.1, key.2.2⟩

/-- The constant `c` of the resolvent weight. -/
noncomputable def cCR {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (p lam : ℝ) : ℝ :=
  -(lam + (p - lam) * (kap P X p * Gρ (((nuq p).prod P).map (Ynr X)) p
      (Canadized.kappaLow P X p lam) -
    (kap P X p - 1) * Zf (Shared.W P X 0 p) p (Canadized.kappaLow P X p lam))) /
    (p * kap P X p * ((((nuq p).prod P).map (Ynr X)) {w | -w ≤ 0}).toReal)

set_option maxHeartbeats 1000000 in
/-- R3: `h = R_β f` on `[0, ∞)` under `Q`. -/
theorem resU_hCR {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) {r : ℝ} (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) {α lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    {y : ℝ} (hy : 0 ≤ y) :
    resU Q X (α + lam) (fun z => ENNReal.ofReal (Real.exp z) *
      kCR lam (α + lam + r) (Canadized.kappaLow P X (α + lam + r) lam)
        (cCR P X (α + lam + r) lam) z) y =
      ENNReal.ofReal (Canadized.hCR P X (α + lam + r) lam y) := by
  have hβ : 0 < α + lam := by linarith
  have hp : 0 < α + lam + r := by linarith
  have hXL := hX.isSNLevy
  have hκ1 : 1 < kap P X (α + lam + r) := by
    have h1 := kap_esscher hX hQ hψ hr hβ
    have h2 := kap_pos 𝓕 Q X (esscher_isSNLevyWrt hX hQ) hβ
    linarith
  haveI := nuq_finite hp
  rw [resU_esscher 𝓕 P Q X hX hQ (α + lam) hp (measurable_kCR _ _ _ _) y]
  have hWeq := W_eq_Wq 𝓕 P X hX hp
  have hsc := isScaleFun_Wq' 𝓕 P X hX hp
  obtain ⟨h1, h2⟩ := ks_facts 𝓕 P X hX hlam (by linarith : lam < α + lam + r) hκ1
  have hW0 : ∀ x ≤ 0, Shared.W P X 0 (α + lam + r) x = 0 := by rw [hWeq]; exact hsc.2.1
  have hWc : ContinuousOn (Shared.W P X 0 (α + lam + r)) (Ioi 0) := by rw [hWeq]; exact hsc.2.2.1
  have hWi : ∀ b, IntegrableOn (Shared.W P X 0 (α + lam + r)) (Ioc 0 b) := by
    rw [hWeq]; exact W_integrableOn_Ioc_of_scale hsc
  have hGW : ∀ u, 0 < u → Gρ (((nuq (α + lam + r)).prod P).map (Ynr X)) (α + lam + r) u =
      Zf (Shared.W P X 0 (α + lam + r)) (α + lam + r) u -
        (α + lam + r) / kap P X (α + lam + r) * Shared.W P X 0 (α + lam + r) u := by
    rw [hWeq]; exact fun u hu => Gρ_eq 𝓕 P X hX hp hu
  rw [resolvent_value (c := cCR P X (α + lam + r) lam) hlam (by linarith) hκ1 (rhoP_univ hXL hp) (rhoP_pos hXL _) hW0 hWc hWi hGW
    h1 h2 rfl hy]
  unfold Canadized.hCR
  rw [Z_eq_Zf]

end Avram2004.Markov92562e40

namespace Avram2004.Markov92562e40

open Avram2004.Canadized in
set_option maxHeartbeats 1000000 in
theorem core_U_super {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (s x : ℝ) (hsx : x ≤ s) :
    Supermartingale (fun (t : ℝ≥0) ω => U P X α lam p s x t ω) 𝓕 Q := by
  subst hp
  have hlam : 0 < lam := hη.1
  have hXL := hX.isSNLevy
  have hXQ := esscher_isSNLevyWrt hX hQ
  have hp : 0 < α + lam + r := by linarith
  have hfm : Measurable (fun z => ENNReal.ofReal (Real.exp z) *
      kCR lam (α + lam + r) (kappaLow P X (α + lam + r) lam) (cCR P X (α + lam + r) lam) z) :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul (measurable_kCR _ _ _ _)
  have hWeq := W_eq_Wq 𝓕 P X hX hp
  have hsc := isScaleFun_Wq' 𝓕 P X hX hp
  have hZ1 : ∀ z, 1 ≤ Shared.Z P X 0 (α + lam + r) z := by
    intro z
    rw [Z_eq_Zf]
    unfold Zf
    have : 0 ≤ ∫ u in Set.Iic z, Shared.W P X 0 (α + lam + r) u :=
      setIntegral_nonneg measurableSet_Iic (fun u _ => by rw [hWeq]; exact hsc.1 u)
    have := mul_nonneg hp.le this
    linarith
  have key := super_of_resolvent 𝓕 Q X hXQ (α + lam) lam (s - x) hlam.le (sub_nonneg.mpr hsx)
    (hCR P X (α + lam + r) lam) hfm
    (by
      intro z _
      rw [mul_comm lam, ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      unfold kCR
      exact le_add_right (le_add_right le_rfl))
    (by
      intro z hz
      refine ⟨?_, (resU_hCR 𝓕 P Q X hX hr hψ hQ hα hlam hz).symm⟩
      unfold hCR
      have h1 := hZ1 (kappaLow P X (α + lam + r) lam - z)
      have h2 : 0 < α + r := by linarith
      have : 0 ≤ (α + lam + r - lam) * Real.exp z * Shared.Z P X 0 (α + lam + r)
          (kappaLow P X (α + lam + r) lam - z) / (α + lam + r) := by
        apply div_nonneg _ hp.le
        apply mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (by linarith)
      have : 0 ≤ lam * Real.exp z / (α + lam + r) := by positivity
      linarith)
  have hU : (fun (t : ℝ≥0) ω => U P X α lam (α + lam + r) s x t ω) =
      (fun (t : ℝ≥0) ω => Real.exp (-(α + lam) * (t : ℝ)) *
        hCR P X (α + lam + r) lam (Shared.refl (s - x) 0 X t ω)
        + lam * ∫ u in (0 : ℝ)..(t : ℝ),
          Real.exp (-(α + lam) * u + Shared.refl (s - x) 0 X u.toNNReal ω)) := by
    funext t ω
    unfold U
    simp_rw [refl_sx hXL s x]
  rw [hU]
  exact key

end Avram2004.Markov92562e40

open MeasureTheory ProbabilityTheory Filter Topology NNReal ENNReal Avram2004 Avram2004.Canadized in
theorem solution {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m)
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (X : ℝ≥0 → Ω → ℝ)
    (hX : Shared.IsSNLevyWrt 𝓕 P X) (hS : Shared.Standing P X) (r : ℝ) (hr : 0 ≤ r) (hψ : Shared.psi P X 1 = r)
    (hQ : Shared.IsEsscher 𝓕 P Q X r) (α : ℝ) (hα : 0 < α) (η : Ω → ℝ) (lam : ℝ)
    (hη : IsExpClock 𝓕 Q η lam) (p : ℝ) (hp : p = α + lam + r)
    (s x : ℝ) (hsx : x ≤ s) :
    Supermartingale (fun (t : ℝ≥0) ω => U P X α lam p s x t ω) 𝓕 Q := by
  exact Avram2004.Markov92562e40.core_U_super 𝓕 P Q X hX hS r hr hψ hQ α hα η lam hη p hp s x hsx
